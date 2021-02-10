// Copyright (c) 2020-present, author: Zhengyang Liu (liuz@cs.utah.edu).
// Distributed under the MIT license that can be found in the LICENSE file.
#include "EnumerativeSynthesis.h"
#include "ConstantSynthesis.h"
#include "IR.h"
#include "LLVMGen.h"

#include "smt/smt.h"
#include "tools/transform.h"
#include "util/symexec.h"
#include "util/config.h"
#include "util/version.h"
#include "llvm_util/llvm2alive.h"

#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/LoopAnalysisManager.h"
#include "llvm/Analysis/CGSCCPassManager.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Scalar/DCE.h"

#include <iostream>
#include <queue>
#include <vector>
#include <set>
#include <map>

using namespace tools;
using namespace util;
using namespace std;
using namespace IR;

namespace vectorsynth {

static void findInputs(llvm::Value *Root, set<unique_ptr<Var>> &Cands,
                       unsigned Max) {
  // breadth-first search
  unordered_set<llvm::Value *> Visited;
  queue<llvm::Value *> Q;
  Q.push(Root);

  while (!Q.empty()) {
    llvm::Value *V = Q.front();
    Q.pop();
    if (Visited.insert(V).second) {
      if (auto I = llvm::dyn_cast<llvm::Instruction>(V)) {
        for (auto &Op : I->operands()) {
          Q.push(Op);
        }
      }

      if (llvm::isa<llvm::Constant>(V))
        continue;
      if (V == Root)
        continue;
      Cands.insert(make_unique<Var>(V));
      if (Cands.size() >= Max)
        return;
    }
  }
}

static bool getSketches(set<unique_ptr<Var>> &Inputs, llvm::Value *V,
                        vector<pair<unique_ptr<Inst>,
                        set<unique_ptr<ReservedConst>>>> &R) {
  auto &Ctx = V->getContext();
  R.clear();
  vector<Comp *> Comps;
  for (auto &I : Inputs) {
    Comps.emplace_back(I.get());
  }

  auto RC1 = make_unique<ReservedConst>(nullptr);
  Comps.emplace_back(RC1.get());
  llvm::Type *ty = V->getType();
  for (unsigned K = BinOp::Op::band; K <= BinOp::Op::mul; K++) {
    for (auto Op0 = Comps.begin(); Op0 != Comps.end(); ++Op0) {
      auto Op1 = BinOp::isCommutative((BinOp::Op)K) ? Op0 : Comps.begin();
      for (; Op1 != Comps.end(); ++Op1) {
        Inst *I = nullptr, *J = nullptr;
        set<unique_ptr<ReservedConst>> RCs;

        // (op rc, var)
        if (dynamic_cast<ReservedConst *>(*Op0)) {
          if (auto R = dynamic_cast<Var *>(*Op1)) {
            // ignore icmp temporarily
            if (R->V()->getType() != ty)
              continue;
            auto T = make_unique<ReservedConst>(R->V()->getType());
            I = T.get();
            RCs.insert(move(T));
            J = R;
          } else continue;
        }
        // (op var, rc)
        else if (dynamic_cast<ReservedConst *>(*Op1)) {
          if (auto L = dynamic_cast<Var *>(*Op0)) {
            if (L->V()->getType() != ty)
              continue;
            I = L;
            auto T = make_unique<ReservedConst>(L->V()->getType());
            J = T.get();
            RCs.insert(move(T));
          } else continue;
        }
        // (op var, var)
        else {
          if (auto L = dynamic_cast<Var *>(*Op0)) {
            if (auto R = dynamic_cast<Var *>(*Op1)) {
              if (L->V()->getType() != R->V()->getType())
                continue;
              if (L->V()->getType() != ty)
                continue;
            };
          };
          I = *Op0;
          J = *Op1;
        }
        BinOp::Op op = static_cast<BinOp::Op>(K);
        auto BO = make_unique<BinOp>(op, *I, *J);
        R.push_back(make_pair(move(BO), move(RCs)));
      }
    }
    
    // BinaryIntrinsics
    for (unsigned K = SIMDBinOp::Op::x86_ssse3_pshuf_b_128;
         K <= SIMDBinOp::Op::x86_avx2_pshuf_b; ++K) {
      // typecheck for return val
      if (!ty->isVectorTy())
        continue;
      llvm::VectorType *vty = llvm::cast<llvm::FixedVectorType>(ty);
      // FIX: Better typecheck
      if (!vty->getElementType()->isIntegerTy())
        continue;

      SIMDBinOp::Op op = static_cast<SIMDBinOp::Op>(K);
      if (SIMDBinOp::binop_ret_v[op].first != vty->getElementCount().getKnownMinValue())
        continue;
      if (SIMDBinOp::binop_ret_v[op].second != vty->getScalarSizeInBits())
        continue;

      for (auto Op0 = Comps.begin(); Op0 != Comps.end(); ++Op0) {
        for (auto Op1 = Comps.begin(); Op1 != Comps.end(); ++Op1) {
          Inst *I = nullptr, *J = nullptr;
          set<unique_ptr<ReservedConst>> RCs;

          // syntactic prunning
          if (auto L = dynamic_cast<Var *> (*Op0)) {
            // typecheck for op0
            if (!L->V()->getType()->isVectorTy())
              continue;
            llvm::VectorType *aty = llvm::cast<llvm::FixedVectorType>(L->V()->getType());
            // FIX: Better typecheck
            if (aty != vty) continue;
            if (SIMDBinOp::binop_op0_v[op].first  != aty->getElementCount().getKnownMinValue())
              continue;
            if (SIMDBinOp::binop_op0_v[op].second != aty->getScalarSizeInBits()) {
              continue;
            }
          }
          if (auto R = dynamic_cast<Var *>(*Op1)) {
            // typecheck for op1
            if (!R->V()->getType()->isVectorTy())
              continue;
            llvm::VectorType *bty = llvm::cast<llvm::FixedVectorType>(R->V()->getType());
            // FIX: Better typecheck
            if (bty != vty) continue;
            if (SIMDBinOp::binop_op1_v[op].first  != bty->getElementCount().getKnownMinValue())
              continue;
            if (SIMDBinOp::binop_op1_v[op].second != bty->getScalarSizeInBits())
              continue;
          }

          // (op rc, var)
          if (dynamic_cast<ReservedConst *>(*Op0)) {
            if (auto R = dynamic_cast<Var *>(*Op1)) {
              unsigned lanes = SIMDBinOp::binop_op0_v[op].first;
              unsigned bits = SIMDBinOp::binop_op0_v[op].second;
              auto aty = llvm::FixedVectorType::get(llvm::IntegerType::get(Ctx, bits), lanes);
              auto T = make_unique<ReservedConst>(aty);
              I = T.get();
              RCs.insert(move(T));
              J = R;
            } else continue;
          }
          // (op var, rc)
          else if (dynamic_cast<ReservedConst *>(*Op1)) {
            if (auto L = dynamic_cast<Var *>(*Op0)) {
              unsigned lanes = SIMDBinOp::binop_op1_v[op].first;
              unsigned bits = SIMDBinOp::binop_op1_v[op].second;
              auto bty = llvm::FixedVectorType::get(llvm::IntegerType::get(Ctx, bits), lanes);
              auto T = make_unique<ReservedConst>(bty);
              J = T.get();
              RCs.insert(move(T));
              I = L;
            } else continue;
          }
          // (op var, var)
          else {
            I = *Op0;
            J = *Op1;
          }

          auto BO = make_unique<SIMDBinOpIntr>(op, *I, *J);
          R.push_back(make_pair(move(BO), move(RCs)));
        }
      }
    }
  }

  // ShuffleVector
#if (false)
  for (auto Op0 = Comps.begin(); Op0 != Comps.end(); ++Op0) {
    for (auto Op1 = Comps.begin(); Op1 != Comps.end(); ++Op1) {
      if (!V->getType()->isVectorTy())
        continue;
      auto vty = llvm::cast<llvm::VectorType>(V->getType());

      Inst *I = nullptr, *J = nullptr;
      set<unique_ptr<ReservedConst>> RCs;
      // (shufflevecttor rc, var, mask)
      if (dynamic_cast<ReservedConst *>(*Op0)) {
        if (dynamic_cast<Var *>(*Op1))
          continue;
      }
        // (shufflevector var, rc, mask)
      else if (dynamic_cast<ReservedConst *>(*Op1)) {
        if (auto L = dynamic_cast<Var *>(*Op0)) {
          if (!L->V()->getType()->isVectorTy())
            continue;
          auto lvty = llvm::cast<llvm::VectorType>(L->V()->getType());
          if (lvty->getElementType() != vty->getElementType())
            continue;
          I = L;
          auto T = make_unique<ReservedConst>(L->V()->getType());
          J = T.get();
          RCs.insert(move(T));
        } else continue;
      }
      // (shufflevector, var, var, mask)
      else {
        if (auto L = dynamic_cast<Var *>(*Op0)) {
          if (auto R = dynamic_cast<Var *>(*Op1)) {
            if (L->V()->getType() != R->V()->getType())
              continue;
            if (!L->V()->getType()->isVectorTy())
              continue;
            auto lvty = llvm::cast<llvm::VectorType>(L->V()->getType());
            if (lvty->getElementType() != vty->getElementType())
              continue;
          };
        };
        I = *Op0;
        J = *Op1;
      }
      auto mty = llvm::VectorType::get(llvm::Type::getInt32Ty(V->getContext()), vty->getElementCount());
      auto mask = make_unique<ReservedConst>(mty);
      auto BO = make_unique<ShuffleVector>(*I, *J, *mask.get());
      RCs.insert(move(mask));
      R.push_back(make_pair(move(BO), move(RCs)));
    }
  }
#endif

  for (auto &I : Inputs) {
    if (I->V()->getType() != V->getType())
      continue;
    set<unique_ptr<ReservedConst>> RCs;
    // TODO : reduce copy
    auto V = make_unique<Var>(I->V());
    R.push_back(make_pair(move(V), move(RCs)));
  }

  return true;
}

static optional<smt::smt_initializer> smt_init;
static bool compareFunctions(IR::Function &Func1, IR::Function &Func2,
                             unsigned &goodCount,
                             unsigned &badCount, unsigned &errorCount) {
  TransformPrintOpts print_opts;
  smt_init->reset();
  Transform t;
  t.src = move(Func1);
  t.tgt = move(Func2);
  t.preprocess();
  TransformVerify verifier(t, false);
  t.print(cout, print_opts);

  {
    auto types = verifier.getTypings();
    if (!types) {
      cerr << "Transformation doesn't verify!\n"
              "ERROR: program doesn't type check!\n\n";
      ++errorCount;
      return true;
    }
    assert(types.hasSingleTyping());
  }

  Errors errs = verifier.verify();
  bool result(errs);
  if (result) {
    if (errs.isUnsound()) {
      cerr << "Transformation doesn't verify!\n" << errs << endl;
      ++badCount;
    } else {
      cerr << errs << endl;
      ++errorCount;
    }
  } else {
    cerr << "Transformation seems to be correct!\n\n";
    ++goodCount;
  }

  return result;
}

static bool
constantSynthesis(IR::Function &Func1, IR::Function &Func2,
                  unsigned &goodCount, unsigned &badCount, unsigned &errorCount,
                  unordered_map<const Value *, llvm::Argument *> &inputMap,
                  unordered_map<llvm::Argument *, llvm::Constant *> &constMap) {
  TransformPrintOpts print_opts;
  smt_init->reset();
  Transform t;
  t.src = move(Func1);
  t.tgt = move(Func2);
  vectorsynth::ConstantSynthesis verifier(t);
  t.print(cout, print_opts);
  // assume type verifies
  std::unordered_map<const IR::Value *, smt::expr> result;
  Errors errs = verifier.synthesize(result);

  bool ret(errs);
  if (result.empty())
    return ret;

  for (auto p : inputMap) {
    auto &ty = p.first->getType();
    auto lty = p.second->getType();

    if (ty.isIntType()) {
      // TODO, fix, do not use numeral_string()
      constMap[p.second] = llvm::ConstantInt::get(llvm::cast<llvm::IntegerType>(lty), result[p.first].numeral_string(), 10);
    } else if (ty.isFloatType()) {
      //TODO
      UNREACHABLE();
    } else if (ty.isVectorType()) {
      auto trunk = result[p.first];
      llvm::FixedVectorType *vty = llvm::cast<llvm::FixedVectorType>(lty);
      llvm::IntegerType *ety = llvm::cast<llvm::IntegerType>(vty->getElementType());
      vector<llvm::Constant *> v;
      for (int i = vty->getElementCount().getKnownMinValue() - 1 ; i >= 0 ; i --) {
        unsigned bits = ety->getBitWidth();
        auto elem = trunk.extract((i + 1) * bits - 1, i * bits);
        // TODO: support undef
        if (!elem.isConst())
          return ret;
        v.push_back(llvm::ConstantInt::get(ety, elem.numeral_string(), 10));
      }
      constMap[p.second] = llvm::ConstantVector::get(v);
    }
  }

  goodCount++;

  return ret;
}

  //void optimizeFunction(llvm::Function &F) {
static void DCE(llvm::Function &F) {
  llvm::LoopAnalysisManager LAM;
  llvm::FunctionAnalysisManager FAM;
  llvm::CGSCCAnalysisManager CGAM;
  llvm::ModuleAnalysisManager MAM;

  llvm::PassBuilder PB;
  PB.registerModuleAnalyses(MAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerFunctionAnalyses(FAM);
  PB.registerLoopAnalyses(LAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

  llvm::FunctionPassManager FPM;
  FPM.addPass(llvm::DCEPass());
  FPM.run(F, FAM);
}

static void removeUnusedDecls(unordered_set<llvm::Function *> IntrinsicDecls) {
  for (auto Intr : IntrinsicDecls) {
    if (Intr->isDeclaration() && Intr->use_empty()) {
      Intr->eraseFromParent();
    }
  }
}

bool synthesize(llvm::Function &F1, llvm::TargetLibraryInfo *TLI) {
  config::disable_undef_input = true;
  config::disable_poison_input = true;
  config::src_unroll_cnt = 2;
  config::tgt_unroll_cnt = 2;

  bool changed = false;

  smt_init.emplace();
  Inst *R = nullptr;
  bool result = false;
  std::unordered_set<llvm::Function *> IntrinsicDecls;

  for (auto &BB : F1) {
    for (llvm::BasicBlock::reverse_iterator I = BB.rbegin(), E = BB.rend(); I != E; I++) {
      unordered_map<llvm::Argument *, llvm::Constant *> constMap;
      set<unique_ptr<Var>> Inputs;
      findInputs(&*I, Inputs, 20);

      vector<pair<unique_ptr<Inst>,set<unique_ptr<ReservedConst>>>> Sketches;
      getSketches(Inputs, &*I, Sketches);


      if (Sketches.empty()) continue;

      cout<<"---------Sketches------------"<<endl;
      for (auto &Sketch : Sketches) {
        cout<<*Sketch.first<<endl;
      }
      cout<<"-----------------------------"<<endl;

      struct Comparator {
        bool operator()(tuple<llvm::Function *, Inst *, bool>& p1, tuple<llvm::Function *, Inst *, bool> &p2) {
          return get<0>(p1)->getInstructionCount() > get<0>(p2)->getInstructionCount();
        }
      };
      unordered_map<string, llvm::Argument *> constants;
      unsigned CI = 0;
      priority_queue<tuple<llvm::Function *, Inst *, bool>, vector<tuple<llvm::Function *, Inst *, bool>>, Comparator> Fns;

      // sketches -> llvm functions
      for (auto &Sketch : Sketches) {
        auto &G = Sketch.first;
        llvm::ValueToValueMapTy VMap;
        auto FT = F1.getFunctionType();

        llvm::SmallVector<llvm::Type *, 8> Args;
        for (auto I: FT->params()) {
          Args.push_back(I);
        }
        
        for (auto &C : Sketch.second) {
          Args.push_back(C->T());
        }

        auto nFT = llvm::FunctionType::get(FT->getReturnType(), Args, FT->isVarArg());

        auto GF = llvm::Function::Create(nFT, F1.getLinkage(), F1.getName(), F1.getParent());
        llvm::SmallVector<llvm::ReturnInst *, 8> returns;

        llvm::Function::arg_iterator GI = GF->arg_begin();

        for (auto I = F1.arg_begin(), E = F1.arg_end(); I != E; ++I, ++GI) {
          VMap[I] = GI;
          GI->setName(I->getName());
        }

        for (auto &C : Sketch.second) {
          string arg_name = "_reservedc_" + std::to_string(CI);
          GI->setName(arg_name);
          constants[arg_name] = GI;
          C->setA(GI);
          ++CI;
          ++GI;
        }

        llvm::CloneFunctionInto(GF, &F1, VMap, false, returns);

        llvm::Instruction *PrevI = llvm::cast<llvm::Instruction>(VMap[&*I]);
        llvm::Value *V = LLVMGen(PrevI, IntrinsicDecls).codeGen(G.get(), VMap, nullptr);
        PrevI->replaceAllUsesWith(V);

        DCE(*GF);
        if (GF->getInstructionCount() >= F1.getInstructionCount()) {
          GF->eraseFromParent();
          continue;
        }

        Fns.push(make_tuple(GF, G.get(), !Sketch.second.empty()));
      }

      // llvm functions -> alive2 functions, followed by verification/synthesis
      while (!Fns.empty()) {
        auto [GF, G, HaveC] = Fns.top();
        Fns.pop();
        auto Func1 = llvm_util::llvm2alive(F1, *TLI);
        auto Func2 = llvm_util::llvm2alive(*GF, *TLI);
        unsigned goodCount = 0, badCount = 0, errorCount = 0;
        if (!HaveC) {
          result |= compareFunctions(*Func1, *Func2,
                                     goodCount, badCount, errorCount);
        } else {
          unordered_map<const Value *, llvm::Argument *> inputMap;
          for (auto &I : Func2->getInputs()) {
            string input_name = I.getName();
            // remove "%"
            input_name.erase(0, 1);
            if (constants.count(input_name)) {
              inputMap[&I] = constants[input_name];
            }
          }
          constMap.clear();
          result |= constantSynthesis(*Func1, *Func2,
                                      goodCount, badCount, errorCount,
                                      inputMap, constMap);
        }
        GF->eraseFromParent();
        if (goodCount) {
          R = G;
          break;
        }
      }

      // clean up
      while (!Fns.empty()) {
        auto [GF, G, HaveC] = Fns.top();
        Fns.pop();
        (void) G; (void) HaveC;
        GF->eraseFromParent();
      }
      if (R) {
        llvm::ValueToValueMapTy VMap;
        llvm::Value *V = LLVMGen(&*I, IntrinsicDecls).codeGen(R, VMap, &constMap);
        I->replaceAllUsesWith(V);
        DCE(F1);
        changed = true;
        break;
      }
    }
  }
  removeUnusedDecls(IntrinsicDecls);
  return changed;
}

};
