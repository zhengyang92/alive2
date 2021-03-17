
// Copyright (c) 2020-present, author: Zhengyang Liu (liuz@cs.utah.edu).
// Distributed under the MIT license that can be found in the LICENSE file.
#include "LLVMGen.h"

#include "IR.h"
#include "SIMDBinOp.h"

#include "llvm/IR/IntrinsicsX86.h"
#include "llvm/IR/IRBuilder.h"

using namespace std;
using namespace llvm;
using namespace vectorsynth;

namespace vectorsynth {

Value* LLVMGen::codeGen(Inst *I, ValueToValueMapTy &VMap,
                        unordered_map<Argument *, Constant*> *constMap) {
  if (auto V = dynamic_cast<Var *>(I)) {
    if (VMap.empty()) {
      return V->V();
    } else {
      return VMap[V->V()];
    }
  } else if (auto B = dynamic_cast<BinOp *>(I)) {
    auto op0 = codeGen(B->L(), VMap, constMap);
    auto op1 = codeGen(B->R(), VMap, constMap);
    llvm::Value *r = nullptr;
    switch (B->K()) {
    case BinOp::band:
      r = b.CreateAnd(op0, op1, "and");
      break;
    case BinOp::bor:
      r = b.CreateOr(op0, op1, "or");
      break;
    case BinOp::bxor:
      r = b.CreateXor(op0, op1, "xor");
      break;
    case BinOp::add:
      r = b.CreateAdd(op0, op1, "add");
      break;
    case BinOp::sub:
      r = b.CreateSub(op0, op1, "sub");
      break;
    case BinOp::mul:
      r = b.CreateMul(op0, op1, "mul");
      break;
    case BinOp::sdiv:
      r = b.CreateSDiv(op0, op1, "sdiv");
      break;
    case BinOp::udiv:
      r = b.CreateUDiv(op0, op1, "udiv");
      break;
    case BinOp::lshr:
      r = b.CreateLShr(op0, op1, "lshr");
      break;
    case BinOp::ashr:
      r = b.CreateAShr(op0, op1, "ashr");
      break;
    case BinOp::shl:
      r = b.CreateShl(op0, op1, "shl");
      break;
    default:
      UNREACHABLE();
    }
    return r;
  } else if (auto B = dynamic_cast<SIMDBinOpIntr *>(I)) {
    auto op0 = codeGen(B->L(), VMap, constMap);
    auto op1 = codeGen(B->R(), VMap, constMap);
    llvm::Function *decl = nullptr;
    switch (B->K()) {
    case IR::SIMDBinOp::Op::x86_avx2_packssdw:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_packssdw);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_packsswb:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_packsswb);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_packusdw:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_packusdw);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_packuswb:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_packuswb);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_pavg_b:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_pavg_b);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_pavg_w:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_pavg_w);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_phadd_d:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_phadd_d);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_phadd_sw:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_phadd_sw);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_phadd_w:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_phadd_w);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_phsub_d:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_phsub_d);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_phsub_sw:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_phsub_sw);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_phsub_w:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_phsub_w);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_pmadd_ub_sw:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_pmadd_ub_sw);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_pmadd_wd:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_pmadd_wd);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_pmul_hr_sw:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_pmul_hr_sw);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_pmulh_w:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_pmulh_w);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_pmulhu_w:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_pmulhu_w);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_psign_b:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_psign_b);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_psign_d:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_psign_d);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_psign_w:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_psign_w);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_psll_d:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_psll_d);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_psll_q:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_psll_q);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_psll_w:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_psll_w);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_psllv_d:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_psllv_d);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_psllv_d_256:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_psllv_d_256);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_psllv_q:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_psllv_q);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_psllv_q_256:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_psllv_q_256);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_psrav_d:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_psrav_d);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_psrav_d_256:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_psrav_d_256);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_psrl_d:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_psrav_d);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_psrl_q:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_psrl_q);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_psrl_w:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_psrl_w);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_psrlv_d:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_psrlv_d);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_psrlv_d_256:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_psrlv_d_256);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_psrlv_q:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_psrlv_q);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_psrlv_q_256:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_psrlv_q_256);
      break;
    case IR::SIMDBinOp::Op::x86_avx2_pshuf_b:
      decl = Intrinsic::getDeclaration(M, Intrinsic::x86_avx2_pshuf_b);
      break;
    default:
      UNREACHABLE();
    }
    IntrinsicDecls.insert(decl);
    return CallInst::Create(decl, ArrayRef<Value *>({op0, op1}),
                            "intr", cast<Instruction>(b.GetInsertPoint()));
  } else if (auto RC = dynamic_cast<ReservedConst *>(I)) {
    if (!constMap) {
      return RC->getA();
    } else {
      return (*constMap)[RC->getA()];
    }
  } else if (auto SV = dynamic_cast<IR::ShuffleVector *>(I)) {
    // TODO
    (void) SV;
#if (false)
    auto op0 = codeGen(SV->L(), b, VMap, F, constMap);
    auto op1 = codeGen(SV->R(), b, VMap, F, constMap);
    auto M = codeGen(SV->M(), b, VMap, F, constMap);
    return b.CreateShuffleVector(op0, op1, M);
#endif
    return nullptr;
  }
  return nullptr;
}

}