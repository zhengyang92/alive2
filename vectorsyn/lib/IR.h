// Copyright (c) 2020-present, author: Zhengyang Liu (liuz@cs.utah.edu).
// Distributed under the MIT license that can be found in the LICENSE file.
#pragma once

#include "SIMDBinOp.h"

#include "llvm/IR/IRBuilder.h"

#include <vector>

namespace vectorsynth {

class Inst {
  std::string name;
  auto& getName() const { return name; }
public:
  virtual void print(std::ostream &os) const = 0;
  friend std::ostream& operator<<(std::ostream &os, const Inst &val);
  virtual ~Inst() {}
};

class Value : public Inst {
};

class Var final : public Value {
  llvm::Value *v;
public:
  Var(llvm::Value *v) : v(v) {}
  void print(std::ostream &os) const override;
  llvm::Value *V () { return v; }
};

class ReservedConst final : public Value {
  // type?
  llvm::Type *type;
  llvm::Argument *A;
public:
  ReservedConst(llvm::Type *t) : type(t) {}
  void print(std::ostream &os) const override;
  llvm::Type *T () { return type; }
  llvm::Argument *getA () { return A; }
  void setA (llvm::Argument *Arg) { A = Arg; }
};

class UnaryOp final : public Value {
public:
  enum Op { copy };
private:
  Op op;
  Inst* op0;
public:
  UnaryOp(Op op, Inst &op0) : op(op), op0(&op0) {}
  void print(std::ostream &os) const override;
  Inst *Op0() { return op0; }

  Op K() { return op; }
};

class BinOp final : public Value {
public:
  enum Op { band, bor, bxor, add, sub, mul, sdiv, udiv, lshr, ashr, shl};
private:
  Op op;
  Inst* lhs;
  Inst* rhs;
public:
  BinOp(Op op, Inst &lhs, Inst &rhs) : op(op), lhs(&lhs), rhs(&rhs) {}
  void print(std::ostream &os) const override;
  Inst *L() { return lhs; }
  Inst *R() { return rhs; }
  Op K() { return op; }
  static bool isCommutative (Op k) {
    return k == Op::band || k == Op::bor || k == Op::bxor || k == Op::mul;
  }
};

class ICmpOp final : public Value {
public:
  // syntactic pruning: less than/less equal only
  enum Cond { eq, ne, ult, ule, slt, sle};
private:
  Cond cond;
  Inst* lhs;
  Inst* rhs;
public:
  ICmpOp(Cond cond, Inst &lhs, Inst &rhs) : cond(cond), lhs(&lhs), rhs(&rhs) {}
  void print(std::ostream &os) const override;
  Inst *L() { return lhs; }
  Inst *R() { return rhs; }
  Cond K() { return cond; }
};

class BitCastOp final : public Value {
  Inst* i;
  unsigned lanes_from, lanes_to;
  unsigned width_from, width_to;
public:
  BitCastOp(Inst &i, unsigned lf, unsigned wf, unsigned lt, unsigned wt);

  void print(std::ostream &os) const override;
  Inst *I() { return i; }
};

class SIMDBinOpIntr final : public Value {
  IR::SIMDBinOp::Op op;
  Inst* lhs;
  Inst* rhs;
public:
  SIMDBinOpIntr(IR::SIMDBinOp::Op op, Inst &lhs, Inst &rhs)
    : op(op), lhs(&lhs), rhs(&rhs) {}
  void print(std::ostream &os) const override;
  Inst *L() { return lhs; }
  Inst *R() { return rhs; }
  IR::SIMDBinOp::Op K() { return op; }
};

class Hole : Inst {
};

class Load final : public Value {
  Inst* ptr;
public:
  Inst *Ptr() { return ptr; }
};

class Store final : public Inst {
  Inst *ptr;
  Inst *value;
public:
  Inst *Ptr() { return ptr; }
};

class GEP final : public Value {

};
};
