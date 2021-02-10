// Copyright (c) 2020-present, author: Zhengyang Liu (liuz@cs.utah.edu).
// Distributed under the MIT license that can be found in the LICENSE file.
#include "IR.h"

#include <string>

using namespace std;

namespace vectorsynth {

void Var::print(ostream &os) const {
  const char *str = "val ";
  os << str;
}

void ReservedConst::print(ostream &os) const {
  const char *str = "reservedconst ";
  os << str;
}


void BinOp::print(ostream &os) const {
  const char *str = nullptr;
  switch (op) {
  case band:       str = "and "; break;
  case bor:        str = "or ";  break;
  case bxor:       str = "xor "; break;
  case add:        str = "add "; break;
  case sub:        str = "sub "; break;
  case mul:        str = "mul "; break;
  case sdiv:       str = "sdiv ";break;
  case udiv:       str = "udiv ";break;
  case lshr:       str = "lshr ";break;
  case ashr:       str = "ashr ";break;
  case shl:        str = "shl " ;break;
  }
  os << str;
}

void BinIntr::print(ostream &os) const {
  const char *str = nullptr;
  switch (op) {
  case IR::SIMDBinOp::Op::x86_avx2_pshuf_b:     str = "v.avx2.pshufb "; break;
  default:                                      str = "(null)"        ; break;
  }
  os << str;
}

/*
BitCastOp(Inst &i, unsigned lf, unsigned wf, unsigned lt, unsigned wt);
  : i(&i), lanes_from(lf), lanes_to(lt), width_from(width_from), width_to(wt) {
    assert(lf * wf == lt * wt);
}*/
};
