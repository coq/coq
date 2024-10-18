/************************************************************************/
/*         *      The Rocq Prover / The Rocq Development Team           */
/*  v      *         Copyright INRIA, CNRS and contributors             */
/* <O___,, * (see version control and CREDITS file for authors & dates) */
/*   \VV/  **************************************************************/
/*    //   *    This file is distributed under the terms of the         */
/*         *     GNU Lesser General Public License Version 2.1          */
/*         *     (see LICENSE file for the text of the license)         */
/************************************************************************/

#include <math.h>
#include <stdint.h>

#define CAML_INTERNALS
#include <caml/alloc.h>

#include "rocq_values.h"

union double_bits {
  double d;
  uint64_t u;
};

static double next_up(double x) {
  union double_bits bits;
  if (!(x < INFINITY)) return x; // x is +oo or NaN
  bits.d = x;
  int64_t i = bits.u;
  if (i >= 0) ++bits.u; // x >= +0.0, go away from zero
  else if (bits.u + bits.u == 0) bits.u = 1; // x is -0.0, should almost never happen
  else --bits.u; // x < 0.0, go toward zero
  return bits.d;
}

static double next_down(double x) {
  union double_bits bits;
  if (!(x > -INFINITY)) return x; // x is -oo or NaN
  bits.d = x;
  int64_t i = bits.u;
  if (i == 0) bits.u = INT64_MIN + 1; // x is +0.0
  else if (i < 0) ++bits.u; // x <= -0.0, go away from zero
  else --bits.u; // x > 0.0, go toward zero
  return bits.d;
}

#define DECLARE_FBINOP(name, e)                                         \
  double rocq_##name(double x, double y) {                               \
    return e;                                                           \
  }                                                                     \
                                                                        \
  value rocq_##name##_byte(value x, value y) {                           \
    return caml_copy_double(rocq_##name(Double_val(x), Double_val(y)));  \
  }

#define DECLARE_FUNOP(name, e)                                          \
  double rocq_##name(double x) {                                         \
    return e;                                                           \
  }                                                                     \
                                                                        \
  value rocq_##name##_byte(value x) {                                    \
    return caml_copy_double(rocq_##name(Double_val(x)));                 \
  }

DECLARE_FBINOP(fmul, x * y)
DECLARE_FBINOP(fadd, x + y)
DECLARE_FBINOP(fsub, x - y)
DECLARE_FBINOP(fdiv, x / y)
DECLARE_FUNOP(fsqrt, sqrt(x))
DECLARE_FUNOP(next_up, next_up(x))
DECLARE_FUNOP(next_down, next_down(x))

value rocq_is_double(value x) {
  return Val_long(Is_double(x));
}
