/************************************************************************/
/*         *   The Coq Proof Assistant / The Coq Development Team       */
/*  v      *         Copyright INRIA, CNRS and contributors             */
/* <O___,, * (see version control and CREDITS file for authors & dates) */
/*   \VV/  **************************************************************/
/*    //   *    This file is distributed under the terms of the         */
/*         *     GNU Lesser General Public License Version 2.1          */
/*         *     (see LICENSE file for the text of the license)         */
/************************************************************************/

#ifndef _COQ_FLOAT64_
#define _COQ_FLOAT64_

#include <math.h>

#define DECLARE_FREL(name, e)                                           \
  int coq_##name(double x, double y) {                                  \
    return e;                                                           \
  }                                                                     \
                                                                        \
  value coq_##name##_byte(value x, value y) {                           \
    return coq_##name(Double_val(x), Double_val(y));                    \
  }

#define DECLARE_FBINOP(name, e)                                         \
  double coq_##name(double x, double y) {                               \
    return e;                                                           \
  }                                                                     \
                                                                        \
  value coq_##name##_byte(value x, value y) {                           \
    return caml_copy_double(coq_##name(Double_val(x), Double_val(y)));  \
  }

#define DECLARE_FUNOP(name, e)                                          \
  double coq_##name(double x) {                                         \
    return e;                                                           \
  }                                                                     \
                                                                        \
  value coq_##name##_byte(value x) {                                    \
    return caml_copy_double(coq_##name(Double_val(x)));                 \
  }

DECLARE_FREL(feq, x == y)
DECLARE_FREL(flt, x < y)
DECLARE_FREL(fle, x <= y)
DECLARE_FBINOP(fmul, x * y)
DECLARE_FBINOP(fadd, x + y)
DECLARE_FBINOP(fsub, x - y)
DECLARE_FBINOP(fdiv, x / y)
DECLARE_FUNOP(fsqrt, sqrt(x))
DECLARE_FUNOP(next_up, nextafter(x, INFINITY))
DECLARE_FUNOP(next_down, nextafter(x, -INFINITY))

value coq_is_double(value x) {
  return Val_long(Is_double(x));
}

#endif /* _COQ_FLOAT64_ */
