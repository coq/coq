#ifndef _COQ_FLOAT64_
#define _COQ_FLOAT64_

#include <math.h>

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

DECLARE_FBINOP(fmul, x * y)
DECLARE_FBINOP(fadd, x + y)
DECLARE_FBINOP(fsub, x - y)
DECLARE_FBINOP(fdiv, x / y)
DECLARE_FUNOP(fsqrt, sqrt(x))
DECLARE_FUNOP(next_up, nextafter(x, INFINITY))
DECLARE_FUNOP(next_down, nextafter(x, -INFINITY))

#endif /* _COQ_FLOAT64_ */
