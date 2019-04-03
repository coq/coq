# pragma once

# include <caml/callback.h>
# include <caml/stack.h>


#define Is_uint63(v) (Tag_val(v) == Custom_tag)

#define uint_of_value(val) (((uint32_t)(val)) >> 1)

# define DECLARE_NULLOP(name) \
value uint63_##name() { \
  static value* cb = 0; \
  CAMLparam0(); \
  if (!cb) cb = caml_named_value("uint63 " #name); \
  CAMLreturn(*cb); \
  }

# define DECLARE_UNOP(name) \
value uint63_##name##_ml(value x) { \
  static value* cb = 0; \
  CAMLparam1(x); \
  if (!cb) cb = caml_named_value("uint63 " #name); \
  CAMLreturn(caml_callback(*cb, x)); \
  }

# define CALL_UNOP_NOASSIGN(name, x) \
  value uint63_return_value__; \
  value uint63_arg_x__ = (x); \
  Setup_for_gc; \
  uint63_return_value__ = uint63_##name##_ml(uint63_arg_x__); \
  Restore_after_gc

# define CALL_UNOP(name, x) do{ \
    CALL_UNOP_NOASSIGN(name, x); \
    accu = uint63_return_value__; \
  }while(0)

# define CALL_PREDICATE(r, name, x) do{ \
    CALL_UNOP_NOASSIGN(name, x); \
    (r) = Int_val(uint63_return_value__); \
  }while(0)

# define DECLARE_BINOP(name) \
value uint63_##name##_ml(value x, value y) { \
  static value* cb = 0; \
  CAMLparam2(x, y); \
  if (!cb) cb = caml_named_value("uint63 " #name); \
  CAMLreturn(caml_callback2(*cb, x, y)); \
  }

# define CALL_BINOP_NOASSIGN(name, x, y) \
  value uint63_return_value__; \
  value uint63_arg_x__ = (x); \
  value uint63_arg_y__ = (y); \
  Setup_for_gc; \
  uint63_return_value__ = uint63_##name##_ml(uint63_arg_x__, uint63_arg_y__); \
  Restore_after_gc

# define CALL_BINOP(name, x, y) do{ \
    CALL_BINOP_NOASSIGN(name, x, y);  \
    accu = uint63_return_value__; \
  }while(0)

# define CALL_RELATION(r, name, x, y) do{ \
    CALL_BINOP_NOASSIGN(name, x, y); \
    (r) = Int_val(uint63_return_value__); \
  }while(0)

# define DECLARE_TEROP(name) \
value uint63_##name##_ml(value x, value y, value z) { \
  static value* cb = 0; \
  CAMLparam3(x, y, z); \
  if (!cb) cb = caml_named_value("uint63 " #name); \
  CAMLreturn(caml_callback3(*cb, x, y, z)); \
  }

# define CALL_TEROP(name, x, y, z) do{ \
    value uint63_return_value__; \
    value uint63_arg_x__ = (x); \
    value uint63_arg_y__ = (y); \
    value uint63_arg_z__ = (z); \
    Setup_for_gc; \
    uint63_return_value__ = uint63_##name##_ml(uint63_arg_x__, uint63_arg_y__, uint63_arg_z__); \
    Restore_after_gc; \
    accu = uint63_return_value__; \
  }while(0)

DECLARE_NULLOP(one)
DECLARE_BINOP(add)
#define Uint63_add(x, y) CALL_BINOP(add, x, y)
DECLARE_BINOP(addcarry)
#define Uint63_addcarry(x, y) CALL_BINOP(addcarry, x, y)
DECLARE_TEROP(addmuldiv)
#define Uint63_addmuldiv(x, y, z) CALL_TEROP(addmuldiv, x, y, z)
DECLARE_BINOP(div)
#define Uint63_div(x, y) CALL_BINOP(div, x, y)
DECLARE_BINOP(eq)
#define Uint63_eq(r, x, y) CALL_RELATION(r, eq, x, y)
DECLARE_UNOP(eq0)
#define Uint63_eq0(r, x) CALL_PREDICATE(r, eq0, x)
DECLARE_UNOP(head0)
#define Uint63_head0(x) CALL_UNOP(head0, x)
DECLARE_BINOP(land)
#define Uint63_land(x, y) CALL_BINOP(land, x, y)
DECLARE_BINOP(leq)
#define Uint63_leq(r, x, y) CALL_RELATION(r, leq, x, y)
DECLARE_BINOP(lor)
#define Uint63_lor(x, y) CALL_BINOP(lor, x, y)
DECLARE_BINOP(lsl)
#define Uint63_lsl(x, y) CALL_BINOP(lsl, x, y)
DECLARE_UNOP(lsl1)
#define Uint63_lsl1(x) CALL_UNOP(lsl1, x)
DECLARE_BINOP(lsr)
#define Uint63_lsr(x, y) CALL_BINOP(lsr, x, y)
DECLARE_UNOP(lsr1)
#define Uint63_lsr1(x) CALL_UNOP(lsr1, x)
DECLARE_BINOP(lt)
#define Uint63_lt(r, x, y) CALL_RELATION(r, lt, x, y)
DECLARE_BINOP(lxor)
#define Uint63_lxor(x, y) CALL_BINOP(lxor, x, y)
DECLARE_BINOP(mod)
#define Uint63_mod(x, y) CALL_BINOP(mod, x, y)
DECLARE_BINOP(mul)
#define Uint63_mul(x, y) CALL_BINOP(mul, x, y)
DECLARE_BINOP(sub)
#define Uint63_sub(x, y) CALL_BINOP(sub, x, y)
DECLARE_BINOP(subcarry)
#define Uint63_subcarry(x, y) CALL_BINOP(subcarry, x, y)
DECLARE_UNOP(tail0)
#define Uint63_tail0(x) CALL_UNOP(tail0, x)

DECLARE_TEROP(div21_ml)
# define Uint63_div21(x, y, z, q) do{ \
    value uint63_return_value__; \
    value uint63_arg_x__ = (x); \
    value uint63_arg_y__ = (y); \
    value uint63_arg_z__ = (z); \
    Setup_for_gc; \
    uint63_return_value__ = \
      uint63_div21_ml_ml(uint63_arg_x__, uint63_arg_y__, uint63_arg_z__); \
    Restore_after_gc; \
    *q = Field(uint63_return_value__, 0); \
    accu = Field(uint63_return_value__, 1); \
  }while(0)

DECLARE_BINOP(mulc_ml)
# define Uint63_mulc(x, y, h) do{ \
    value uint63_return_value__; \
    value uint63_arg_x__ = (x); \
    value uint63_arg_y__ = (y); \
    Setup_for_gc; \
    uint63_return_value__ = \
      uint63_mulc_ml_ml(uint63_arg_x__, uint63_arg_y__); \
    Restore_after_gc; \
    *(h) = Field(uint63_return_value__, 0); \
    accu = Field(uint63_return_value__, 1); \
  }while(0)

DECLARE_UNOP(to_float)
#define Uint63_to_double(x) CALL_UNOP(to_float, x)

DECLARE_UNOP(of_float)
#define Uint63_of_double(f) do{ \
  Coq_copy_double(f); \
  CALL_UNOP(of_float, accu); \
  }while(0)

DECLARE_UNOP(of_int)
#define Uint63_of_int(x) CALL_UNOP(of_int, x)

DECLARE_UNOP(to_int_saturate)
#define Int_of_uint63(x) CALL_PREDICATE(accu, to_int_saturate, x)
