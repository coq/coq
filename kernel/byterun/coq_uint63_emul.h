# pragma once

# include <caml/callback.h>
# include <caml/stack.h>


#define Is_uint63(v) (Tag_val(v) == Custom_tag)

# define DECLARE_NULLOP(name) \
value uint63_##name() { \
  static value* cb = 0; \
  CAMLparam0(); \
  if (!cb) cb = caml_named_value("uint63 " #name); \
  CAMLreturn(*cb); \
  }

# define DECLARE_UNOP(name) \
value uint63_##name(value x) { \
  static value* cb = 0; \
  CAMLparam1(x); \
  if (!cb) cb = caml_named_value("uint63 " #name); \
  CAMLreturn(caml_callback(*cb, x)); \
  }

# define DECLARE_PREDICATE(name) \
value uint63_##name(value x) { \
  static value* cb = 0; \
  CAMLparam1(x); \
  if (!cb) cb = caml_named_value("uint63 " #name); \
  CAMLreturn(Int_val(caml_callback(*cb, x))); \
  }

# define DECLARE_BINOP(name) \
value uint63_##name(value x, value y) { \
  static value* cb = 0; \
  CAMLparam2(x, y); \
  if (!cb) cb = caml_named_value("uint63 " #name); \
  CAMLreturn(caml_callback2(*cb, x, y)); \
  }

# define DECLARE_RELATION(name) \
value uint63_##name(value x, value y) { \
  static value* cb = 0; \
  CAMLparam2(x, y); \
  if (!cb) cb = caml_named_value("uint63 " #name); \
  CAMLreturn(Int_val(caml_callback2(*cb, x, y))); \
  }

# define DECLARE_TEROP(name) \
value uint63_##name(value x, value y, value z) { \
  static value* cb = 0; \
  CAMLparam3(x, y, z); \
  if (!cb) cb = caml_named_value("uint63 " #name); \
  CAMLreturn(caml_callback3(*cb, x, y, z)); \
  }


DECLARE_NULLOP(one)
DECLARE_BINOP(add)
DECLARE_BINOP(addcarry)
DECLARE_TEROP(addmuldiv)
DECLARE_BINOP(div)
DECLARE_TEROP(div21_ml)
DECLARE_RELATION(eq)
DECLARE_PREDICATE(eq0)
DECLARE_UNOP(head0)
DECLARE_BINOP(land)
DECLARE_RELATION(leq)
DECLARE_BINOP(lor)
DECLARE_BINOP(lsl)
DECLARE_UNOP(lsl1)
DECLARE_BINOP(lsr)
DECLARE_UNOP(lsr1)
DECLARE_RELATION(lt)
DECLARE_BINOP(lxor)
DECLARE_BINOP(mod)
DECLARE_BINOP(mul)
DECLARE_BINOP(mulc_ml)
DECLARE_BINOP(sub)
DECLARE_BINOP(subcarry)
DECLARE_UNOP(tail0)

value uint63_div21(value x, value y, value z, value* q) {
  CAMLparam3(x, y, z);
  CAMLlocal1(qr);
  qr = uint63_div21_ml(x, y, z);
  *q = Field(qr, 0);
  CAMLreturn(Field(qr, 1));
}

value uint63_mulc(value x, value y, value* h) {
  CAMLparam2(x, y);
  CAMLlocal1(hl);
  hl = uint63_mulc_ml(x, y);
  *h = Field(hl, 0);
  CAMLreturn(Field(hl, 1));
}
