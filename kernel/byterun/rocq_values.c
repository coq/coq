/***********************************************************************/
/*                                                                     */
/*                          Rocq Compiler                              */
/*                                                                     */
/*        Benjamin Gregoire, projets Logical and Cristal               */
/*                        INRIA Rocquencourt                           */
/*                                                                     */
/*                                                                     */
/***********************************************************************/

#include <stdlib.h>
#include <stdio.h>
#include <caml/memory.h>
#include "rocq_fix_code.h"
#include "rocq_instruct.h"
#include "rocq_memory.h"
#include "rocq_values.h"
#include <memory.h>
/* KIND OF VALUES */

#define Setup_for_gc
#define Restore_after_gc

#define Is_instruction(c, i) rocq_is_instruction(*c, i)

value rocq_kind_of_closure(value v) {
  opcode_t * c;
  int is_app = 0;
  c = Code_val(v);
  if (Is_instruction(c, GRAB)) return Val_int(0);
  if (Is_instruction(c, RESTART)) {is_app = 1; c++;}
  if (Is_instruction(c, GRABREC)) return Val_int(1+is_app);
  if (Is_instruction(c, MAKEACCU)) return Val_int(3);
  return Val_int(0);
}

value rocq_is_accumulate_code(value code)
{
  code_t q = Code_val(code);
  int res;
  res = Is_instruction(q,ACCUMULATE);
  return Val_bool(res);
}

/* DESTRUCT ACCU */

value rocq_closure_arity(value clos) {
  opcode_t * c = Code_val(clos);
  if (Is_instruction(c,RESTART)) {
    c++;
    if (Is_instruction(c,GRAB)) return Val_int(4 + c[1] - Wosize_val(clos));
    else {
      if (Wosize_val(clos) != 3) caml_failwith("Rocq Values : rocq_closure_arity");
      return Val_int(1);
    }
  }
  if (Is_instruction(c,GRAB)) return Val_int(1 + c[1]);
  return Val_int(1);
}

/* Fonction sur les  fix */

value rocq_current_fix(value v) {
  if (Tag_val(v) == Closure_tag) return Val_int(0);
  else return Val_long(Wsize_bsize(Infix_offset_val(v)) / 3);
}

value rocq_shift_fix(value v, value offset) {
  return v + Int_val(offset) * 3 * sizeof(value);
}

value rocq_last_fix(value v) {
  return v + (Int_val(Field(v, 1)) - 2) * sizeof(value);
}

value rocq_set_bytecode_field(value v, value i, value code) {
  // No write barrier because the bytecode does not live on the OCaml heap
  Field(v, Long_val(i)) = (value) Code_val(code);
  return Val_unit;
}

value rocq_offset_tcode(value code,value offset){
  CAMLparam1(code);
  CAMLlocal1(res);
  res = caml_alloc_small(1, Abstract_tag);
  Code_val(res) = Code_val(code) + Int_val(offset);
  CAMLreturn(res);
}

value rocq_int_tcode(value pc, value offset) {
  code_t code = Code_val(pc);
  return Val_int(*((code_t) code + Int_val(offset)));
}

value rocq_tcode_array(value tcodes) {
  CAMLparam1(tcodes);
  CAMLlocal2(res, tmp);
  int i;
  /* Assumes that the vector of types is small. This was implicit in the
    previous code which was building the type array using Alloc_small. */
  res = caml_alloc_small(Wosize_val(tcodes), Default_tag);
  for (i = 0; i < Wosize_val(tcodes); i++) {
    tmp = caml_alloc_small(1, Abstract_tag);
    Code_val(tmp) = (code_t) Field(tcodes, i);
    Store_field(res, i, tmp);
  }
  CAMLreturn(res);
}

CAMLprim value rocq_obj_set_tag (value arg, value new_tag)
{
#if OCAML_VERSION >= 50000
// Placeholder used by native_compute
  abort();
#else
  Tag_val (arg) = Int_val (new_tag);
#endif
  return Val_unit;
}
