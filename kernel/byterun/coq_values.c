/***********************************************************************/
/*                                                                     */
/*                           Coq Compiler                              */
/*                                                                     */
/*        Benjamin Gregoire, projets Logical and Cristal               */
/*                        INRIA Rocquencourt                           */
/*                                                                     */
/*                                                                     */
/***********************************************************************/

#include <stdio.h>
#include <caml/memory.h>
#include "coq_fix_code.h"
#include "coq_instruct.h"
#include "coq_memory.h"
#include "coq_values.h"
#include <memory.h>
/* KIND OF VALUES */

#define Setup_for_gc
#define Restore_after_gc

value coq_kind_of_closure(value v) {
  opcode_t * c;
  int is_app = 0;
  c = Code_val(v);
  if (Is_instruction(c, GRAB)) return Val_int(0);
  if (Is_instruction(c, RESTART)) {is_app = 1; c++;}
  if (Is_instruction(c, GRABREC)) return Val_int(1+is_app);
  if (Is_instruction(c, MAKEACCU)) return Val_int(3);
  return Val_int(0);
}


/* DESTRUCT ACCU */

value coq_closure_arity(value clos) {
  opcode_t * c = Code_val(clos);
  if (Is_instruction(c,RESTART)) {
    c++;
    if (Is_instruction(c,GRAB)) return Val_int(3 + c[1] - Wosize_val(clos));
    else { 
      if (Wosize_val(clos) != 2) failwith("Coq Values : coq_closure_arity");
      return Val_int(1);
    }
  }
  if (Is_instruction(c,GRAB)) return Val_int(1 + c[1]);
  return Val_int(1);
}

/* Fonction sur les  fix */

value coq_offset(value v) {
  if (Tag_val(v) == Closure_tag) return Val_int(0);
  else return Val_long(-Wsize_bsize(Infix_offset_val(v)));
}

value coq_offset_closure(value v, value offset){
  return (value)&Field(v, Int_val(offset));
}

value coq_set_bytecode_field(value v, value i, value code) {
  // No write barrier because the bytecode does not live on the OCaml heap
  Field(v, Long_val(i)) = (value) Code_val(code);
  return Val_unit;
}

value coq_offset_tcode(value code,value offset){
  CAMLparam1(code);
  CAMLlocal1(res);
  res = caml_alloc_small(1, Abstract_tag);
  Code_val(res) = Code_val(code) + Int_val(offset);
  CAMLreturn(res);
}

value coq_int_tcode(value pc, value offset) {
  code_t code = Code_val(pc);
  return Val_int(*((code_t) code + Int_val(offset)));
}

value coq_tcode_array(value tcodes) {
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
