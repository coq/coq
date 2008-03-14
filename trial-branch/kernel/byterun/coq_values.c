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
  int res;
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

value coq_offset_tcode(value code,value offset){
  return((value)((code_t)code + Int_val(offset)));
}

value coq_int_tcode(value code, value offset) {
  return Val_int(*((code_t) code + Int_val(offset)));
}
