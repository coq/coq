/***********************************************************************/
/*                                                                     */
/*                           Coq Compiler                              */
/*                                                                     */
/*        Benjamin Gregoire, projets Logical and Cristal               */
/*                        INRIA Rocquencourt                           */
/*                                                                     */
/*                                                                     */
/***********************************************************************/

#include <stdlib.h>
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

#define Is_instruction(c, i) coq_is_instruction(*c, i)

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

value coq_is_accumulate_code(value code)
{
  code_t q = Code_val(code);
  int res;
  res = Is_instruction(q,ACCUMULATE);
  return Val_bool(res);
}

/* DESTRUCT ACCU */

value coq_closure_arity(value clos) {
  opcode_t * c = Code_val(clos);
  if (Is_instruction(c,RESTART)) {
    c++;
    if (Is_instruction(c,GRAB)) return Val_int(4 + c[1] - Wosize_val(clos));
    else {
      if (Wosize_val(clos) != 3) caml_failwith("Coq Values : coq_closure_arity");
      return Val_int(1);
    }
  }
  if (Is_instruction(c,GRAB)) return Val_int(1 + c[1]);
  return Val_int(1);
}

/* Fonction sur les  fix */

value coq_current_fix(value v) {
  if (Tag_val(v) == Closure_tag) return Val_int(0);
  else return Val_long(Wsize_bsize(Infix_offset_val(v)) / 3);
}

value coq_shift_fix(value v, value offset) {
  return v + Int_val(offset) * 3 * sizeof(value);
}

value coq_last_fix(value v) {
  return v + (Int_val(Field(v, 1)) - 2) * sizeof(value);
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

code_t coq_accumulate_addr;

value coq_proxy_accu(value clos) {
  value v;
  CAMLassert(Tag_val(clos) == Closure_tag && Arity_closinfo(Closinfo_val(clos)) == 2);
  /* Field 2 of the closure contains the code pointer for the arity-2 direct call. */
  coq_accumulate_addr = ((code_t *)clos)[2];
  /* The following assembly block does not perform any meaningful computation;
     it just returns a pointer to the inner code (notice the initial "jmp").
     The inner code translates the call "foo x" (i.e., "%apply x foo") into
     "accumulate foo.2 x". For both calls, the two arguments are stored in %rax
     and %rbx, while register %rdi is caller-saved. */
  asm("jmp 1f\n\t"
      ".align 8\n\t"
      ".quad 3067\n"
      "2:\n\t"
      "mov %%rax, %%rdi\n\t"
      "mov 16(%%rbx), %%rax\n\t"
      "mov %%rdi, %%rbx\n\t"
      "mov coq_accumulate_addr@GOTPCREL(%%rip), %%rdi\n\t"
      "jmp *(%%rdi)\n"
      "1:\n\t"
      "lea 2b(%%rip), %0\n\t"
      : "=r"(v));
  /* v is a pointer that can be used as field 0 of an OCaml closure. But it is
     also a pointer to a block that is ignored by the garbage collector (notice
     the header 3067). So, v can be put inside closures that do not have tag 247. */
  return v;
}
