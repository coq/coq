/***********************************************************************/
/*                                                                     */
/*                           Coq Compiler                              */
/*                                                                     */
/*        Benjamin Gregoire, projets Logical and Cristal               */
/*                        INRIA Rocquencourt                           */
/*                                                                     */
/*                                                                     */
/***********************************************************************/

/* Arnaud Spiwack: expanded the virtual machine with operators used
   for fast computation of bounded (31bits) integers */

#include <stdio.h>
#include <stdlib.h> 
#include <stdint.h>
#include <caml/config.h>
#include <caml/misc.h>
#include <caml/mlvalues.h>
#include <caml/fail.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include "coq_instruct.h"
#include "coq_fix_code.h"

#ifdef THREADED_CODE
char ** coq_instr_table;
char * coq_instr_base;
int arity[STOP+1];

void init_arity () {
  /* instruction with zero operand */
  arity[ACC0]=arity[ACC1]=arity[ACC2]=arity[ACC3]=arity[ACC4]=arity[ACC5]=
    arity[ACC6]=arity[ACC7]=arity[PUSH]=arity[PUSHACC0]=arity[PUSHACC1]=
    arity[PUSHACC2]=arity[PUSHACC3]=arity[PUSHACC4]=arity[PUSHACC5]=
    arity[PUSHACC6]=arity[PUSHACC7]=arity[ENVACC1]=arity[ENVACC2]=
    arity[ENVACC3]=arity[ENVACC4]=arity[PUSHENVACC1]=arity[PUSHENVACC2]=
    arity[PUSHENVACC3]=arity[PUSHENVACC4]=arity[APPLY1]=arity[APPLY2]=
    arity[APPLY3]=arity[APPLY4]=arity[RESTART]=arity[OFFSETCLOSUREM2]=
    arity[OFFSETCLOSURE0]=arity[OFFSETCLOSURE2]=arity[PUSHOFFSETCLOSUREM2]=
    arity[PUSHOFFSETCLOSURE0]=arity[PUSHOFFSETCLOSURE2]=
    arity[GETFIELD0]=arity[GETFIELD1]=arity[SETFIELD0]=arity[SETFIELD1]=
    arity[CONST0]=arity[CONST1]=arity[CONST2]=arity[CONST3]=
    arity[PUSHCONST0]=arity[PUSHCONST1]=arity[PUSHCONST2]=arity[PUSHCONST3]=
    arity[ACCUMULATE]=arity[STOP]=arity[MAKEPROD]= 
    arity[ADDINT63]=arity[SUBINT63]=arity[LTINT63]=arity[LEINT63]=
    arity[ISINT]=arity[AREINT2]=0;
  /* instruction with one operand */
  arity[ACC]=arity[PUSHACC]=arity[POP]=arity[ENVACC]=arity[PUSHENVACC]=
    arity[PUSH_RETADDR]=arity[APPLY]=arity[APPTERM1]=arity[APPTERM2]=
    arity[APPTERM3]=arity[RETURN]=arity[GRAB]=arity[OFFSETCLOSURE]=
    arity[PUSHOFFSETCLOSURE]=arity[GETGLOBAL]=arity[PUSHGETGLOBAL]=
    arity[MAKEBLOCK1]=arity[MAKEBLOCK2]=arity[MAKEBLOCK3]=arity[MAKEBLOCK4]=
    arity[MAKEACCU]=arity[CONSTINT]=arity[PUSHCONSTINT]=arity[GRABREC]=
    arity[PUSHFIELDS]=arity[GETFIELD]=arity[SETFIELD]=
    arity[BRANCH]=arity[ENSURESTACKCAPACITY]=
    arity[CHECKADDINT63]=arity[CHECKADDCINT63]=arity[CHECKADDCARRYCINT63]=
    arity[CHECKSUBINT63]=arity[CHECKSUBCINT63]=arity[CHECKSUBCARRYCINT63]=
    arity[CHECKMULINT63]=arity[CHECKMULCINT63]=
    arity[CHECKDIVINT63]=arity[CHECKMODINT63]=arity[CHECKDIVEUCLINT63]=
    arity[CHECKDIV21INT63]=
    arity[CHECKLXORINT63]=arity[CHECKLORINT63]=arity[CHECKLANDINT63]=
    arity[CHECKLSLINT63]=arity[CHECKLSRINT63]=arity[CHECKADDMULDIVINT63]=
    arity[CHECKLSLINT63CONST1]=arity[CHECKLSRINT63CONST1]=
    arity[CHECKEQINT63]=arity[CHECKLTINT63]=arity[CHECKLEINT63]=
    arity[CHECKCOMPAREINT63]=arity[CHECKHEAD0INT63]=arity[CHECKTAIL0INT63]=1;
  /* instruction with two operands */
  arity[APPTERM]=arity[MAKEBLOCK]=arity[CLOSURE]=
  arity[PROJ]=2;
  /* instruction with four operands */ 
  arity[MAKESWITCHBLOCK]=4;
  /* instruction with arbitrary operands */
  arity[CLOSUREREC]=arity[CLOSURECOFIX]=arity[SWITCH]=0;
}

#endif /*  THREADED_CODE */


void * coq_stat_alloc (asize_t sz)
{
  void * result = malloc (sz);
  if (result == NULL) raise_out_of_memory ();
  return result;
}

value coq_makeaccu (value i) {
  CAMLparam1(i);
  CAMLlocal1(res);
  code_t q = coq_stat_alloc(2 * sizeof(opcode_t));
  res = caml_alloc_small(1, Abstract_tag);
  Code_val(res) = q;
  *q++ = VALINSTR(MAKEACCU);
  *q = (opcode_t)Int_val(i);
  CAMLreturn(res);
}

value coq_pushpop (value i) {
  CAMLparam1(i);
  CAMLlocal1(res);
  code_t q;
  res = caml_alloc_small(1, Abstract_tag);
  int n = Int_val(i);
  if (n == 0) {
    q = coq_stat_alloc(sizeof(opcode_t));
    Code_val(res) = q;
    *q = VALINSTR(STOP);
    CAMLreturn(res);
  }
  else {
    q = coq_stat_alloc(3 * sizeof(opcode_t));
    Code_val(res) = q;
    *q++ = VALINSTR(POP);
    *q++ = (opcode_t)n;
    *q = VALINSTR(STOP);
    CAMLreturn(res);
  }
}

value coq_is_accumulate_code(value code){
  code_t q = Code_val(code);
  int res;
  res = Is_instruction(q,ACCUMULATE);
  return Val_bool(res);
}

#ifdef ARCH_BIG_ENDIAN
#define Reverse_32(dst,src) {                                               \
  char * _p, * _q;							    \
  char _a, _b;                                                              \
  _p = (char *) (src);                                                      \
  _q = (char *) (dst);                                                      \
  _a = _p[0];                                                               \
  _b = _p[1];                                                               \
  _q[0] = _p[3];                                                            \
  _q[1] = _p[2];                                                            \
  _q[3] = _a;                                                               \
  _q[2] = _b;                                                               \
}
#define COPY32(dst,src) Reverse_32(dst,src)
#else
#define COPY32(dst,src) (*dst=*src)
#endif /* ARCH_BIG_ENDIAN */

value coq_tcode_of_code (value code) {
  CAMLparam1 (code);
  CAMLlocal1 (res);
  code_t p, q;
  asize_t len = (asize_t) caml_string_length(code);
  res = caml_alloc_small(1, Abstract_tag);
  q = coq_stat_alloc(len);
  Code_val(res) = q;
  len /= sizeof(opcode_t);
  for (p = (code_t)code; p < (code_t)code + len; /*nothing*/) {  
    opcode_t instr;
    COPY32(&instr,p); 
    p++;
    if (instr < 0 || instr > STOP){
      instr = STOP;
    };
    *q++ = VALINSTR(instr);
    if (instr == SWITCH) {
      uint32_t i, sizes, const_size, block_size;
      COPY32(q,p); p++;
      sizes=*q++;
      const_size = sizes & 0xFFFFFF;
      block_size = sizes >> 24;
      sizes = const_size + block_size;
      for(i=0; i<sizes; i++) { COPY32(q,p); p++; q++; };
    } else if (instr == CLOSUREREC || instr==CLOSURECOFIX) {
      uint32_t i, n;
      COPY32(q,p); p++; /* ndefs */
      n = 3 + 2*(*q);  /* ndefs, nvars, start, typlbls,lbls*/
      q++;
      for(i=1; i<n; i++) { COPY32(q,p); p++; q++; };
    } else {
      uint32_t i, ar;
      ar = arity[instr]; 
      for(i=0; i<ar; i++) { COPY32(q,p); p++; q++; };
    }
  }
  CAMLreturn(res);
}
