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
#include <caml/config.h>
#include <caml/misc.h>
#include <caml/mlvalues.h>
#include <caml/fail.h>
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
    arity[ACC6]=arity[ACC7]=
    arity[PUSH]=
    arity[PUSHACC0]=arity[PUSHACC1]=arity[PUSHACC2]=arity[PUSHACC3]=
    arity[PUSHACC4]=arity[PUSHACC5]=arity[PUSHACC6]=arity[PUSHACC7]=
    arity[ENVACC1]=arity[ENVACC2]=arity[ENVACC3]=arity[ENVACC4]=
    arity[PUSHENVACC1]=arity[PUSHENVACC2]=
    arity[PUSHENVACC3]=arity[PUSHENVACC4]=
    arity[APPLY1]=arity[APPLY2]=arity[APPLY3]=arity[APPLY4]=
    arity[RESTART]=
    arity[OFFSETCLOSUREM2]=arity[OFFSETCLOSURE0]=arity[OFFSETCLOSURE2]=
    arity[PUSHOFFSETCLOSUREM2]=
    arity[PUSHOFFSETCLOSURE0]=arity[PUSHOFFSETCLOSURE2]=
    arity[GETFIELD0]=arity[GETFIELD1]=arity[SETFIELD0]=arity[SETFIELD1]=
    arity[CONST0]=arity[CONST1]=arity[CONST2]=arity[CONST3]=
    arity[PUSHCONST0]=arity[PUSHCONST1]=arity[PUSHCONST2]=arity[PUSHCONST3]=
    arity[ACCUMULATE]=arity[STOP]=arity[MAKEPROD]= 
    arity[ADDINT31]=arity[SUBINT31]=arity[LTINT31]=arity[LEINT31]=
    arity[AREINT2]=0;
  /* instruction with one operand */
  arity[ACC]=arity[PUSHACC]=arity[POP]=arity[ENVACC]=arity[PUSHENVACC]=
    arity[PUSH_RETADDR]=arity[APPLY]=arity[APPTERM1]=arity[APPTERM2]=
    arity[APPTERM3]=arity[RETURN]=arity[GRAB]=arity[OFFSETCLOSURE]=
    arity[PUSHOFFSETCLOSURE]=arity[GETGLOBAL]=arity[PUSHGETGLOBAL]=
    arity[MAKEBLOCK1]=arity[MAKEBLOCK2]=arity[MAKEBLOCK3]=arity[MAKEBLOCK4]=
    arity[MAKEACCU]=arity[CONSTINT]=arity[PUSHCONSTINT]=arity[GRABREC]=
    arity[PUSHFIELDS]=arity[GETFIELD]=arity[SETFIELD]=arity[ACCUMULATECOND]=
    arity[BRANCH]=
    arity[CHECKADDINT31]=arity[CHECKADDCINT31]=arity[CHECKADDCARRYCINT31]=
    arity[CHECKSUBINT31]=arity[CHECKSUBCINT31]=arity[CHECKSUBCARRYCINT31]=
    arity[CHECKMULINT31]=arity[CHECKMULCINT31]= 
    arity[CHECKDIVINT31]=arity[CHECKMODINT31]=arity[CHECKDIVEUCLINT31]=
    arity[CHECKDIV21INT31]= 
    arity[CHECKLXORINT31]=arity[CHECKLORINT31]=arity[CHECKLANDINT31]= 
    arity[CHECKLSLINT31]=arity[CHECKLSRINT31]=arity[CHECKADDMULDIVINT31]=  
    arity[CHECKLSLINT31CONST1]=arity[CHECKLSRINT31CONST1]=
    arity[CHECKEQINT31]=arity[CHECKLTINT31]=arity[CHECKLEINT31]=
    arity[CHECKCOMPAREINT31]=arity[CHECKHEAD0INT31]=arity[CHECKTAIL0INT31]=
    1;
  /* instruction with two operands */
  arity[APPTERM]=arity[MAKEBLOCK]=arity[CLOSURE]=
    arity[ISINT_CAML_CALL1]=arity[ISARRAY_CAML_CALL1]=
    arity[ISINT_CAML_CALL2]=arity[ISARRAY_INT_CAML_CALL2]=
    arity[ISARRAY_INT_CAML_CALL3]=
    2;
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
  code_t q;
  code_t res = coq_stat_alloc(8);
  q = res;
  *q++ = VALINSTR(MAKEACCU);
  *q = (opcode_t)Int_val(i);
  return (value)res;
}

value coq_accucond (value i) {
  code_t q;
  code_t res = coq_stat_alloc(8);
  q = res;
  *q++ = VALINSTR(ACCUMULATECOND);
  *q = (opcode_t)Int_val(i);
  return (value)res;
}

value coq_pushpop (value i) {
  code_t res;
  int n;
  n = Int_val(i);
  if (n == 0) {
    res = coq_stat_alloc(4);
    *res = VALINSTR(STOP);
    return (value)res;
  }
  else {
    code_t q;
    res = coq_stat_alloc(12);
    q = res;
    *q++ = VALINSTR(POP);
    *q++ = (opcode_t)n;
    *q = VALINSTR(STOP);
    return (value)res;
  }
}

value coq_is_accumulate_code(value code){
  code_t q;
  int res;
  q = (code_t)code;
  res = Is_instruction(q,ACCUMULATECOND) || Is_instruction(q,ACCUMULATE);
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

value coq_tcode_of_code (value code, value size) {
  code_t p, q, res; 
  asize_t len = (asize_t) Long_val(size);
  res = coq_stat_alloc(len);
  q = res;
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
      uint32 i, sizes, const_size, block_size;
      COPY32(q,p); p++;
      sizes=*q++;
      const_size = sizes & 0xFFFF;
      block_size = sizes >> 16;
      sizes = const_size + block_size;
      for(i=0; i<sizes; i++) { COPY32(q,p); p++; q++; };
    } else if (instr == CLOSUREREC || instr==CLOSURECOFIX) {
      uint32 i, n;
      COPY32(q,p); p++; /* ndefs */
      n = 3 + 2*(*q);  /* ndefs, nvars, start, typlbls,lbls*/
      q++;
      for(i=1; i<n; i++) { COPY32(q,p); p++; q++; };
    } else {
      uint32 i, ar;
      ar = arity[instr]; 
      for(i=0; i<ar; i++) { COPY32(q,p); p++; q++; };
    }
  }
  return (value)res;
}
