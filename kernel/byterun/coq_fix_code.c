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
#include <stdlib.h> 
#include "config.h"
#include "misc.h"
#include "mlvalues.h"
#include "fail.h"
#include "memory.h"
#include "coq_instruct.h"
#include "coq_fix_code.h"

void * coq_stat_alloc (asize_t sz)
{
  void * result = malloc (sz);
  if (result == NULL) raise_out_of_memory ();
  return result;
}

#ifdef THREADED_CODE

char ** coq_instr_table;
char * coq_instr_base;

value coq_makeaccu (value i) {
  code_t q;
  code_t res = coq_stat_alloc(8);
  q = res;
  *q++ = (opcode_t)(coq_instr_table[MAKEACCU] - coq_instr_base);
  *q = (opcode_t)Int_val(i);
  return (value)res;
}

value coq_accucond (value i) {
  code_t q;
  code_t res = coq_stat_alloc(8);
  q = res;
  *q++ = (opcode_t)(coq_instr_table[ACCUMULATECOND] - coq_instr_base);
  *q = (opcode_t)Int_val(i);
  return (value)res;
}

value coq_is_accumulate_code(value code){
  code_t q;
  int res;
  q = (code_t)code;
  res = 
    (*q == (opcode_t)(coq_instr_table[ACCUMULATECOND] - coq_instr_base))
    || 
    (*q == (opcode_t)(coq_instr_table[ACCUMULATE] - coq_instr_base));
  return Val_bool(res);
}

value coq_pushpop (value i) {
  code_t res;
  int n;
  n = Int_val(i);
  if (n == 0) {
    res = coq_stat_alloc(4);
    *res = (opcode_t)(coq_instr_table[STOP] - coq_instr_base);
    return (value)res;
  }
  else {
    code_t q;
    res = coq_stat_alloc(12);
    q = res;
    *q++ = (opcode_t)(coq_instr_table[POP] - coq_instr_base);
    *q++ = (opcode_t)n;
    *q = (opcode_t)(coq_instr_table[STOP] - coq_instr_base);
    return (value)res;
  }
}
  
code_t coq_thread_code (code_t code, asize_t len){
  opcode_t instr;
  code_t p, q;
  code_t res = coq_stat_alloc(len);
  int i;
  q = res;
  len /= sizeof(opcode_t);
  for (p=code; p < code + len; /*nothing*/) {
    instr = *p++;
    *q++ = (opcode_t)(coq_instr_table[instr] - coq_instr_base);
    switch(instr){
      /* instruction with zero operand */
    case ACC0: case ACC1: case ACC2: case ACC3: case ACC4: case ACC5:
    case ACC6: case ACC7: case PUSH: case PUSHACC0: case PUSHACC1:
    case PUSHACC2: case PUSHACC3: case PUSHACC4: case PUSHACC5: case PUSHACC6:
    case PUSHACC7: case ENVACC1: case ENVACC2: case ENVACC3: case ENVACC4:
    case PUSHENVACC1: case PUSHENVACC2: case PUSHENVACC3: case PUSHENVACC4:
    case APPLY1: case APPLY2: case APPLY3: case RESTART: case OFFSETCLOSUREM2:
    case OFFSETCLOSURE0: case OFFSETCLOSURE2: case PUSHOFFSETCLOSUREM2:
    case PUSHOFFSETCLOSURE0: case PUSHOFFSETCLOSURE2:
    case CONST0: case CONST1: case CONST2: case CONST3:
    case PUSHCONST0: case PUSHCONST1: case PUSHCONST2: case PUSHCONST3:
    case ACCUMULATE: case STOP: case FORCE: case MAKEPROD: 
    break;
    
    /* instruction with one operand */
    case ACC: case PUSHACC: case  POP: case ENVACC: case PUSHENVACC: 
    case PUSH_RETADDR:
    case APPLY: case APPTERM1: case APPTERM2: case APPTERM3: case RETURN:
    case GRAB: case COGRAB: 
    case OFFSETCLOSURE: case PUSHOFFSETCLOSURE: 
    case GETGLOBAL: case PUSHGETGLOBAL: 
      /*    case GETGLOBALBOXED: case PUSHGETGLOBALBOXED: */
    case MAKEBLOCK1: case MAKEBLOCK2: case MAKEBLOCK3: case MAKEACCU:
    case CONSTINT: case PUSHCONSTINT: case GRABREC: case PUSHFIELD:
    case ACCUMULATECOND:
    *q++ = *p++;
    break;
    
    /* instruction with two operands */
    case APPTERM: case MAKEBLOCK: case CLOSURE:
      *q++ = *p++; *q++ = *p++;
      break;
    
    /* instruction with four operands */ 
    case MAKESWITCHBLOCK:
      *q++ = *p++; *q++ = *p++; *q++ = *p++; *q++ = *p++;
    break;
    
    /* instruction with arbitrary operands */
    case CLOSUREREC: {
      int i; 
      uint32 n = 2*(*p) + 3; /* ndefs, nvars, start, typlbls,lbls*/
      for(i=0; i < n; i++) *q++ = *p++;
    }
    break; 

    case SWITCH: {
      int i;
      uint32 sizes = *p;
      uint32 const_size = sizes & 0xFFFF;
      uint32 block_size = sizes >> 16;
      sizes = const_size + block_size + 1 ;/* sizes */
      for(i=0; i < sizes; i++) *q++ = *p++;
    }  
    break;
    
    default: 
       invalid_argument("Fatal error in coq_thread_code : bad opcode");
    break;
    }
  }
  if (p != code + len) fprintf(stderr, "error thread code\n");
  return res;
}

value coq_tcode_of_code(value code, value len){
  return (value)coq_thread_code((code_t)code,(asize_t) Long_val(len));
}
#else

value coq_makeaccu (value i) {
  code_t q;
  code_t res = coq_stat_alloc(8);
  q = res;
  *q++ = (opcode_t)MAKEACCU;
  *q = (opcode_t)Int_val(i);
  return (value)res;
}

value coq_accucond (value i) {
  code_t q;
  code_t res = coq_stat_alloc(8);
  q = res;
  *q++ = (opcode_t)ACCUMULATECOND;
  *q = (opcode_t)Int_val(i);
  return (value)res;
}

value coq_is_accumulate_code(value code){
  code_t q;
  int res;
  q = (code_t)code;
  res = 
    (*q == ACCUMULATECOND) || 
    (*q == ACCUMULATE);
  return Val_bool(res);
}

value coq_pushpop (value i) {
  code_t res;
  int n;
  n = Int_val(i);
  if (n == 0) {
    res = coq_stat_alloc(4);
    *res = (opcode_t)STOP;
    return (value)res;
  }
  else {
    res = coq_stat_alloc(12);
    q = res;
    *q++ = (opcode_t)POP;
    *q++ = (opcode_t)n;
    *q = (opcode_t)STOP;
    return (value)res;
  }
}

value coq_tcode_of_code(value s, value size) 
{
  void * new_s = coq_stat_alloc(Int_val(size));
  memmove(new_s, &Byte(s, 0), Int_val(size));
  return (value)new_s;
}

#endif /* THREADED_CODE */



