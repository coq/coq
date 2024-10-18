/***********************************************************************/
/*                                                                     */
/*                          Rocq Compiler                              */
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
#include "rocq_instruct.h"
#include "rocq_arity.h"
#include "rocq_fix_code.h"

#ifdef THREADED_CODE

static char ** rocq_instr_table;
static char * rocq_instr_base;
#define VALINSTR(instr) ((opcode_t)(rocq_instr_table[instr] - rocq_instr_base))

void rocq_init_thread_code(void ** instr_table, void * instr_base)
{
  rocq_instr_table = (char **) instr_table;
  rocq_instr_base = (char *) instr_base;
}

#else
#define VALINSTR(instr) instr
#endif /*  THREADED_CODE */

int rocq_is_instruction(opcode_t instr1, opcode_t instr2)
{
  return instr1 == VALINSTR(instr2);
}

void * rocq_stat_alloc (asize_t sz)
{
  void * result = malloc (sz);
  if (result == NULL) caml_raise_out_of_memory ();
  return result;
}

static opcode_t accu_instr;
code_t accumulate = &accu_instr;

value rocq_accumulate(value unit)
{
  CAMLparam1(unit);
  CAMLlocal1(res);
  accu_instr = VALINSTR(ACCUMULATE);
  res = caml_alloc_small(1, Abstract_tag);
  Code_val(res) = accumulate;
  CAMLreturn(res);
}

value rocq_makeaccu (value i) {
  CAMLparam1(i);
  CAMLlocal1(res);
  code_t q = rocq_stat_alloc(2 * sizeof(opcode_t));
  res = caml_alloc_small(1, Abstract_tag);
  Code_val(res) = q;
  *q++ = VALINSTR(MAKEACCU);
  *q = (opcode_t)Int_val(i);
  CAMLreturn(res);
}

value rocq_pushpop (value i) {
  CAMLparam1(i);
  CAMLlocal1(res);
  code_t q;
  res = caml_alloc_small(1, Abstract_tag);
  int n = Int_val(i);
  if (n == 0) {
    q = rocq_stat_alloc(sizeof(opcode_t));
    Code_val(res) = q;
    *q = VALINSTR(STOP);
    CAMLreturn(res);
  }
  else {
    q = rocq_stat_alloc(3 * sizeof(opcode_t));
    Code_val(res) = q;
    *q++ = VALINSTR(POP);
    *q++ = (opcode_t)n;
    *q = VALINSTR(STOP);
    CAMLreturn(res);
  }
}

#ifdef ARCH_BIG_ENDIAN
#define Reverse_32(dst,src) {                                               \
  char * _p, * _q;                                                          \
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

value rocq_tcode_of_code (value code) {
  CAMLparam1 (code);
  CAMLlocal1 (res);
  code_t p, q;
  asize_t len = (asize_t) caml_string_length(code);
  res = caml_alloc_small(1, Abstract_tag);
  q = rocq_stat_alloc(len);
  Code_val(res) = q;
  len /= sizeof(opcode_t);
  for (p = (code_t)code; p < (code_t)code + len; /*nothing*/) {
    opcode_t instr;
    COPY32(&instr,p);
    p++;
    if (instr < 0 || instr > STOP) abort();
    *q++ = VALINSTR(instr);
    if (instr == SWITCH) {
      uint32_t i, sizes, const_size, block_size;
      COPY32(q,p); p++;
      sizes=*q++;
      const_size = sizes >> 8;
      block_size = sizes & 0xFF;
      sizes = const_size + block_size;
      for(i=0; i<sizes; i++) { COPY32(q,p); p++; q++; };
    } else if (instr == CLOSUREREC || instr==CLOSURECOFIX) {
      uint32_t i, n;
      COPY32(q,p); p++; /* ndefs */
      n = 3 + 2*(*q);  /* ndefs, nvars, start, typlbls,lbls*/
      q++;
      for(i=1; i<n; i++) { COPY32(q,p); p++; q++; };
    } else {
      int i, ar;
      ar = arity[instr];
      if (ar < 0) abort();
      for(i=0; i<ar; i++) { COPY32(q,p); p++; q++; };
    }
  }
  CAMLreturn(res);
}
