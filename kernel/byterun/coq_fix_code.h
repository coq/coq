/***********************************************************************/
/*                                                                     */
/*                           Coq Compiler                              */
/*                                                                     */
/*        Benjamin Gregoire, projets Logical and Cristal               */
/*                        INRIA Rocquencourt                           */
/*                                                                     */
/*                                                                     */
/***********************************************************************/


#ifndef _COQ_FIX_CODE_
#define _COQ_FIX_CODE_

#include "mlvalues.h"
void * coq_stat_alloc (asize_t sz);

#ifdef THREADED_CODE
extern char ** coq_instr_table;
extern char * coq_instr_base;
#define Is_instruction(i1,i2) \
       (*i1 == (opcode_t)(coq_instr_table[i2] - coq_instr_base))
#else 
#define Is_instruction(i1,i2) (*i1 == i2)
#endif

value coq_tcode_of_code(value code, value len);
value coq_makeaccu (value i);
value coq_pushpop (value i);
value coq_accucond (value i);
value coq_is_accumulate_code(value code);
#endif /* _COQ_FIX_CODE_ */
