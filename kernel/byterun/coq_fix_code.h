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

#include <caml/mlvalues.h>
void * coq_stat_alloc (asize_t sz);

#ifdef THREADED_CODE
extern char ** coq_instr_table;
extern char * coq_instr_base;
#define VALINSTR(instr) ((opcode_t)(coq_instr_table[instr] - coq_instr_base))
#else
#define VALINSTR(instr) instr
#endif /*  THREADED_CODE */

int coq_is_instruction(opcode_t, opcode_t);
value coq_tcode_of_code(value code);
value coq_makeaccu (value i);
value coq_pushpop (value i);
value coq_accucond (value i);

#endif /* _COQ_FIX_CODE_ */
