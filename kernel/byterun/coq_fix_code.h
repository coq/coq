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
void coq_init_thread_code(void ** instr_table, void * instr_base);
opcode_t coq_valinstr(int instr);
#define VALINSTR(instr) (coq_valinstr(instr))
#else
#define VALINSTR(instr) instr
#endif /*  THREADED_CODE */

#define Is_instruction(pc,instr) (*pc == VALINSTR(instr))

value coq_tcode_of_code(value code);
value coq_makeaccu (value i);
value coq_pushpop (value i);
value coq_accucond (value i);
value coq_is_accumulate_code(value code);

#endif /* _COQ_FIX_CODE_ */
