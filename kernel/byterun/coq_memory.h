/***********************************************************************/
/*                                                                     */
/*                           Coq Compiler                              */
/*                                                                     */
/*        Benjamin Gregoire, projets Logical and Cristal               */
/*                        INRIA Rocquencourt                           */
/*                                                                     */
/*                                                                     */
/***********************************************************************/

#ifndef _COQ_MEMORY_
#define _COQ_MEMORY_

#include <caml/config.h>
#include <caml/fail.h>
#include <caml/misc.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>


#define Coq_stack_size (4096 * sizeof(value))
#define Coq_stack_threshold (256 * sizeof(value))
#define Coq_max_stack_size (256 * 1024)

#define TRANSP 0
#define BOXED 1

/* stack */

extern value * coq_stack_low;
extern value * coq_stack_high;
extern value * coq_stack_threshold;

/* global_data */

extern int coq_all_transp;

extern int drawinstr;
/* interp state */

extern value * coq_sp;
/* Some predefined pointer code */ 
extern code_t accumulate;

/* functions over global environment */

value coq_static_alloc(value size);  /* ML */

value init_coq_vm(value unit); /* ML */
value re_init_coq_vm(value unit); /* ML */

void  realloc_coq_stack(asize_t required_space); 
value coq_set_transp_value(value transp); /* ML */
value get_coq_transp_value(value unit); /* ML */
#endif /* _COQ_MEMORY_ */


value coq_set_drawinstr(value unit);
