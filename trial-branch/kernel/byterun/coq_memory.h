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

#include <config.h>
#include <fail.h>
#include <misc.h>
#include <memory.h>
#include <mlvalues.h>


#define Coq_stack_size (4096 * sizeof(value))
#define Coq_stack_threshold (256 * sizeof(value))
#define Coq_global_data_Size (4096 * sizeof(value))
#define Coq_max_stack_size (256 * 1024)

#define TRANSP 0
#define BOXED 1

/* stack */

extern value * coq_stack_low;
extern value * coq_stack_high;
extern value * coq_stack_threshold;

/* global_data */

extern value coq_global_data;
extern value coq_global_boxed;
extern int coq_all_transp;
extern value coq_atom_tbl;

extern int drawinstr;
/* interp state */

extern value * coq_sp;
/* Some predefined pointer code */ 
extern code_t accumulate;

/* functions over global environment */

value coq_static_alloc(value size);  /* ML */
value coq_static_free(value string); /* ML */

value init_coq_vm(value unit); /* ML */
value re_init_coq_vm(value unit); /* ML */

void  realloc_coq_stack(asize_t required_space); 
value get_coq_global_data(value unit); /* ML */
value realloc_coq_global_data(value size); /* ML */
value get_coq_global_boxed(value unit);
value realloc_coq_global_boxed(value size); /* ML */
value get_coq_atom_tbl(value unit); /* ML */
value realloc_coq_atom_tbl(value size); /* ML */
value coq_set_transp_value(value transp); /* ML */
value get_coq_transp_value(value unit); /* ML */
#endif /* _COQ_MEMORY_ */


value coq_set_drawinstr(value unit);
