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
#define Coq_stack_threshold (256 * sizeof(value))  /* see kernel/cbytegen.ml */
#define Coq_max_stack_size (256 * 1024)

#define TRANSP 0
#define BOXED 1

/* stack */

extern value * coq_stack_low;
extern value * coq_stack_high;
extern value * coq_stack_threshold;

/* global_data */

extern int coq_all_transp;

/* interp state */

extern value * coq_sp;

/* functions over global environment */

value coq_static_alloc(value size);  /* ML */

value init_coq_vm(value unit); /* ML */

void  realloc_coq_stack(asize_t required_space);

#endif /* _COQ_MEMORY_ */
