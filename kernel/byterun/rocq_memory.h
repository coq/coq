/***********************************************************************/
/*                                                                     */
/*                          Rocq Compiler                              */
/*                                                                     */
/*        Benjamin Gregoire, projets Logical and Cristal               */
/*                        INRIA Rocquencourt                           */
/*                                                                     */
/*                                                                     */
/***********************************************************************/

#ifndef _ROCQ_MEMORY_
#define _ROCQ_MEMORY_

#include <caml/config.h>
#include <caml/fail.h>
#include <caml/misc.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>


#define Rocq_stack_size (4096 * sizeof(value))
#define Rocq_stack_threshold (256 * sizeof(value))  /* see kernel/cbytegen.ml */
#define Rocq_max_stack_size (256 * 1024)

#define TRANSP 0
#define BOXED 1

/* stack */

extern value * rocq_stack_low;
extern value * rocq_stack_high;
extern value * rocq_stack_threshold;

/* global_data */

extern int rocq_all_transp;

/* interp state */

extern value * rocq_sp;

/* functions over global environment */

value rocq_static_alloc(value size);  /* ML */

value init_rocq_vm(value unit); /* ML */

void  realloc_rocq_stack(asize_t required_space);

#endif /* _ROCQ_MEMORY_ */
