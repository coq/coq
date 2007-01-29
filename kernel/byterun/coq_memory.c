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
#include <string.h> 
#include "coq_gc.h"
#include "coq_instruct.h"
#include "coq_fix_code.h"
#include "coq_memory.h"
#include "coq_interp.h"

/* stack */

value * coq_stack_low;
value * coq_stack_high;
value * coq_stack_threshold;
asize_t coq_max_stack_size = Coq_max_stack_size;
/* global_data */


value coq_global_data;
value coq_global_boxed;
int coq_all_transp;
value coq_atom_tbl;

int drawinstr;
/* interp state */

long coq_saved_sp_offset;
value * coq_sp;
/* Some predefined pointer code */ 
code_t accumulate;

/* functions over global environment */

void coq_stat_free (void * blk)
{
  free (blk);
}

value coq_static_alloc(value size) /* ML */
{
  return (value) coq_stat_alloc((asize_t) Long_val(size));
}

value coq_static_free(value blk)  /* ML */
{
  coq_stat_free((void *) blk);
  return Val_unit;
}

value accumulate_code(value unit) /* ML */
{
  return (value) accumulate;
}

static void (*coq_prev_scan_roots_hook) (scanning_action);

static void coq_scan_roots(scanning_action action)
{
  register value * i;
  /* Scan the global variables */
  (*action)(coq_global_data, &coq_global_data);
  (*action)(coq_global_boxed, &coq_global_boxed);
  (*action)(coq_atom_tbl, &coq_atom_tbl);
  /* Scan the stack */
  for (i = coq_sp; i < coq_stack_high; i++) {
    (*action) (*i, i);
  };
  /* Hook */
  if (coq_prev_scan_roots_hook != NULL) (*coq_prev_scan_roots_hook)(action);


}

void init_coq_stack()
{
  coq_stack_low = (value *) coq_stat_alloc(Coq_stack_size);
  coq_stack_high = coq_stack_low + Coq_stack_size / sizeof (value);
  coq_stack_threshold = coq_stack_low + Coq_stack_threshold / sizeof(value);
  coq_max_stack_size = Coq_max_stack_size;
}  

void init_coq_global_data(long requested_size)
{
  int i;
  coq_global_data = alloc_shr(requested_size, 0);
  for (i = 0; i < requested_size; i++) 
    Field (coq_global_data, i) = Val_unit;
}

void init_coq_global_boxed(long requested_size)
{
  int i;
  coq_global_boxed = alloc_shr(requested_size, 0);
  for (i = 0; i < requested_size; i++) 
    Field (coq_global_boxed, i) = Val_true;
}

void init_coq_atom_tbl(long requested_size){
  int i;
  coq_atom_tbl = alloc_shr(requested_size, 0);
  for (i = 0; i < requested_size; i++) Field (coq_atom_tbl, i) = Val_unit;
}

void init_coq_interpreter()
{
  coq_sp = coq_stack_high;
  coq_interprete(NULL, Val_unit, Val_unit, 0);
}

static int coq_vm_initialized = 0;

value init_coq_vm(value unit) /* ML */
{
  int i;
  if (coq_vm_initialized == 1) {
    fprintf(stderr,"already open \n");fflush(stderr);}
  else {
    drawinstr=0;
#ifdef THREADED_CODE   
    init_arity();
#endif /* THREADED_CODE */
    /* Allocate the table of global and the stack */
    init_coq_stack();
    init_coq_global_data(Coq_global_data_Size);
    init_coq_global_boxed(40);
    init_coq_atom_tbl(40);
    /* Initialing the interpreter */
    coq_all_transp = 0;
    init_coq_interpreter();
    
    /* Some predefined pointer code */
    accumulate = (code_t) coq_stat_alloc(sizeof(opcode_t));
    *accumulate = VALINSTR(ACCUMULATE);

  /* Initialize GC */
    if (coq_prev_scan_roots_hook == NULL)
      coq_prev_scan_roots_hook = scan_roots_hook;
    scan_roots_hook = coq_scan_roots;
    coq_vm_initialized = 1;
  } 
  return Val_unit;;
}

void realloc_coq_stack(asize_t required_space)
{
  asize_t size;
  value * new_low, * new_high, * new_sp;
  value * p;
  size = coq_stack_high - coq_stack_low;
  do {
    size *= 2;
  } while (size < coq_stack_high - coq_sp + required_space);
  new_low = (value *) coq_stat_alloc(size * sizeof(value));
  new_high = new_low + size;

#define shift(ptr) \
    ((char *) new_high - ((char *) coq_stack_high - (char *) (ptr)))

  new_sp = (value *) shift(coq_sp);
  memmove((char *) new_sp,
        (char *) coq_sp,
        (coq_stack_high - coq_sp) * sizeof(value));
  coq_stat_free(coq_stack_low);
  coq_stack_low = new_low;
  coq_stack_high = new_high;
  coq_stack_threshold = coq_stack_low + Coq_stack_threshold / sizeof(value);
  coq_sp = new_sp;
#undef shift
}

value get_coq_global_data(value unit)                /* ML */
{
  return coq_global_data;
}

value get_coq_atom_tbl(value unit)                  /* ML */
{
  return coq_atom_tbl;
}

value get_coq_global_boxed(value unit)        /* ML */
{
  return coq_global_boxed;
}

value realloc_coq_global_data(value size)           /* ML */
{
  mlsize_t requested_size, actual_size, i;
  value new_global_data;
  requested_size = Long_val(size);
  actual_size = Wosize_val(coq_global_data);
  if (requested_size >= actual_size) {
    requested_size = (requested_size + 0x100) & 0xFFFFFF00;
    new_global_data = alloc_shr(requested_size, 0);
    for (i = 0; i < actual_size; i++)
      initialize(&Field(new_global_data, i), Field(coq_global_data, i));
    for (i = actual_size; i < requested_size; i++){
      Field (new_global_data, i) = Val_long (0);
    }
    coq_global_data = new_global_data;
  }
  return Val_unit;
}

value realloc_coq_global_boxed(value size)           /* ML */
{
  mlsize_t requested_size, actual_size, i;
  value new_global_boxed;
  requested_size = Long_val(size);
  actual_size = Wosize_val(coq_global_boxed);
  if (requested_size >= actual_size) {
    requested_size = (requested_size + 0x100) & 0xFFFFFF00;
    new_global_boxed = alloc_shr(requested_size, 0);
    for (i = 0; i < actual_size; i++)
      initialize(&Field(new_global_boxed, i), Field(coq_global_boxed, i));
    for (i = actual_size; i < requested_size; i++)
      Field (new_global_boxed, i) = Val_long (0);
    coq_global_boxed = new_global_boxed;
  }
  return Val_unit;
}

value realloc_coq_atom_tbl(value size)            /* ML */
{
  mlsize_t requested_size, actual_size, i;
  value new_atom_tbl;
  requested_size = Long_val(size);
  actual_size = Wosize_val(coq_atom_tbl);
  if (requested_size >= actual_size) {
    requested_size = (requested_size + 0x100) & 0xFFFFFF00;
    new_atom_tbl = alloc_shr(requested_size, 0);
    for (i = 0; i < actual_size; i++)
      initialize(&Field(new_atom_tbl, i), Field(coq_atom_tbl, i));
    for (i = actual_size; i < requested_size; i++)
      Field (new_atom_tbl, i) = Val_long (0);
    coq_atom_tbl = new_atom_tbl;
  }
  return Val_unit;
}


value coq_set_transp_value(value transp)
{
  coq_all_transp = (transp == Val_true);
  return Val_unit;
}

value get_coq_transp_value(value unit)
{
  return Val_bool(coq_all_transp);
}

value coq_set_drawinstr(value unit)
{
  drawinstr = 1;
  return Val_unit;
}

