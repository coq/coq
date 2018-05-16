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
#include <caml/alloc.h>
#include <caml/address_class.h>
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

value accumulate_code(value unit) /* ML */
{
  CAMLparam1(unit);
  CAMLlocal1(res);
  res = caml_alloc_small(1, Abstract_tag);
  Code_val(res) = accumulate;
  CAMLreturn(res);
}

static void (*coq_prev_scan_roots_hook) (scanning_action);

static void coq_scan_roots(scanning_action action)
{
  register value * i;
  /* Scan the stack */
  for (i = coq_sp; i < coq_stack_high; i++) {
#ifdef NO_NAKED_POINTERS
    /* The VM stack may contain C-allocated bytecode */
    if (Is_block(*i) && !Is_in_heap_or_young(*i)) continue;
#endif
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

void init_coq_interpreter()
{
  coq_sp = coq_stack_high;
  coq_interprete(NULL, Val_unit, Atom(0), Atom(0), Val_unit, 0);
}

static int coq_vm_initialized = 0;

value init_coq_vm(value unit) /* ML */
{
  if (coq_vm_initialized == 1) {
    fprintf(stderr,"already open \n");fflush(stderr);}
  else {
    drawinstr=0;
#ifdef THREADED_CODE   
    init_arity();
#endif /* THREADED_CODE */
    /* Allocate the table of global and the stack */
    init_coq_stack();
    /* Initialing the interpreter */
    init_coq_interpreter();
    
    /* Some predefined pointer code.
     * It is typically contained in accumlator blocks whose tag is 0 and thus
     * scanned by the GC, so make it look like an OCaml block. */
    value accu_block = (value) coq_stat_alloc(2 * sizeof(value));
    Hd_hp (accu_block) = Make_header (1, Abstract_tag, Caml_black);        \
    accumulate = (code_t) Val_hp(accu_block);
    *accumulate = VALINSTR(ACCUMULATE);

  /* Initialize GC */
    if (coq_prev_scan_roots_hook == NULL)
      coq_prev_scan_roots_hook = scan_roots_hook;
    scan_roots_hook = coq_scan_roots;
    coq_vm_initialized = 1;
  } 
  return Val_unit;;
}

/* [required_space] is a size in words */
void realloc_coq_stack(asize_t required_space)
{
  asize_t size;
  value * new_low, * new_high, * new_sp;
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

value coq_set_drawinstr(value unit)
{
  drawinstr = 1;
  return Val_unit;
}

