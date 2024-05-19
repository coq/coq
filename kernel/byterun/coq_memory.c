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

#define CAML_INTERNALS
#include <caml/address_class.h>
#include <caml/alloc.h>
#include <caml/roots.h>
#include <caml/version.h>

#if OCAML_VERSION >= 50000
#include <caml/shared_heap.h>
#endif

#include "coq_fix_code.h"
#include "coq_instruct.h"
#include "coq_interp.h"
#include "coq_memory.h"

/* stack */

value *coq_stack_low;
value *coq_stack_high;
value *coq_stack_threshold;
asize_t coq_max_stack_size = Coq_max_stack_size;

/* interp state */

long coq_saved_sp_offset;
value *coq_sp;

/* functions over global environment */

void coq_stat_free(void *blk) { free(blk); }

value coq_static_alloc(value size) /* ML */
{
  return (value)coq_stat_alloc((asize_t)Long_val(size));
}

#if OCAML_VERSION < 50000
static void (*coq_prev_scan_roots_hook)(scanning_action);

static void coq_scan_roots(scanning_action action) {
  register value *i;
  /* Scan the stack */
  for (i = coq_sp; i < coq_stack_high; i++) {
    if (!Is_block(*i))
      continue;
    (*action)(*i, i);
  };
  /* Hook */
  if (coq_prev_scan_roots_hook != NULL)
    (*coq_prev_scan_roots_hook)(action);
}
#else
static void (*coq_prev_scan_roots_hook)(scanning_action, scanning_action_flags,
                                        void *, caml_domain_state *);

static void coq_scan_roots(scanning_action action, scanning_action_flags flags,
                           void *ctx, caml_domain_state *state) {
  register value *i;
  /* Scan the stack */
  for (i = coq_sp; i < coq_stack_high; i++) {
    if (!Is_block(*i))
      continue;
    (*action)(ctx, *i, i);
  };
  /* Hook */
  if (coq_prev_scan_roots_hook != NULL)
    (*coq_prev_scan_roots_hook)(action, flags, ctx, state);
}
#endif

static int coq_vm_initialized = 0;

value init_coq_vm(value unit) /* ML */
{
  if (coq_vm_initialized) {
    fprintf(stderr, "already open\n");
    fflush(stderr);
    return Val_unit;
  }

  /* Allocate the table of global and the stack */
  coq_stack_low = (value *)coq_stat_alloc(Coq_stack_size);
  coq_stack_high = coq_stack_low + Coq_stack_size / sizeof(value);
  coq_stack_threshold = coq_stack_low + Coq_stack_threshold / sizeof(value);
  coq_max_stack_size = Coq_max_stack_size;

  /* Initialize the interpreter */
  coq_sp = coq_stack_high;
  coq_interprete(NULL, Val_unit, Atom(0), Atom(0), Val_unit, 0);

  /* Initialize GC */
  if (coq_prev_scan_roots_hook == NULL)
    coq_prev_scan_roots_hook = caml_scan_roots_hook;
  caml_scan_roots_hook = coq_scan_roots;
  coq_vm_initialized = 1;

  return Val_unit;
  ;
}

/* [required_space] is a size in words */
void realloc_coq_stack(asize_t required_space) {
  asize_t size;
  value *new_low, *new_high, *new_sp;
  size = coq_stack_high - coq_stack_low;
  do {
    size *= 2;
  } while (size < coq_stack_high - coq_sp + required_space);
  new_low = (value *)coq_stat_alloc(size * sizeof(value));
  new_high = new_low + size;

#define shift(ptr) ((char *)new_high - ((char *)coq_stack_high - (char *)(ptr)))

  new_sp = (value *)shift(coq_sp);
  memmove((char *)new_sp, (char *)coq_sp,
          (coq_stack_high - coq_sp) * sizeof(value));
  coq_stat_free(coq_stack_low);
  coq_stack_low = new_low;
  coq_stack_high = new_high;
  coq_stack_threshold = coq_stack_low + Coq_stack_threshold / sizeof(value);
  coq_sp = new_sp;
#undef shift
}
