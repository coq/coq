/***********************************************************************/
/*                                                                     */
/*                          Rocq Compiler                              */
/*                                                                     */
/*        Benjamin Gregoire, projets Logical and Cristal               */
/*                        INRIA Rocquencourt                           */
/*                                                                     */
/*                                                                     */
/***********************************************************************/

#include <stdio.h>
#include <string.h>

#define CAML_INTERNALS
#include <caml/alloc.h>
#include <caml/address_class.h>
#include <caml/roots.h>
#include <caml/version.h>

#if OCAML_VERSION >= 50000
#include <caml/shared_heap.h>
#endif

#include "rocq_instruct.h"
#include "rocq_fix_code.h"
#include "rocq_memory.h"
#include "rocq_interp.h"

/* stack */

value * rocq_stack_low;
value * rocq_stack_high;
value * rocq_stack_threshold;
asize_t rocq_max_stack_size = Rocq_max_stack_size;

/* interp state */

long rocq_saved_sp_offset;
value * rocq_sp;

/* functions over global environment */

void rocq_stat_free (void * blk)
{
  free (blk);
}

value rocq_static_alloc(value size) /* ML */
{
  return (value) rocq_stat_alloc((asize_t) Long_val(size));
}

#if OCAML_VERSION < 50000
static void (*rocq_prev_scan_roots_hook) (scanning_action);

static void rocq_scan_roots(scanning_action action)
{
  register value * i;
  /* Scan the stack */
  for (i = rocq_sp; i < rocq_stack_high; i++) {
    if (!Is_block(*i)) continue;
    (*action) (*i, i);
  };
  /* Hook */
  if (rocq_prev_scan_roots_hook != NULL) (*rocq_prev_scan_roots_hook)(action);
}
#else
static void (*rocq_prev_scan_roots_hook) (scanning_action, scanning_action_flags, void *, caml_domain_state *);

static void rocq_scan_roots(scanning_action action, scanning_action_flags flags, void *ctx, caml_domain_state *state)
{
  register value * i;
  /* Scan the stack */
  for (i = rocq_sp; i < rocq_stack_high; i++) {
    if (!Is_block(*i)) continue;
    (*action) (ctx, *i, i);
  };
  /* Hook */
  if (rocq_prev_scan_roots_hook != NULL) (*rocq_prev_scan_roots_hook)(action, flags, ctx, state);
}
#endif

static int rocq_vm_initialized = 0;

value init_rocq_vm(value unit) /* ML */
{
  if (rocq_vm_initialized) {
    fprintf(stderr, "already open\n");
    fflush(stderr);
    return Val_unit;
  }

  /* Allocate the table of global and the stack */
  rocq_stack_low = (value *) rocq_stat_alloc(Rocq_stack_size);
  rocq_stack_high = rocq_stack_low + Rocq_stack_size / sizeof (value);
  rocq_stack_threshold = rocq_stack_low + Rocq_stack_threshold / sizeof(value);
  rocq_max_stack_size = Rocq_max_stack_size;

  /* Initialize the interpreter */
  rocq_sp = rocq_stack_high;
  rocq_interprete(NULL, Val_unit, Atom(0), Atom(0), Val_unit, 0);

  /* Initialize GC */
  if (rocq_prev_scan_roots_hook == NULL)
    rocq_prev_scan_roots_hook = caml_scan_roots_hook;
  caml_scan_roots_hook = rocq_scan_roots;
  rocq_vm_initialized = 1;

  return Val_unit;;
}

/* [required_space] is a size in words */
void realloc_rocq_stack(asize_t required_space)
{
  asize_t size;
  value * new_low, * new_high, * new_sp;
  size = rocq_stack_high - rocq_stack_low;
  do {
    size *= 2;
  } while (size < rocq_stack_high - rocq_sp + required_space);
  new_low = (value *) rocq_stat_alloc(size * sizeof(value));
  new_high = new_low + size;

#define shift(ptr) \
    ((char *) new_high - ((char *) rocq_stack_high - (char *) (ptr)))

  new_sp = (value *) shift(rocq_sp);
  memmove((char *) new_sp,
        (char *) rocq_sp,
        (rocq_stack_high - rocq_sp) * sizeof(value));
  rocq_stat_free(rocq_stack_low);
  rocq_stack_low = new_low;
  rocq_stack_high = new_high;
  rocq_stack_threshold = rocq_stack_low + Rocq_stack_threshold / sizeof(value);
  rocq_sp = new_sp;
#undef shift
}
