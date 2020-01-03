/***********************************************************************/
/*                                                                     */
/*                           Coq Compiler                              */
/*                                                                     */
/*        Benjamin Gregoire, projets Logical and Cristal               */
/*                        INRIA Rocquencourt                           */
/*                                                                     */
/*                                                                     */
/***********************************************************************/

#ifndef _COQ_CAML_GC_
#define _COQ_CAML_GC_
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/version.h>

typedef void (*scanning_action) (value, value *);


#if OCAML_VERSION < 41000
CAMLextern char *young_ptr;
CAMLextern char *young_limit;
#endif
CAMLextern void (*scan_roots_hook) (scanning_action);
CAMLextern void minor_collection (void);

#define Caml_white (0 << 8)
#define Caml_black (3 << 8)

#ifdef HAS_OCP_MEMPROF

/*  This code is necessary to make the OCamlPro memory profiling branch of
    OCaml compile. */

#define Make_header(wosize, tag, color)                                 \
  caml_make_header(wosize, tag, color)

#else

#define Make_header(wosize, tag, color)                                 \
  (((header_t) (((header_t) (wosize) << 10)                             \
		+ (color)                                               \
		+ (tag_t) (tag)))   					\
   )
#endif

#define Alloc_small(result, wosize, tag) do{                            \
  caml_young_ptr -= Bhsize_wosize (wosize);                             \
  if (caml_young_ptr < caml_young_limit){                               \
    caml_young_ptr += Bhsize_wosize (wosize);                           \
    Setup_for_gc;                                                       \
    minor_collection ();                                                \
    Restore_after_gc;                                                   \
    caml_young_ptr -= Bhsize_wosize (wosize);                           \
  }                                                                     \
  Hd_hp (caml_young_ptr) = Make_header ((wosize), (tag), Caml_black);   \
  (result) = Val_hp (caml_young_ptr);                                   \
  }while(0) 


#endif /*_COQ_CAML_GC_ */
