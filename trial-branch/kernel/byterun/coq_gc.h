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
#include <mlvalues.h>
#include <alloc.h>

typedef void (*scanning_action) (value, value *);


CAMLextern char *young_ptr;
CAMLextern char *young_limit;
CAMLextern void (*scan_roots_hook) (scanning_action);
CAMLextern void minor_collection (void);

#define Caml_white (0 << 8)
#define Caml_black (3 << 8)

#define Make_header(wosize, tag, color)                                 \
  (((header_t) (((header_t) (wosize) << 10)                             \
		+ (color)                                               \
		+ (tag_t) (tag)))   					\
   )


#define Alloc_small(result, wosize, tag) do{                            \
  young_ptr -= Bhsize_wosize (wosize);                                  \
  if (young_ptr < young_limit){                                         \
    young_ptr += Bhsize_wosize (wosize);                                \
    Setup_for_gc;                                                       \
    minor_collection ();                                                \
    Restore_after_gc;                                                   \
    young_ptr -= Bhsize_wosize (wosize);                                \
  }                                                                     \
  Hd_hp (young_ptr) = Make_header ((wosize), (tag), Caml_black);        \
  (result) = Val_hp (young_ptr);                                        \
  }while(0) 


#endif /*_COQ_CAML_GC_ */
