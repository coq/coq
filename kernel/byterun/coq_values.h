/***********************************************************************/
/*                                                                     */
/*                           Coq Compiler                              */
/*                                                                     */
/*        Benjamin Gregoire, projets Logical and Cristal               */
/*                        INRIA Rocquencourt                           */
/*                                                                     */
/*                                                                     */
/***********************************************************************/

#ifndef _COQ_VALUES_
#define _COQ_VALUES_

#include "alloc.h"
#include "mlvalues.h"

#define ATOM_FIX_TAG 3
#define ATOM_SWITCH_TAG 4

#define Accu_tag 0
#define Default_tag 0

/* Les blocs accumulate */
#define Is_accu(v) (Is_block(v) && (Tag_val(v) == Accu_tag))

#endif /* _COQ_VALUES_ */


