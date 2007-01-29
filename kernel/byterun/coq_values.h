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

#include <alloc.h>
#include <mlvalues.h>

#define Default_tag 0
#define Accu_tag 0



#define ATOM_ID_TAG 0
#define ATOM_IDDEF_TAG 1
#define ATOM_INDUCTIVE_TAG 2
#define ATOM_FIX_TAG 3
#define ATOM_SWITCH_TAG 4
#define ATOM_COFIX_TAG 5
#define ATOM_COFIXEVALUATED_TAG 6



/* Les blocs accumulate */
#define Is_accu(v) (Is_block(v) && (Tag_val(v) == Accu_tag))

#define IS_EVALUATED_COFIX(v) (Is_accu(v) && Is_block(Field(v,1)) && (Tag_val(Field(v,1)) == ATOM_COFIXEVALUATED_TAG))
#endif /* _COQ_VALUES_ */


