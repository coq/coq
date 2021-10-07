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

#include <caml/alloc.h>
#include <caml/mlvalues.h>

#include <float.h>

#define Default_tag 0

#define ATOM_ID_TAG 0
#define ATOM_INDUCTIVE_TAG 1
#define ATOM_TYPE_TAG 2
#define ATOM_PROJ_TAG 3
#define ATOM_FIX_TAG 4
#define ATOM_SWITCH_TAG 5
#define ATOM_COFIX_TAG 6
#define ATOM_COFIXEVALUATED_TAG 7

#define Is_double(v) (Tag_val(v) == Double_tag)
#define Is_tailrec_switch(v) (Field(v,1) == Val_true)

/* coq values for primitive operations */
#define coq_tag_C1 2
#define coq_tag_C0 1
#define coq_tag_pair 1
#define coq_true Val_int(0)
#define coq_false Val_int(1)
#define coq_Eq Val_int(0)
#define coq_Lt Val_int(1)
#define coq_Gt Val_int(2)
#define coq_FEq Val_int(0)
#define coq_FLt Val_int(1)
#define coq_FGt Val_int(2)
#define coq_FNotComparable Val_int(3)
#define coq_PNormal Val_int(0)
#define coq_NNormal Val_int(1)
#define coq_PSubn Val_int(2)
#define coq_NSubn Val_int(3)
#define coq_PZero Val_int(4)
#define coq_NZero Val_int(5)
#define coq_PInf Val_int(6)
#define coq_NInf Val_int(7)
#define coq_NaN Val_int(8)

#define FLOAT_EXP_SHIFT (2101) /* 2*emax + prec */

#endif /* _COQ_VALUES_ */
