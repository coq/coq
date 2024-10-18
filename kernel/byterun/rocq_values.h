/***********************************************************************/
/*                                                                     */
/*                          Rocq Compiler                              */
/*                                                                     */
/*        Benjamin Gregoire, projets Logical and Cristal               */
/*                        INRIA Rocquencourt                           */
/*                                                                     */
/*                                                                     */
/***********************************************************************/

#ifndef _ROCQ_VALUES_
#define _ROCQ_VALUES_

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

/* rocq values for primitive operations */
#define rocq_tag_C1 2
#define rocq_tag_C0 1
#define rocq_tag_pair 1
#define rocq_true Val_int(0)
#define rocq_false Val_int(1)
#define rocq_Eq Val_int(0)
#define rocq_Lt Val_int(1)
#define rocq_Gt Val_int(2)
#define rocq_FEq Val_int(0)
#define rocq_FLt Val_int(1)
#define rocq_FGt Val_int(2)
#define rocq_FNotComparable Val_int(3)
#define rocq_PNormal Val_int(0)
#define rocq_NNormal Val_int(1)
#define rocq_PSubn Val_int(2)
#define rocq_NSubn Val_int(3)
#define rocq_PZero Val_int(4)
#define rocq_NZero Val_int(5)
#define rocq_PInf Val_int(6)
#define rocq_NInf Val_int(7)
#define rocq_NaN Val_int(8)

#define FLOAT_EXP_SHIFT (2101) /* 2*emax + prec */

#endif /* _ROCQ_VALUES_ */
