(***************************************************************************

  This module provides a function for solving an elementary
  unification problem modulo an associative and commutative
  symbol. This function should only be called on a problem which is
  quasi-solved, that is all the equations are of the form 
  [variable = term] and the {\bf Merge} rule can apply.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

(*

Obsolete header:

  Remark : the general solver for an elementary unification problem
  modulo ACU is provided in the module [Unif_acu] by the function
  [solve].

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Variables
open Gen_terms
open Theory
open Problems

val solve : 
  unif_kind -> var_id VarSet.t -> 'symbol elem_pb -> 
    ('symbol term * 'symbol term) list list
