(***************************************************************************

  This module provides a function for solving an elementary
  unification problem modulo an associative and commutative
  symbol. This function should only be called on a problem which is
  solved except that the marked variables may be instanciated.

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


(*

  [(solve unif_k non_unit_variables elem_pb)] should be called only
  when the status of [elem_pb] is [Marked]. [non_unit_variables] is a
  set of variables which cannot be instanciated by the unit of the ACU
  theory. [(solve unif_k non_unit_variables elem_pb)] returns a list
  of solutions, each solution being given by a list of equations.

*)

val solve : 
  unif_kind -> (*i 'symbol Signatures.signature ->
    Variables.user_variables -> i*) var_id VarSet.t -> 'symbol elem_pb -> 
    ('symbol term * 'symbol term) list list
