(***************************************************************************

  Unification modulo an associative and commutative symbol.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Variables
open Gen_terms
open Theory
open Problems

(*

  [solve elem_pb] computes a unifier for [elem_pb] modulo the
  associativity-commutativity, that is, solves the equations of the
  problem and checks that the constraints of marks are satisfied.

*)

  val solve :
    Theory.unif_kind ->
    Variables.var_id Variables.VarSet.t ->
    'a Problems.elem_pb -> ('a Gen_terms.term * 'a Gen_terms.term) list list

val solve :
  unif_kind -> var_id VarSet.t -> 'symbol elem_pb -> ('symbol term * 'symbol term) list list


