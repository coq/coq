(***************************************************************************

  Unification modulo a commutative symbol.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Gen_terms
open Problems

(*i

val solve_without_marks :
  'symbol #Signatures.signature -> ('symbol term * 'symbol term) list ->
    ('symbol term * 'symbol term) list list

i*)

(*

  [solve sign elem_pb] computes a unifier for [elem_pb] modulo the
  commutativity, that is, solves the equations of the problem and
  checks that the constraints of marks are satisfied.

*)

val solve :
  'symbol #Signatures.signature -> (*i Variables.user_variables -> i*)
    'symbol elem_pb -> ('symbol term * 'symbol term) list list




