(***************************************************************************

  Unification in the free theory.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Variables
open Gen_terms
open Problems

type 'symbol pure_elem_pb =
    {
      map_of_var_var : (unit, var_id) VarMap.t;
      scanned_equations : ('symbol term * 'symbol term) list;
      other_equations : ('symbol term * 'symbol term) list
    }

(* 

   Deletion of trivial equations.  

*)

val delete : 'symbol pure_elem_pb -> 'symbol pure_elem_pb


(*

  Coalesce (Replacement of a variable by a variable).

*)

val coalesce : 'symbol pure_elem_pb -> 'symbol pure_elem_pb


(*

  Merge for two equations with the same variable left-hand side.

*)

val merge :
  'symbol #Signatures.signature ->
    'symbol pure_elem_pb -> 'symbol pure_elem_pb


(*

  [solve_without_marks sign list_of_equations] computes a unifier
  for [list_of_equations] modulo the empty equational theory.

*)



val solve_without_marks :
  'symbol #Signatures.signature -> (*i Variables.user_variables -> i*)
    ('symbol term * 'symbol term) list ->
      ('symbol term * 'symbol term) list



(*

  [solve sign elem_pb] computes a unifier for [elem_pb] modulo the
  empty equational theory, that is, solves the equations of the
  problem and checks that the constraints of marks are satisfied.

*)

val solve :
  'symbol #Signatures.signature -> (*i Variables.user_variables -> i*)
    'symbol elem_pb ->
    ('symbol term * 'symbol term) list list




