(***************************************************************************

  Unification modulo an associative and commutative symbol with a unit.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Variables
open Gen_terms
open Theory
open Problems

(*i
val vect_var_debut : int -> var_id array -> int array
;;
val iengendrer_vect_car : int array array * int array array -> int -> int -> int array -> int array list
;;
i*)

val generate_vect_char :
  unif_kind -> int -> int -> (unit, int) VarMap.t -> int array array -> 
    int array array -> int array list

val filter_non_unit_vars :
  'a VarSet.t -> int -> (unit, int) VarMap.t -> (unit, int) VarMap.t

val solve : 
  unif_kind -> var_id VarSet.t -> 'symbol elem_pb -> 
    ('symbol term * 'symbol term) list list

val is_ac_unifiable : var_id VarSet.t -> 'symbol elem_pb -> bool

