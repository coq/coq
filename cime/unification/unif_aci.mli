(***************************************************************************

  Unification modulo an associative, commutative and idempotent symbol.

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


