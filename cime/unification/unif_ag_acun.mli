(***************************************************************************

  Unification modulo AG, the Abelian Groups theory and modulo ACUN, a
  theory with a unit and an associative, commutative and nilpotent
  symbol of order $n$.

CiME Project - D�mons research team - LRI - Universit� Paris XI

$Id$

***************************************************************************)

open Variables
open Gen_terms
open Theory
open Problems

val solve : 
  unif_kind -> var_id VarSet.t -> 'symbol elem_pb -> 
    ('symbol term * 'symbol term) list list
