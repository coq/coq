(***************************************************************************

Innermost strategies

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Gen_terms;;
open Substitution;;

(*

  [(innermost_normalize sign red t)] returns the innermost normal
form of [t] w.r.t to the reduction relation [red].

  [red] is a function which, given a term [t], returns a pair
  [(u,sigma)] such that [t] rewrites to [u sigma], or raises
  [Irreducible] if [t] is irreducible.

  The substitution will be applied during the normalization process.

*)


val innermost_normalize : 
  'symbol #Signatures.signature ->
    ('symbol term -> 'symbol term * 'symbol substitution) -> 
      'symbol term -> 'symbol term ;;

(*

  [(force_innermost_normalize red t)] does the same as
  [(innermost_normalize red t)], but raises [Irreducible] if no
  reduction at all is possible.

*)

exception Irreducible;;

val force_innermost_normalize : 
  'symbol #Signatures.signature ->
  ('symbol term -> 'symbol term * 'symbol substitution) -> 
    'symbol term -> 'symbol term ;;

(* [safe_innermost_normalize sign n red t] does the same but where [n]
is a bound for the number of rewrite steps to apply. If this bound is
reached, then this function raises the exception [Unnormalized u]
where [u] is the reduct of [t] obtained so far *)


exception Unnormalized;;

val safe_innermost_normalize : 
  'symbol #Signatures.signature ->
    int -> 
      ('symbol term -> 'symbol term * 'symbol substitution) -> 
	'symbol term -> 'symbol term ;;

val safe_force_innermost_normalize : 
  'symbol #Signatures.signature ->
    int -> 
      ('symbol term -> 'symbol term * 'symbol substitution) -> 
	'symbol term -> 'symbol term ;;


