(***************************************************************************

This module allows to define orderings on finite sets.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

(*

  This module allows one to define ordering on finite sets of
  objects. The construction of such an ordering on a set $E$ is
  obtained by starting from the ``smallest'' ordering on $E$ (that is
  the relation $=$) and adding comparison pairs $x > y$ or $x=y$,
  performing the transitive closure at each step.

  Formally speaking, this allows to build ordering on infinite sets,
  but only if they differ from identity on finitely many pairs.

*)

exception Incompatible

module type Finite_ordering =
sig
  type elt
  type t
  val identity_ordering : t
  val compare : t -> elt Orderings_generalities.ordering
  val add_equiv : t -> elt -> elt -> t
  val add_greater : t -> elt -> elt -> t
end

module Make : functor (M : Map.OrderedType)
  -> Finite_ordering with type elt = M.t

(*

  [(identity_ordering comp)] builds an identity ordering object on a
  given data type [t]. [comp] is any total comparison function on [t]:
  [comp x y] is 0 if [x] and [y] are equal, negative if [x < y], and
  positive if [x > y]

*)


(*

  Building finite orderings from lists of comparisons.

  [(add_list o p)] adds all comparison in list [p] to [o]. [p] is a
 concrete type that represents a list of comparison. For example [ x >
 y = z < t ] is represented as [Gt(x,Eq(y,Lt(z,One(t))))]. On that
 example, it will do [add_greater x y], [add_equiv y z], and
 [add_greater t z], of course performing transitive closure at each
 step.

*)

(*
type 'a precedence =
    One of 'a
  | Gt of 'a * 'a precedence
  | Lt of 'a * 'a precedence
  | Eq of 'a * 'a precedence

val add_list : 'a finite_ordering -> 'a precedence -> unit;;

val map_prec : ('a -> 'b) -> 'a precedence -> 'b precedence;;
*)
