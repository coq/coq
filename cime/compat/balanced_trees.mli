(***************************************************************************

Balanced trees with one data info.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

(*

  data type of balanced tree with one info of type ['a]

*)

type 'a t = Empty | Node of 'a t * 'a * 'a t * int


val height : 'a t -> int

(* Creates a new node with left son l, value x and right son r.
   l and r must be balanced and | height l - height r | <= 2.
   Inline expansion of height for better speed. *)

val create : 'a t -> 'a -> 'a t -> 'a t

(* Same as create, but performs one step of rebalancing if necessary.
   Assumes l and r balanced.
   Inline expansion of create for better speed in the most frequent case
   where no rebalancing is required. *)

val bal : 'a t -> 'a -> 'a t -> 'a t

(* Same as bal, but repeat rebalancing until the final result
   is balanced. *)

val join : 'a t -> 'a -> 'a t -> 'a t


(* Merge two trees l and r into one.
   All elements of l must precede the elements of r.
   Assumes | height l - height r | <= 2. *)

val merge : 'a t -> 'a t -> 'a t


(* Same as merge, but does not assume anything about l and r. *)

val concat : 'a t -> 'a t -> 'a t




