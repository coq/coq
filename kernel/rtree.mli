(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Type of regular tree with nodes labelled by values of type 'a
   The implementation uses de Bruijn indices, so binding capture
   is avoided by the lift operator (see example below).

   Note that it differs from standard regular trees by accepting
   vectors of vectors in nodes, which is useful for encoding
   disjunctive-conjunctive recursive trees such as inductive types.
   Standard regular trees can however easily be simulated by using
   singletons of vectors *)
type 'a t

(** Building trees *)

(** Build a node given a label and a vector of vectors of sons *)
val mk_node  : 'a -> 'a t array array -> 'a t

(** Build mutually recursive trees:
    X_1 = f_1(X_1,..,X_n) ... X_n = f_n(X_1,..,X_n)
   is obtained by the following pseudo-code
   let vx = mk_rec_calls n in
   let [|x_1;..;x_n|] =
      mk_rec[|f_1(vx.(0),..,vx.(n-1);..;f_n(vx.(0),..,vx.(n-1))|]

  First example: build  rec X = a(X,Y) and Y = b(X,Y,Y)
  let [|vx;vy|] = mk_rec_calls 2 in
  let [|x;y|] = mk_rec [|mk_node a [|[|vx;vy|]|]; mk_node b [|[|vx;vy;vy|]|]|]

  Another example: nested recursive trees rec Y = b(rec X = a(X,Y),Y,Y)
  let [|vy|] = mk_rec_calls 1 in
  let [|vx|] = mk_rec_calls 1 in
  let [|x|] = mk_rec[|mk_node a [|[|vx;lift 1 vy|]|]|]
  let [|y|] = mk_rec[|mk_node b [|[|x;vy;vy|]|]|]
  (note the lift so that Y links to the "rec Y" skipping the "rec X")
 *)
val mk_rec_calls : int -> 'a t array
val mk_rec   : 'a t array -> 'a t array

(** [lift k t] increases of [k] the free parameters of [t]. Needed
   to avoid captures when a tree appears under [mk_rec] *)
val lift : int -> 'a t -> 'a t

val is_node : 'a t -> bool

(** Destructors (recursive calls are expanded) *)
val dest_node  : 'a t -> 'a * 'a t array array

(** First projection of {!dest_node} *)
val dest_head : 'a t -> 'a

(** dest_var is not needed for closed trees (i.e. with no free variable) *)
val dest_var : 'a t -> int * int

(** Tells if a tree has an infinite branch. The first arg is a comparison
    used to detect already seen elements, hence loops *)
val is_infinite : ('a -> 'a -> bool) -> 'a t -> bool

(** [Rtree.equiv eq eqlab t1 t2] compares t1 t2 (top-down).
   If t1 and t2 are both nodes, [eqlab] is called on their labels,
   in case of success deeper nodes are examined.
   In case of loop (detected via structural equality parametrized
   by [eq]), then the comparison is successful. *)
val equiv :
  ('a -> 'a -> bool) -> ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

(** [Rtree.equal eq t1 t2] compares t1 and t2, first via physical
    equality, then by structural equality (using [eq] on elements),
    then by logical equivalence [Rtree.equiv eq eq] *)
val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

val inter : ('a -> 'a -> bool) -> ('a -> 'a -> 'a option) -> 'a -> 'a t -> 'a t -> 'a t

val incl : ('a -> 'a -> bool) -> ('a -> 'a -> 'a option) -> 'a -> 'a t -> 'a t -> bool

(** Iterators *)

(** See also [Smart.map] *)
val map : ('a -> 'b) -> 'a t -> 'b t

(** Pretty-printer *)
val pr_tree : ('a -> Pp.t) -> 'a t -> Pp.t

module Smart :
sig

  (** [(Smart.map f t) == t] if [(f a) ==a ] for all nodes *)
  val map : ('a -> 'a) -> 'a t -> 'a t

end

module Kind :
sig

type 'a rtree = 'a t
type 'a t
type 'a kind = Var of int * int | Node of 'a * 'a t array array

val make : 'a rtree -> 'a t
val kind : 'a t -> 'a kind
val repr : 'a t -> 'a rtree

end
