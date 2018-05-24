(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Type of regular tree with nodes labelled by values of type 'a
   The implementation uses de Bruijn indices, so binding capture
   is avoided by the lift operator (see example below) *)
type 'a t

(** Building trees *)

(** build a node given a label and the vector of sons *)
val mk_node  : 'a -> 'a t array -> 'a t

(** Build mutually recursive trees:
    X_1 = f_1(X_1,..,X_n) ... X_n = f_n(X_1,..,X_n)
   is obtained by the following pseudo-code
   let vx = mk_rec_calls n in
   let [|x_1;..;x_n|] =
      mk_rec[|f_1(vx.(0),..,vx.(n-1);..;f_n(vx.(0),..,vx.(n-1))|]

  First example: build  rec X = a(X,Y) and Y = b(X,Y,Y)
  let [|vx;vy|] = mk_rec_calls 2 in
  let [|x;y|] = mk_rec [|mk_node a [|vx;vy|]; mk_node b [|vx;vy;vy|]|]

  Another example: nested recursive trees rec Y = b(rec X = a(X,Y),Y,Y)
  let [|vy|] = mk_rec_calls 1 in
  let [|vx|] = mk_rec_calls 1 in
  let [|x|] = mk_rec[|mk_node a vx;lift 1 vy|]
  let [|y|] = mk_rec[|mk_node b x;vy;vy|]
  (note the lift to avoid
 *)
val mk_rec_calls : int -> 'a t array
val mk_rec   : 'a t array -> 'a t array

(** [lift k t] increases of [k] the free parameters of [t]. Needed
   to avoid captures when a tree appears under [mk_rec] *)
val lift : int -> 'a t -> 'a t

val is_node : 'a t -> bool

(** Destructors (recursive calls are expanded) *)
val dest_node  : 'a t -> 'a * 'a t array

(** dest_param is not needed for closed trees (i.e. with no free variable) *)
val dest_param : 'a t -> int * int

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

val smartmap : ('a -> 'a) -> 'a t -> 'a t
(** @deprecated Same as [Smart.map] *)

(** A rather simple minded pretty-printer *)
val pp_tree : ('a -> Pp.t) -> 'a t -> Pp.t

val eq_rtree : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
(** @deprecated Same as [Rtree.equal] *)

module Smart :
sig

  (** [(Smart.map f t) == t] if [(f a) ==a ] for all nodes *)
  val map : ('a -> 'a) -> 'a t -> 'a t

end
