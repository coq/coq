(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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

(** Tells if a tree has an infinite branch *)
val is_infinite : 'a t -> bool

(** [compare_rtree f t1 t2] compares t1 t2 (top-down).
   f is called on each node: if the result is negative then the
   traversal ends on false, it is is positive then deeper nodes are
   not examined, and the traversal continues on respective siblings,
   and if it is 0, then the traversal continues on sons, pairwise.
   In this latter case, if the nodes do not have the same number of
   sons, then the traversal ends on false.
   In case of loop, the traversal is successful and it resumes on
   siblings.
 *)
val compare_rtree : ('a t -> 'b t -> int) -> 'a t -> 'b t -> bool

val eq_rtree : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

(** Iterators *)

val map : ('a -> 'b) -> 'a t -> 'b t

(** [(smartmap f t) == t] if [(f a) ==a ] for all nodes *)
val smartmap : ('a -> 'a) -> 'a t -> 'a t
val fold : (bool -> 'a t -> ('a t -> 'b) -> 'b) -> 'a t -> 'b
val fold2 :
  (bool -> 'a t -> 'b -> ('a t -> 'b -> 'c) -> 'c) -> 'a t -> 'b -> 'c

(** A rather simple minded pretty-printer *)
val pp_tree : ('a -> Pp.std_ppcmds) -> 'a t -> Pp.std_ppcmds
