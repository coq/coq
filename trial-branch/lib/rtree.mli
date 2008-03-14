(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(* Type of regular tree with nodes labelled by values of type 'a *)

type 'a t 

(* Building trees *)
(* build a recursive call *) 
val mk_param : int -> 'a t
(* build a node given a label and the vector of sons *)
val mk_node  : 'a -> 'a t array -> 'a t
(* build mutually dependent trees *)
val mk_rec   : 'a t array -> 'a t array

(* [lift k t] increases of [k] the free parameters of [t]. Needed
   to avoid captures when a tree appears under [mk_rec] *) 
val lift : int -> 'a t -> 'a t

val map : ('a -> 'b) -> 'a t -> 'b t

(* [(smartmap f t) == t] if [(f a) ==a ] for all nodes *)
val smartmap : ('a -> 'a) -> 'a t -> 'a t

(* Destructors (recursive calls are expanded) *)
val dest_param : 'a t -> int
val dest_node  : 'a t -> 'a * 'a t array

(* Tells if a tree has an infinite branch *)
val is_infinite : 'a t -> bool

(* A rather simple minded pretty-printer *)
val pp_tree : ('a -> Pp.std_ppcmds) -> 'a t -> Pp.std_ppcmds
