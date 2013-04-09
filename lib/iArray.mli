(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

type +'a t
(** Immutable arrays containing elements of type ['a]. *)

(** {5 Operations inherited from [Array]}

  Refer to the documentation of [CArray] for greater detail.

*)

val length : 'a t -> int
val make : int -> 'a -> 'a t
val init : int -> (int -> 'a) -> 'a t
val append : 'a t -> 'a t -> 'a t
val concat : 'a t list -> 'a t
val sub : 'a t -> int -> int -> 'a t
val of_list : 'a list -> 'a t
val to_list : 'a t -> 'a list
val iter : ('a -> unit) -> 'a t -> unit
val iteri : (int -> 'a -> unit) -> 'a t -> unit
val map : ('a -> 'b) -> 'a t -> 'b t
val mapi : (int -> 'a -> 'b) -> 'a t -> 'b t
val fold_right : ('a -> 'b -> 'b) -> 'b -> 'a t -> 'b
val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a

(** {5 Unsafe operations} *)

module Unsafe :
sig
  val get : 'a t -> int -> 'a
  (** Get a value, does not do bound checking. *)

  val of_array : 'a array -> 'a t
  (** Cast a mutable array into an immutable one. Essentially identity. *)

  val to_array : 'a t -> 'a array
  (** Cast an immutable array into a mutable one. Essentially identity. *)
end
(** Unsafe operations. Use with caution! *)
