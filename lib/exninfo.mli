(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** Additional information worn by exceptions. *)

type 'a t
(** Information containing a given type. *)

val make : unit -> 'a t
(** Create a new piece of information. *)

val add : exn -> 'a t -> 'a -> exn
(** Add information to an exception. *)

val get : exn -> 'a t -> 'a option
(** Get information worn by an exception. Returns [None] if undefined. *)

(* val remove : exn -> 'a t -> exn *)
(** TODO: Remove a given piece of information. *)

val clear : exn -> exn
(** Remove any information. *)

val copy : exn -> exn -> exn
(** [copy src dst] adds the additional info from [src] to [dst]. *)
