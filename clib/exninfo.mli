(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Additional information worn by exceptions. *)

type 'a t
(** Information containing a given type. *)

type info
(** All information *)

type iexn = exn * info
(** Information-wearing exceptions *)

val make : unit -> 'a t
(** Create a new piece of information. *)

val null : info
(** No information *)

val add : info -> 'a t -> 'a -> info
(** Add information to an exception. *)

val get : info -> 'a t -> 'a option
(** Get information worn by an exception. Returns [None] if undefined. *)

val info : exn -> info
(** Retrieve the information of the last exception raised. *)

val iraise : iexn -> 'a
(** Raise the given enriched exception. *)

val raise : ?info:info -> exn -> 'a
(** Raise the given exception with additional information. *)
