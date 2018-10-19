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

val attach : exn -> info -> exn
(** Attach information to the given exception. *)

(** Deprecated stuff *)
type iexn = exn * info
[@@ocaml.deprecated "pairs of exn * info are deprecated and only needed in very specific exception manipulation cases"]

val iraise : exn * info -> 'a
[@@ocaml.deprecated "Use regular [raise] or [reraise] plus [attach]"]
