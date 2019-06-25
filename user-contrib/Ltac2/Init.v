(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Declare ML Module "ltac2_plugin".

(** Primitive types *)

Ltac2 Type int.
Ltac2 Type string.
Ltac2 Type char.
Ltac2 Type ident.
Ltac2 Type uint63.

(** Constr-specific built-in types *)
Ltac2 Type meta.
Ltac2 Type evar.
Ltac2 Type sort.
Ltac2 Type cast.
Ltac2 Type instance.
Ltac2 Type constant.
Ltac2 Type inductive.
Ltac2 Type constructor.
Ltac2 Type projection.
Ltac2 Type pattern.
Ltac2 Type constr.

Ltac2 Type message.
Ltac2 Type exn := [ .. ].
Ltac2 Type 'a array.

(** Pervasive types *)

Ltac2 Type 'a option := [ None | Some ('a) ].

Ltac2 Type 'a ref := { mutable contents : 'a }.

Ltac2 Type bool := [ true | false ].

Ltac2 Type 'a result := [ Val ('a) | Err (exn) ].

(** Pervasive exceptions *)

Ltac2 Type err.
(** Coq internal errors. Cannot be constructed, merely passed around. *)

Ltac2 Type exn ::= [ Internal (err) ].
(** Wrapper around the errors raised by Coq implementation. *)

Ltac2 Type exn ::= [ Out_of_bounds (message option) ].
(** Used for bound checking, e.g. with String and Array. *)

Ltac2 Type exn ::= [ Not_focussed ].
(** In Ltac2, the notion of "current environment" only makes sense when there is
    at most one goal under focus. Contrarily to Ltac1, instead of dynamically
    focussing when we need it, we raise this non-backtracking error when it does
    not make sense. *)

Ltac2 Type exn ::= [ Not_found ].
(** Used when something is missing. *)

Ltac2 Type exn ::= [ No_value ].
(** Used for empty lists, None options and the like. *)

Ltac2 Type exn ::= [ Match_failure ].
(** Used to signal a pattern didn't match a term. *)

Ltac2 Type exn ::= [ Invalid_argument (message option) ].
(** Used to signal that an invalid argument was passed to a tactic. *)

Ltac2 Type exn ::= [ Tactic_failure (message option) ].
(** Generic error for tactic failure. *)
