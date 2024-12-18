(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.

Ltac2 Type t := string.

Ltac2 @external make : int -> char -> string := "rocq-runtime.plugins.ltac2" "string_make".
Ltac2 @external length : string -> int := "rocq-runtime.plugins.ltac2" "string_length".
Ltac2 @external get : string -> int -> char := "rocq-runtime.plugins.ltac2" "string_get".
Ltac2 @external set : string -> int -> char -> unit := "rocq-runtime.plugins.ltac2" "string_set".
Ltac2 @external concat : string -> string list -> string := "rocq-runtime.plugins.ltac2" "string_concat".
Ltac2 @external app : string -> string -> string := "rocq-runtime.plugins.ltac2" "string_app".
Ltac2 @external sub : string -> int -> int -> string := "rocq-runtime.plugins.ltac2" "string_sub".
Ltac2 @external equal : string -> string -> bool := "rocq-runtime.plugins.ltac2" "string_equal".
Ltac2 @external compare : string -> string -> int := "rocq-runtime.plugins.ltac2" "string_compare".

Ltac2 is_empty s := match s with "" => true | _ => false end.
