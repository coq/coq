(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.

Ltac2 Type t := string.

Ltac2 @external make : int -> char -> string := "coq-core.plugins.ltac2" "string_make".
Ltac2 @external length : string -> int := "coq-core.plugins.ltac2" "string_length".
Ltac2 @external get : string -> int -> char := "coq-core.plugins.ltac2" "string_get".
Ltac2 @external set : string -> int -> char -> unit := "coq-core.plugins.ltac2" "string_set".
Ltac2 @external concat : string -> string list -> string := "coq-core.plugins.ltac2" "string_concat".
Ltac2 @external app : string -> string -> string := "coq-core.plugins.ltac2" "string_app".
Ltac2 @external sub : string -> int -> int -> string := "coq-core.plugins.ltac2" "string_sub".
Ltac2 @external equal : string -> string -> bool := "coq-core.plugins.ltac2" "string_equal".
Ltac2 @external compare : string -> string -> int := "coq-core.plugins.ltac2" "string_compare".

Ltac2 is_empty s := match s with "" => true | _ => false end.
