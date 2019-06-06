(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.

Ltac2 @external make : int -> char -> string := "ltac2" "string_make".
Ltac2 @external length : string -> int := "ltac2" "string_length".
Ltac2 @external get : string -> int -> char := "ltac2" "string_get".
Ltac2 @external set : string -> int -> char -> unit := "ltac2" "string_set".
