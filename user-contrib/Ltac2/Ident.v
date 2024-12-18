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

Ltac2 Type t := ident.

Ltac2 @ external equal : t -> t -> bool := "rocq-runtime.plugins.ltac2" "ident_equal".

Ltac2 @ external of_string : string -> t option := "rocq-runtime.plugins.ltac2" "ident_of_string".

Ltac2 @ external to_string : t -> string := "rocq-runtime.plugins.ltac2" "ident_to_string".
