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

Ltac2 Type t := pstring.

Ltac2 Type char63 := uint63.

Ltac2 @ external max_length : uint63 := "rocq-runtime.plugins.ltac2" "pstring_max_length".

Ltac2 @ external to_string : t -> string := "rocq-runtime.plugins.ltac2" "pstring_to_string".
Ltac2 @ external of_string : string -> t option := "rocq-runtime.plugins.ltac2" "pstring_of_string".

Ltac2 @ external make : uint63 -> char63 -> t := "rocq-runtime.plugins.ltac2" "pstring_make".
Ltac2 @ external length : t -> uint63 := "rocq-runtime.plugins.ltac2" "pstring_length".
Ltac2 @ external get : t -> uint63 -> char63 := "rocq-runtime.plugins.ltac2" "pstring_get".
Ltac2 @ external sub : t -> uint63 -> uint63 -> t := "rocq-runtime.plugins.ltac2" "pstring_sub".
Ltac2 @ external cat : t -> t -> t := "rocq-runtime.plugins.ltac2" "pstring_cat".

Ltac2 @ external equal : t -> t -> bool := "rocq-runtime.plugins.ltac2" "pstring_equal".
Ltac2 @ external compare : t -> t -> int := "rocq-runtime.plugins.ltac2" "pstring_compare".
