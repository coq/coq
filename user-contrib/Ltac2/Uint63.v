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

Ltac2 Type t := uint63.

Ltac2 @ external equal : t -> t -> bool := "coq-core.plugins.ltac2" "uint63_equal".

Ltac2 @external compare : t -> t -> int := "coq-core.plugins.ltac2" "uint63_compare".

Ltac2 @external of_int : int -> t := "coq-core.plugins.ltac2" "uint63_of_int".

Ltac2 @external print : t -> message := "coq-core.plugins.ltac2" "uint63_print".
