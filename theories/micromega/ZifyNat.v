(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Instances of [ZifyClasses] for dealing with advanced [nat] operators. *)

Require Import BinInt Znat Zdiv.
Require Import ZifyClasses ZifyInst Zify.

Ltac zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
