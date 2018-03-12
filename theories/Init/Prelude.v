(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export Notations.
Require Export Logic.
Require Export Logic_Type.
Require Export Datatypes.
Require Export Specif.
Require Coq.Init.Decimal.
Require Coq.Init.Nat.
Require Export Peano.
Require Export Coq.Init.Wf.
Require Export Coq.Init.Tactics.
Require Export Coq.Init.Tauto.
(* Some initially available plugins. See also:
   - ltac_plugin (in Notations)
   - tauto_plugin (in Tauto).
*)
Declare ML Module "cc_plugin".
Declare ML Module "ground_plugin".
Declare ML Module "numeral_notation_plugin".

(* Parsing / printing of decimal numbers *)
Arguments Nat.of_uint d%dec_uint_scope.
Arguments Nat.of_int d%dec_int_scope.
Numeral Notation Decimal.uint Decimal.uint_of_uint Decimal.uint_of_uint
  : dec_uint_scope.
Numeral Notation Decimal.int Decimal.int_of_int Decimal.int_of_int
  : dec_int_scope.

(* Parsing / printing of [nat] numbers *)
Numeral Notation nat Nat.of_uint Nat.to_uint : nat_scope (abstract after 5000).

(* Default substrings not considered by queries like SearchAbout *)
Add Search Blacklist "_subproof" "_subterm" "Private_".
