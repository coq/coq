(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
Require Coq.Init.Byte.
Require Coq.Init.Decimal.
Require Coq.Init.Hexadecimal.
Require Coq.Init.Numeral.
Require Coq.Init.Nat.
Require Export Peano.
Require Export Coq.Init.Wf.
Require Export Coq.Init.Ltac.
Require Export Coq.Init.Tactics.
Require Export Coq.Init.Tauto.
(* Some initially available plugins. See also:
   - ltac_plugin (in Ltac)
   - tauto_plugin (in Tauto).
*)
Declare ML Module "cc_plugin".
Declare ML Module "ground_plugin".
Declare ML Module "numeral_notation_plugin".
Declare ML Module "string_notation_plugin".

(* Parsing / printing of hexadecimal numbers *)
Arguments Nat.of_hex_uint d%hex_uint_scope.
Arguments Nat.of_hex_int d%hex_int_scope.
Numeral Notation Numeral.uint Numeral.uint_of_uint Numeral.uint_of_uint
  : hex_uint_scope.
Numeral Notation Numeral.int Numeral.int_of_int Numeral.int_of_int
  : hex_int_scope.

(* Parsing / printing of decimal numbers *)
Arguments Nat.of_uint d%dec_uint_scope.
Arguments Nat.of_int d%dec_int_scope.
Numeral Notation Numeral.uint Numeral.uint_of_uint Numeral.uint_of_uint
  : dec_uint_scope.
Numeral Notation Numeral.int Numeral.int_of_int Numeral.int_of_int
  : dec_int_scope.

(* Parsing / printing of [nat] numbers *)
Numeral Notation nat Nat.of_num_uint Nat.to_num_hex_uint : hex_nat_scope (abstract after 5001).
Numeral Notation nat Nat.of_num_uint Nat.to_num_uint : nat_scope (abstract after 5001).

(* Printing/Parsing of bytes *)
Export Byte.ByteSyntaxNotations.

(* Default substrings not considered by queries like Search *)
Add Search Blacklist "_subproof" "_subterm" "Private_".
