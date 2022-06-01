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
Require Export Datatypes.
Require Export Specif.
Require Coq.Init.Byte.
Require Coq.Init.Decimal.
Require Coq.Init.Hexadecimal.
Require Coq.Init.Number.
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
Declare ML Module "cc_plugin:coq-core.plugins.cc".
Declare ML Module "firstorder_plugin:coq-core.plugins.firstorder".

(* Parsing / printing of hexadecimal numbers *)
Arguments Nat.of_hex_uint d%hex_uint_scope.
Arguments Nat.of_hex_int d%hex_int_scope.
Number Notation Number.uint Number.uint_of_uint Number.uint_of_uint
  : hex_uint_scope.
Number Notation Number.int Number.int_of_int Number.int_of_int
  : hex_int_scope.

(* Parsing / printing of decimal numbers *)
Arguments Nat.of_uint d%dec_uint_scope.
Arguments Nat.of_int d%dec_int_scope.
Number Notation Number.uint Number.uint_of_uint Number.uint_of_uint
  : dec_uint_scope.
Number Notation Number.int Number.int_of_int Number.int_of_int
  : dec_int_scope.

(* Parsing / printing of [nat] numbers *)
Number Notation nat Nat.of_num_uint Nat.to_num_hex_uint (abstract after 5001) : hex_nat_scope.
Number Notation nat Nat.of_num_uint Nat.to_num_uint (abstract after 5001) : nat_scope.

(* Printing/Parsing of bytes *)
Export Byte.ByteSyntaxNotations.

(* Default substrings not considered by queries like Search *)
Add Search Blacklist "_subproof" "_subterm" "Private_".
