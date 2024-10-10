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
Require Stdlib.Init.Byte.
Require Stdlib.Init.Decimal.
Require Stdlib.Init.Hexadecimal.
Require Stdlib.Init.Number.
Require Stdlib.Init.Nat.
Require Export Peano.
Require Export Stdlib.Init.Wf.
Require Export Stdlib.Init.Ltac.
Require Export Stdlib.Init.Tactics.
Require Export Stdlib.Init.Tauto.
Require Export Stdlib.Init.Sumbool.
(* Some initially available plugins. See also:
   - ltac_plugin (in Ltac)
   - tauto_plugin (in Tauto).
*)
Declare ML Module "cc_core_plugin:coq-core.plugins.cc_core".
Declare ML Module "cc_plugin:coq-core.plugins.cc".
Declare ML Module "firstorder_core_plugin:coq-core.plugins.firstorder_core".
Declare ML Module "firstorder_plugin:coq-core.plugins.firstorder".

(* Parsing / printing of hexadecimal numbers *)
Arguments Nat.of_hex_uint d%_hex_uint_scope.
Arguments Nat.of_hex_int d%_hex_int_scope.
Number Notation Number.uint Number.uint_of_uint Number.uint_of_uint
  : hex_uint_scope.
Number Notation Number.int Number.int_of_int Number.int_of_int
  : hex_int_scope.

(* Parsing / printing of decimal numbers *)
Arguments Nat.of_uint d%_dec_uint_scope.
Arguments Nat.of_int d%_dec_int_scope.
Number Notation Number.uint Number.uint_of_uint Number.uint_of_uint
  : dec_uint_scope.
Number Notation Number.int Number.int_of_int Number.int_of_int
  : dec_int_scope.

(* Parsing / printing of [nat] numbers *)
Number Notation nat Nat.of_num_uint Nat.to_num_hex_uint (abstract after 5000) : hex_nat_scope.
Number Notation nat Nat.of_num_uint Nat.to_num_uint (abstract after 5000) : nat_scope.

(* Printing/Parsing of bytes *)
Export Byte.ByteSyntaxNotations.

(* Default substrings not considered by queries like Search *)
Add Search Blacklist "_subproof" "_subterm" "Private_".

(* Dummy coercion used by the elaborator to leave a trace in its
   result. When [x] is (reversible) coerced to [x'], the result
   [reverse_coercion x' x], convertible to [x'] will still be displayed [x]
   thanks to the reverse_coercion coercion. *)
#[universes(polymorphic=yes)] Definition ReverseCoercionSource (T : Type) := T.
#[universes(polymorphic=yes)] Definition ReverseCoercionTarget (T : Type) := T.
#[warning="-uniform-inheritance", reversible=no, universes(polymorphic=yes)]
Coercion reverse_coercion {T' T} (x' : T') (x : ReverseCoercionSource T)
  : ReverseCoercionTarget T' := x'.
Register reverse_coercion as core.coercion.reverse_coercion.
