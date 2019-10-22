(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Extraction to OCaml of native binary64 floating-point numbers. *)

From Coq Require Floats Extraction.

(** Basic data types used by some primitive operators. *)

Extract Inductive bool => bool [ true false ].
Extract Inductive prod => "( * )" [ "" ].

Extract Inductive FloatClass.float_class =>
  "Float64.float_class"
  [ "PNormal" "NNormal" "PSubn" "NSubn" "PZero" "NZero" "PInf" "NInf" "NaN" ].
Extract Inductive PrimFloat.float_comparison =>
  "Float64.float_comparison"
  [ "FEq" "FLt" "FGt" "FNotComparable" ].

(** Primitive types and operators. *)

Extract Constant PrimFloat.float => "Float64.t".
Extraction Inline PrimFloat.float.
(* Otherwise, the name conflicts with the primitive OCaml type [float] *)

Extract Constant PrimFloat.classify => "Float64.classify".
Extract Constant PrimFloat.abs => "Float64.abs".
Extract Constant PrimFloat.sqrt => "Float64.sqrt".
Extract Constant PrimFloat.opp => "Float64.opp".
Extract Constant PrimFloat.eqb => "Float64.eq".
Extract Constant PrimFloat.ltb => "Float64.lt".
Extract Constant PrimFloat.leb => "Float64.le".
Extract Constant PrimFloat.compare => "Float64.compare".
Extract Constant PrimFloat.mul => "Float64.mul".
Extract Constant PrimFloat.add => "Float64.add".
Extract Constant PrimFloat.sub => "Float64.sub".
Extract Constant PrimFloat.div => "Float64.div".
Extract Constant PrimFloat.of_int63 => "Float64.of_int63".
Extract Constant PrimFloat.normfr_mantissa => "Float64.normfr_mantissa".
Extract Constant PrimFloat.frshiftexp => "Float64.frshiftexp".
Extract Constant PrimFloat.ldshiftexp => "Float64.ldshiftexp".
Extract Constant PrimFloat.next_up => "Float64.next_up".
Extract Constant PrimFloat.next_down => "Float64.next_down".
