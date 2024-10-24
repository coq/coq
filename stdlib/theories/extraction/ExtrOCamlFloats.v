(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Extraction to OCaml of native binary64 floating-point numbers.

Note: the extraction of primitive floats relies on Coq's internal file
kernel/float64.ml, so make sure the corresponding binary is available
when linking the extracted OCaml code.

For example, if you build a ("_CoqProject" + coq_makefile)-based project
and if you created an empty subfolder "extracted" and a file "test.v"
containing [Cd "extracted". Separate Extraction function_to_extract.],
you will just need to add in the "_CoqProject" file: [test.v], [-I extracted]
and the list of [extracted/*.ml] and [extracted/*.mli] files, then add
[CAMLFLAGS += -w -33] in the Makefile.local file.  *)

From Stdlib Require Floats Extraction.

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
Extract Constant PrimFloat.Leibniz.eqb => "Float64.equal".
Extract Constant PrimFloat.mul => "Float64.mul".
Extract Constant PrimFloat.add => "Float64.add".
Extract Constant PrimFloat.sub => "Float64.sub".
Extract Constant PrimFloat.div => "Float64.div".
Extract Constant PrimFloat.of_uint63 => "Float64.of_uint63".
Extract Constant PrimFloat.normfr_mantissa => "Float64.normfr_mantissa".
Extract Constant PrimFloat.frshiftexp => "Float64.frshiftexp".
Extract Constant PrimFloat.ldshiftexp => "Float64.ldshiftexp".
Extract Constant PrimFloat.next_up => "Float64.next_up".
Extract Constant PrimFloat.next_down => "Float64.next_down".
