(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Extraction to OCaml of persistent arrays. *)

From Stdlib Require PArray Extraction.

(** Primitive types and operators. *)
Extract Constant PrimArray.array "'a" => "'a Parray.t".
Extraction Inline PrimArray.array.
(* Otherwise, the name conflicts with the primitive OCaml type [array] *)

Extract Constant PrimArray.make => "Parray.make".
Extract Constant PrimArray.get => "Parray.get".
Extract Constant PrimArray.default => "Parray.default".
Extract Constant PrimArray.set => "Parray.set".
Extract Constant PrimArray.length => "Parray.length".
Extract Constant PrimArray.copy => "Parray.copy".
