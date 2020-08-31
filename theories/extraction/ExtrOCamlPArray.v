(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Extraction to OCaml of persistent arrays. *)

From Coq Require PArray Extraction.

(** Primitive types and operators. *)
Extract Constant PArray.array "'a" => "'a Parray.t".
Extraction Inline PArray.array.
(* Otherwise, the name conflicts with the primitive OCaml type [array] *)

Extract Constant PArray.make => "Parray.make".
Extract Constant PArray.get => "Parray.get".
Extract Constant PArray.default => "Parray.default".
Extract Constant PArray.set => "Parray.set".
Extract Constant PArray.length => "Parray.length".
Extract Constant PArray.copy => "Parray.copy".
