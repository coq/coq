(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Extraction to Ocaml : special handling of ascii and strings *)

Require Coq.extraction.Extraction.

Require Import Ascii String Coq.Strings.Byte.
Require Export ExtrOcamlChar.

Extract Inductive string => "char list" [ "[]" "(::)" ].
