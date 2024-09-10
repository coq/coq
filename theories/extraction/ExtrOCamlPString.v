(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Extraction to OCaml of primitive strings.

Note: the extraction of primitive strings relies on Coq's internal file
kernel/pstring.ml, so make sure the corresponding binary is available
when linking the extracted OCaml code.

For example, if you build a ("_CoqProject" + coq_makefile)-based project
and if you created an empty subfolder "extracted" and a file "test.v"
containing [Cd "extracted". Separate Extraction function_to_extract.],
you will just need to add in the "_CoqProject" file: [test.v], [-I extracted]
and the list of [extracted/*.ml] and [extracted/*.mli] files, then add
[CAMLFLAGS += -w -33] in the Makefile.local file.  *)

From Stdlib Require PrimString Extraction.
From Stdlib Require Import ExtrOCamlInt63.

(** Primitive types and operators. *)

Extract Constant PrimString.string => "Pstring.t".

Extract Constant PrimString.max_length => "Pstring.max_length".
Extract Constant PrimString.make => "Pstring.make".
Extract Constant PrimString.length => "Pstring.length".
Extract Constant PrimString.get => "Pstring.get".
Extract Constant PrimString.sub => "Pstring.sub".
Extract Constant PrimString.cat => "Pstring.cat".
Extract Constant PrimString.compare => "(fun x y -> let c = Pstring.compare x y in if c = 0 then Eq else if c < 0 then Lt else Gt)".
