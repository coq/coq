(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*s This module declares the extraction commands. *)

open Names
open Libnames

val simple_extraction : reference -> unit
val full_extraction : string option -> reference list -> unit
val separate_extraction : reference list -> unit
val extraction_library : bool -> Id.t -> unit

(* For the test-suite : extraction to a temporary file + ocamlc on it *)

val extract_and_compile : reference list -> unit

(* For debug / external output via coqtop.byte + Drop : *)

val mono_environment :
 global_reference list -> ModPath.t list -> Miniml.ml_structure

(* Used by the Relation Extraction plugin *)

val print_one_decl :
  Miniml.ml_structure -> ModPath.t -> Miniml.ml_decl -> Pp.t

(* Used by Extraction Compute *)

val structure_for_compute :
  Constr.t -> (Miniml.ml_decl list) * Miniml.ml_ast * Miniml.ml_type
