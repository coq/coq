(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*s This module declares the extraction commands. *)

open Names
open Libnames
open Globnames

val simple_extraction : reference -> unit
val full_extraction : string option -> reference list -> unit
val separate_extraction : reference list -> unit
val extraction_library : bool -> Id.t -> unit

(* For debug / external output via coqtop.byte + Drop : *)

val mono_environment :
 global_reference list -> module_path list -> Miniml.ml_structure

(* Used by the Relation Extraction plugin *)

val print_one_decl :
  Miniml.ml_structure -> module_path -> Miniml.ml_decl -> Pp.std_ppcmds

(* Used by Extraction Compute *)

val structure_for_compute :
  Term.constr ->
    Miniml.ml_flat_structure * Miniml.ml_ast * Miniml.ml_type
