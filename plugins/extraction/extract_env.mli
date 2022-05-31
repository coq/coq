(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*s This module declares the extraction commands. *)

val simple_extraction : Libnames.qualid -> unit
val full_extraction : string option -> Libnames.qualid list -> unit
val separate_extraction : Libnames.qualid list -> unit
val extraction_library : bool -> Names.lident -> unit

(* For the test-suite : extraction to a temporary file + ocamlc on it *)

val extract_and_compile : Libnames.qualid list -> unit

(* For debug / external output via coqtop.byte + Drop : *)

val mono_environment :
Names.GlobRef.t list -> Names.ModPath.t list -> Miniml.ml_structure

(* Used by the Relation Extraction plugin *)

val print_one_decl :
  Miniml.ml_structure -> Names.ModPath.t -> Miniml.ml_decl -> Pp.t

(* Used by Extraction Compute *)

val structure_for_compute :
  Environ.env -> Evd.evar_map -> EConstr.t ->
    Miniml.ml_decl list * Miniml.ml_ast * Miniml.ml_type

(* Show the extraction of the current ongoing proof *)

val show_extraction : pstate:Declare.Proof.t -> unit
