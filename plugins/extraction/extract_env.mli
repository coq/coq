(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*s This module declares the extraction commands. *)

open Names
open Libnames

val simple_extraction : qualid -> unit
val full_extraction : string option -> qualid list -> unit
val separate_extraction : qualid list -> unit
val extraction_library : bool -> Id.t -> unit

(* For the test-suite : extraction to a temporary file + ocamlc on it *)

val extract_and_compile : qualid list -> unit

(* For debug / external output via coqtop.byte + Drop : *)

val mono_environment :
 GlobRef.t list -> ModPath.t list -> Miniml.ml_structure

(* Used by the Relation Extraction plugin *)

val print_one_decl :
  Miniml.ml_structure -> ModPath.t -> Miniml.ml_decl -> Pp.t

(* Used by Extraction Compute *)

val structure_for_compute :
  Environ.env -> Evd.evar_map -> EConstr.t ->
    Miniml.ml_decl list * Miniml.ml_ast * Miniml.ml_type

(* Show the extraction of the current ongoing proof *)

val show_extraction : unit -> unit
