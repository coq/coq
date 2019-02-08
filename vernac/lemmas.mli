(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Decl_kinds

type declaration_hook

val mk_hook : (Decl_kinds.locality -> GlobRef.t -> unit) -> declaration_hook
val call_hook :
  ?hook:declaration_hook -> ?fix_exn:Future.fix_exn ->
  Decl_kinds.locality -> GlobRef.t -> unit

val start_proof : Id.t -> ?pl:UState.universe_decl -> goal_kind -> Evd.evar_map ->
  ?terminator:(?hook:declaration_hook -> Proof_global.lemma_possible_guards -> Proof_global.proof_terminator) ->
  ?sign:Environ.named_context_val ->
  ?compute_guard:Proof_global.lemma_possible_guards ->
  ?hook:declaration_hook ->  EConstr.types -> unit

val start_proof_univs : Id.t -> ?pl:UState.universe_decl -> goal_kind -> Evd.evar_map ->
  ?terminator:(?univ_hook:(UState.t option -> declaration_hook) -> Proof_global.lemma_possible_guards -> Proof_global.proof_terminator) ->
  ?sign:Environ.named_context_val ->
  ?compute_guard:Proof_global.lemma_possible_guards ->
  ?univ_hook:(UState.t option -> declaration_hook) -> EConstr.types -> unit

val start_proof_com :
  program_mode:bool -> ?inference_hook:Pretyping.inference_hook ->
  ?hook:declaration_hook -> goal_kind -> Vernacexpr.proof_expr list ->
  unit

val start_proof_with_initialization :
  ?hook:declaration_hook ->
  goal_kind -> Evd.evar_map -> UState.universe_decl ->
  (bool * Proof_global.lemma_possible_guards * unit Proofview.tactic list option) option ->
  (Id.t (* name of thm *) *
     (EConstr.types (* type of thm *) * (Name.t list (* names to pre-introduce *) * Impargs.manual_explicitation list))) list ->
  int list option -> unit

val universe_proof_terminator :
  ?univ_hook:(UState.t option -> declaration_hook) ->
  Proof_global.lemma_possible_guards ->
  Proof_global.proof_terminator

val standard_proof_terminator :
  ?hook:declaration_hook -> Proof_global.lemma_possible_guards ->
  Proof_global.proof_terminator

val fresh_name_for_anonymous_theorem : unit -> Id.t

(* Prepare global named context for proof session: remove proofs of
   opaque section definitions and remove vm-compiled code *)

val initialize_named_context_for_proof : unit -> Environ.named_context_val

(** {6 ... } *)

val save_proof : ?proof:Proof_global.closed_proof -> Vernacexpr.proof_end -> unit
