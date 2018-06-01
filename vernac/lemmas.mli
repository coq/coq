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

type 'a declaration_hook
val mk_hook :
  (Decl_kinds.locality -> GlobRef.t -> 'a) -> 'a declaration_hook

val call_hook :
  Future.fix_exn -> 'a declaration_hook -> Decl_kinds.locality -> GlobRef.t -> 'a

(** A hook start_proof calls on the type of the definition being started *)
val set_start_hook : (EConstr.types -> unit) -> unit

val start_proof : Id.t -> ?pl:UState.universe_decl -> goal_kind -> Evd.evar_map ->
  ?terminator:(Proof_global.lemma_possible_guards -> unit declaration_hook -> Proof_global.proof_terminator) ->
  ?sign:Environ.named_context_val -> EConstr.types ->
  ?init_tac:unit Proofview.tactic -> ?compute_guard:Proof_global.lemma_possible_guards -> 
   unit declaration_hook -> unit

val start_proof_univs : Id.t -> ?pl:UState.universe_decl -> goal_kind -> Evd.evar_map ->
  ?terminator:(Proof_global.lemma_possible_guards -> (UState.t option -> unit declaration_hook) -> Proof_global.proof_terminator) ->
  ?sign:Environ.named_context_val -> EConstr.types ->
  ?init_tac:unit Proofview.tactic -> ?compute_guard:Proof_global.lemma_possible_guards -> 
  (UState.t option -> unit declaration_hook) -> unit

val start_proof_com :
  ?inference_hook:Pretyping.inference_hook ->
  goal_kind -> Vernacexpr.proof_expr list ->
  unit declaration_hook -> unit

val start_proof_with_initialization :
  goal_kind -> Evd.evar_map -> UState.universe_decl ->
  (bool * Proof_global.lemma_possible_guards * unit Proofview.tactic list option) option ->
  (Id.t (* name of thm *) *
     (EConstr.types (* type of thm *) * (Name.t list (* names to pre-introduce *) * Impargs.manual_explicitation list))) list
  -> int list option -> unit declaration_hook -> unit

val universe_proof_terminator :
  Proof_global.lemma_possible_guards ->
    (UState.t option -> unit declaration_hook) ->
    Proof_global.proof_terminator

val standard_proof_terminator :
  Proof_global.lemma_possible_guards -> unit declaration_hook ->
    Proof_global.proof_terminator

val fresh_name_for_anonymous_theorem : unit -> Id.t

(** {6 ... } *)

(** A hook the next three functions pass to cook_proof *)
val set_save_hook : (Proof.t -> unit) -> unit

val save_proof : ?proof:Proof_global.closed_proof -> Vernacexpr.proof_end -> unit


(** [get_current_context ()] returns the evar context and env of the
   current open proof if any, otherwise returns the empty evar context
   and the current global env *)

val get_current_context : unit -> Evd.evar_map * Environ.env
[@@ocaml.deprecated "please use [Pfedit.get_current_context]"]
