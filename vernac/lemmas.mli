(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Decl_kinds
open Pfedit

type 'a declaration_hook
val mk_hook :
  (Decl_kinds.locality -> Globnames.global_reference -> 'a) -> 'a declaration_hook

val call_hook :
  Future.fix_exn -> 'a declaration_hook -> Decl_kinds.locality -> Globnames.global_reference -> 'a

(** A hook start_proof calls on the type of the definition being started *)
val set_start_hook : (EConstr.types -> unit) -> unit

val start_proof : Id.t -> ?pl:universe_binders -> goal_kind -> Evd.evar_map ->
  ?terminator:(lemma_possible_guards -> unit declaration_hook -> Proof_global.proof_terminator) ->
  ?sign:Environ.named_context_val -> EConstr.types ->
  ?init_tac:unit Proofview.tactic -> ?compute_guard:lemma_possible_guards -> 
   unit declaration_hook -> unit

val start_proof_univs : Id.t -> ?pl:universe_binders -> goal_kind -> Evd.evar_map ->
  ?terminator:(lemma_possible_guards -> (Evd.evar_universe_context option -> unit declaration_hook) -> Proof_global.proof_terminator) ->
  ?sign:Environ.named_context_val -> EConstr.types ->
  ?init_tac:unit Proofview.tactic -> ?compute_guard:lemma_possible_guards -> 
  (Evd.evar_universe_context option -> unit declaration_hook) -> unit

val start_proof_com :
  ?inference_hook:Pretyping.inference_hook ->
  goal_kind -> Vernacexpr.proof_expr list ->
  unit declaration_hook -> unit

val start_proof_with_initialization : 
  goal_kind -> Evd.evar_map ->
  (bool * lemma_possible_guards * unit Proofview.tactic list option) option ->
  ((Id.t (* name of thm *) * universe_binders option) *
     (types (* type of thm *) * (Name.t list (* names to pre-introduce *) * Impargs.manual_explicitation list))) list
  -> int list option -> unit declaration_hook -> unit

val universe_proof_terminator :
  Proof_global.lemma_possible_guards ->
    (Evd.evar_universe_context option -> unit declaration_hook) ->
    Proof_global.proof_terminator

val standard_proof_terminator :
  Proof_global.lemma_possible_guards -> unit declaration_hook ->
    Proof_global.proof_terminator

(** {6 ... } *)

(** A hook the next three functions pass to cook_proof *)
val set_save_hook : (Proof.proof -> unit) -> unit

val save_proof : ?proof:Proof_global.closed_proof -> Vernacexpr.proof_end -> unit


(** [get_current_context ()] returns the evar context and env of the
   current open proof if any, otherwise returns the empty evar context
   and the current global env *)

val get_current_context : unit -> Evd.evar_map * Environ.env
