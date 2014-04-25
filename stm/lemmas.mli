(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Decl_kinds
open Constrexpr
open Tacexpr
open Vernacexpr
open Pfedit

(** A hook start_proof calls on the type of the definition being started *)
val set_start_hook : (types -> unit) -> unit

val start_proof : Id.t -> goal_kind -> ?sign:Environ.named_context_val -> types ->
  ?init_tac:unit Proofview.tactic -> ?compute_guard:lemma_possible_guards -> 
   unit declaration_hook -> unit

val start_proof_com : goal_kind ->
  (lident option * (local_binder list * constr_expr * (lident option * recursion_order_expr) option)) list ->
  unit declaration_hook -> unit

val start_proof_with_initialization : 
  goal_kind -> (bool * lemma_possible_guards * unit Proofview.tactic list option) option ->
  (Id.t * (types * (Name.t list * Impargs.manual_explicitation list))) list
  -> int list option -> unit declaration_hook -> unit

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

