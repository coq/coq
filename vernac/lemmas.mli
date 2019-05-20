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

(* Hooks allow users of the API to perform arbitrary actions at
 * proof/definition saving time. For example, to register a constant
 * as a Coercion, perform some cleanup, update the search database,
 * etc...
 *
 * Here, we use an extended hook type suitable for obligations /
 * equations.
 *)
(** [hook_type] passes to the client:
    - [ustate]: universe constraints obtained when the term was closed
    - [(n1,t1),...(nm,tm)]: association list between obligation
        name and the corresponding defined term (might be a constant,
        but also an arbitrary term in the Expand case of obligations)
    - [locality]: Locality of the original declaration
    - [ref]: identifier of the origianl declaration
 *)
type hook_type = UState.t -> (Id.t * Constr.t) list -> Decl_kinds.locality -> GlobRef.t -> unit

val mk_hook : hook_type -> declaration_hook
val call_hook
  :  ?hook:declaration_hook
  -> ?fix_exn:Future.fix_exn
  -> hook_type

val start_proof : Id.t -> ?pl:UState.universe_decl -> goal_kind -> Evd.evar_map ->
  ?terminator:(?hook:declaration_hook -> Proof_global.lemma_possible_guards -> Proof_global.proof_terminator) ->
  ?sign:Environ.named_context_val ->
  ?compute_guard:Proof_global.lemma_possible_guards ->
  ?hook:declaration_hook -> EConstr.types -> Proof_global.pstate

val start_proof_com
  :  program_mode:bool
  -> ?inference_hook:Pretyping.inference_hook
  -> ?hook:declaration_hook -> goal_kind -> Vernacexpr.proof_expr list
  -> Proof_global.pstate

val start_proof_with_initialization :
  ?hook:declaration_hook ->
  goal_kind -> Evd.evar_map -> UState.universe_decl ->
  (bool * Proof_global.lemma_possible_guards * unit Proofview.tactic list option) option ->
  (Id.t (* name of thm *) *
     (EConstr.types (* type of thm *) * (Name.t list (* names to pre-introduce *) * Impargs.manual_explicitation list))) list
  -> int list option -> Proof_global.pstate

val standard_proof_terminator :
  ?hook:declaration_hook -> Proof_global.lemma_possible_guards ->
  Proof_global.proof_terminator

val fresh_name_for_anonymous_theorem : pstate:Proof_global.stack option -> Id.t

(* Prepare global named context for proof session: remove proofs of
   opaque section definitions and remove vm-compiled code *)

val initialize_named_context_for_proof : unit -> Environ.named_context_val

(** {6 ... } *)

val save_proof_admitted
  :  ?proof:Proof_global.closed_proof
  -> pstate:Proof_global.pstate
  -> unit

val save_proof_proved
  :  ?proof:Proof_global.closed_proof
  -> ?ontop:Proof_global.stack
  -> opaque:Proof_global.opacity_flag
  -> idopt:Names.lident option
  -> Proof_global.stack option

val save_pstate_proved
  : pstate:Proof_global.pstate
  -> opaque:Proof_global.opacity_flag
  -> idopt:Names.lident option
  -> unit
