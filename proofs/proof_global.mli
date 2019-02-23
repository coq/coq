(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module defines proof facilities relevant to the
     toplevel. In particular it defines the global proof
     environment. *)

type t
val get_current_proof_name : t -> Names.Id.t
val get_current_persistence : t -> Decl_kinds.goal_kind
val get_all_proof_names : t -> Names.Id.t list

val discard : Names.lident -> t -> t option
val discard_current : t -> t option

val give_me_the_proof : t -> Proof.t
val compact_the_proof : t -> t

(** When a proof is closed, it is reified into a [proof_object], where
    [id] is the name of the proof, [entries] the list of the proof terms
    (in a form suitable for definitions). Together with the [terminator]
    function which takes a [proof_object] together with a [proof_end]
    (i.e. an proof ending command) and registers the appropriate
    values. *)
type lemma_possible_guards = int list list

type proof_object = {
  id : Names.Id.t;
  entries : Safe_typing.private_constants Entries.definition_entry list;
  persistence : Decl_kinds.goal_kind;
  universes: UState.t;
}

type opacity_flag = Opaque | Transparent

type proof_ending =
  | Admitted of Names.Id.t * Decl_kinds.goal_kind * Entries.parameter_entry *
                UState.t
  | Proved of opacity_flag *
              Names.lident option *
              proof_object
type proof_terminator
type closed_proof = proof_object * proof_terminator

val make_terminator : (proof_ending -> unit) -> proof_terminator
val apply_terminator : proof_terminator -> proof_ending -> unit

(** [start_proof ~ontop id str pl goals terminator] starts a proof of name
   [id] with goals [goals] (a list of pairs of environment and
   conclusion); [str] describes what kind of theorem/definition this
   is; [terminator] is used at the end of the proof to close the proof
   (e.g. to declare the built constructions as a coercion or a setoid
   morphism). The proof is started in the evar map [sigma] (which can
   typically contain universe constraints), and with universe bindings
   pl. *)
val start_proof : ontop:t option ->
  Evd.evar_map -> Names.Id.t -> ?pl:UState.universe_decl ->
  Decl_kinds.goal_kind -> (Environ.env * EConstr.types) list  ->
    proof_terminator -> t

(** Like [start_proof] except that there may be dependencies between
    initial goals. *)
val start_dependent_proof : ontop:t option ->
  Names.Id.t -> ?pl:UState.universe_decl -> Decl_kinds.goal_kind ->
  Proofview.telescope -> proof_terminator -> t

(** Update the proofs global environment after a side-effecting command
  (e.g. a sublemma definition) has been run inside it. Assumes
  there_are_pending_proofs. *)
val update_global_env : t -> t

(* Takes a function to add to the exceptions data relative to the
   state in which the proof was built *)
val close_proof : opaque:opacity_flag -> keep_body_ucst_separate:bool -> Future.fix_exn -> t -> closed_proof

(* Intermediate step necessary to delegate the future.
 * Both access the current proof state. The former is supposed to be
 * chained with a computation that completed the proof *)

type closed_proof_output = (Constr.t * Safe_typing.private_constants) list * UState.t

(* If allow_partial is set (default no) then an incomplete proof
 * is allowed (no error), and a warn is given if the proof is complete. *)
val return_proof : ?allow_partial:bool -> t -> closed_proof_output
val close_future_proof : opaque:opacity_flag -> feedback_id:Stateid.t -> t ->
  closed_proof_output Future.computation -> closed_proof

(** Gets the current terminator without checking that the proof has
    been completed. Useful for the likes of [Admitted]. *)
val get_terminator : t -> proof_terminator
val set_terminator : proof_terminator -> t -> t
val get_open_goals : t -> int

(** Runs a tactic on the current proof. Raises [NoCurrentProof] is there is
    no current proof.
    The return boolean is set to [false] if an unsafe tactic has been used. *)
val with_current_proof :
  (unit Proofview.tactic -> Proof.t -> Proof.t * 'a) -> t -> t * 'a
val simple_with_current_proof :
  (unit Proofview.tactic -> Proof.t -> Proof.t) -> t -> t

(** Sets the tactic to be used when a tactic line is closed with [...] *)
val set_endline_tactic : Genarg.glob_generic_argument -> t -> t

(** Sets the section variables assumed by the proof, returns its closure
 * (w.r.t. type dependencies and let-ins covered by it) + a list of
 * ids to be cleared *)
val set_used_variables : t ->
  Names.Id.t list -> (Constr.named_context * Names.lident list) * t

val get_used_variables : t -> Constr.named_context option

(** Get the universe declaration associated to the current proof. *)
val get_universe_decl : t -> UState.universe_decl

val copy_terminators : src:t -> tgt:t -> t
