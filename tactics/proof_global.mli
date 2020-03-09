(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** State for interactive proofs. *)

type t

(* Should be moved into a proper view *)
val get_proof : t -> Proof.t
val get_proof_name : t -> Names.Id.t
val get_used_variables : t -> Names.Id.Set.t option

(** Get the universe declaration associated to the current proof. *)
val get_universe_decl : t -> UState.universe_decl

(** Get initial universe state *)
val get_initial_euctx : t -> UState.t

val compact_the_proof : t -> t

(** When a proof is closed, it is reified into a [proof_object] *)
type proof_object =
  { name : Names.Id.t
  (** name of the proof *)
  ; entries : Evd.side_effects Declare.proof_entry list
  (** list of the proof terms (in a form suitable for definitions). *)
  ; uctx: UState.t
  (** universe state *)
  }

type opacity_flag = Opaque | Transparent

(** [start_proof ~name ~udecl ~poly sigma goals] starts a proof of
   name [name] with goals [goals] (a list of pairs of environment and
   conclusion); [poly] determines if the proof is universe
   polymorphic. The proof is started in the evar map [sigma] (which
   can typically contain universe constraints), and with universe
   bindings [udecl]. *)
val start_proof
  :  name:Names.Id.t
  -> udecl:UState.universe_decl
  -> poly:bool
  -> Evd.evar_map
  -> (Environ.env * EConstr.types) list
  -> t

(** Like [start_proof] except that there may be dependencies between
    initial goals. *)
val start_dependent_proof
  :  name:Names.Id.t
  -> udecl:UState.universe_decl
  -> poly:bool
  -> Proofview.telescope
  -> t

(** Update the proofs global environment after a side-effecting command
  (e.g. a sublemma definition) has been run inside it. Assumes
  there_are_pending_proofs. *)
val update_global_env : t -> t

(* Takes a function to add to the exceptions data relative to the
   state in which the proof was built *)
val close_proof : opaque:opacity_flag -> keep_body_ucst_separate:bool -> Future.fix_exn -> t -> proof_object

(* Intermediate step necessary to delegate the future.
 * Both access the current proof state. The former is supposed to be
 * chained with a computation that completed the proof *)

type closed_proof_output

(* If allow_partial is set (default no) then an incomplete proof
 * is allowed (no error), and a warn is given if the proof is complete. *)
val return_proof : ?allow_partial:bool -> t -> closed_proof_output
val close_future_proof : opaque:opacity_flag -> feedback_id:Stateid.t -> t ->
  closed_proof_output Future.computation -> proof_object

val get_open_goals : t -> int

val map_proof : (Proof.t -> Proof.t) -> t -> t
val map_fold_proof : (Proof.t -> Proof.t * 'a) -> t -> t * 'a
val map_fold_proof_endline : (unit Proofview.tactic -> Proof.t -> Proof.t * 'a) -> t -> t * 'a

(** Sets the tactic to be used when a tactic line is closed with [...] *)
val set_endline_tactic : Genarg.glob_generic_argument -> t -> t

(** Sets the section variables assumed by the proof, returns its closure
 * (w.r.t. type dependencies and let-ins covered by it) + a list of
 * ids to be cleared *)
val set_used_variables : t ->
  Names.Id.t list -> (Constr.named_context * Names.lident list) * t
