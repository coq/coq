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

(* Declaration hooks *)
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

(* Proofs that define a constant + terminators *)
type t
type proof_terminator

module Stack : sig

  type lemma = t
  type t

  val pop : t -> lemma * t option
  val push : t option -> lemma -> t

  val map_top : f:(lemma -> lemma) -> t -> t
  val map_top_pstate : f:(Proof_global.t -> Proof_global.t) -> t -> t

  val with_top : t -> f:(lemma -> 'a ) -> 'a
  val with_top_pstate : t -> f:(Proof_global.t -> 'a ) -> 'a

  val get_all_proof_names : t -> Names.Id.t list

  val copy_terminators : src:t -> tgt:t -> t
  (** Gets the current terminator without checking that the proof has
      been completed. Useful for the likes of [Admitted]. *)

end

val standard_proof_terminator
  :  Proof_global.lemma_possible_guards
  -> proof_terminator

val set_endline_tactic : Genarg.glob_generic_argument -> t -> t
val pf_map : (Proof_global.t -> Proof_global.t) -> t -> t
val pf_fold : (Proof_global.t -> 'a) -> t -> 'a

val by : unit Proofview.tactic -> t -> t * bool

(* Start of high-level proofs with an associated constant *)

val start_lemma
  :  Id.t
  -> ?pl:UState.universe_decl
  -> goal_kind
  -> Evd.evar_map
  -> ?terminator:(Proof_global.lemma_possible_guards -> proof_terminator)
  -> ?sign:Environ.named_context_val
  -> ?compute_guard:Proof_global.lemma_possible_guards
  -> ?hook:declaration_hook
  -> EConstr.types
  -> t

val start_dependent_lemma
  :  Id.t
  -> ?pl:UState.universe_decl
  -> goal_kind
  -> ?terminator:(Proof_global.lemma_possible_guards -> proof_terminator)
  -> ?sign:Environ.named_context_val
  -> ?compute_guard:Proof_global.lemma_possible_guards
  -> ?hook:declaration_hook
  -> Proofview.telescope
  -> t

val start_lemma_com
  :  program_mode:bool
  -> ?inference_hook:Pretyping.inference_hook
  -> ?hook:declaration_hook -> goal_kind -> Vernacexpr.proof_expr list
  -> t

val start_lemma_with_initialization
  :  ?hook:declaration_hook
  -> goal_kind -> Evd.evar_map -> UState.universe_decl
  -> (bool * Proof_global.lemma_possible_guards * unit Proofview.tactic list option) option
  -> (Id.t (* name of thm *) *
     (EConstr.types (* type of thm *) *
      (Name.t list (* names to pre-introduce *) * Impargs.manual_implicits))) list
  -> int list option
  -> t

val default_thm_id : Names.Id.t

(* Prepare global named context for proof session: remove proofs of
   opaque section definitions and remove vm-compiled code *)

val initialize_named_context_for_proof : unit -> Environ.named_context_val

(** {6 Saving proofs } *)

val save_lemma_admitted
  :  ?proof:(Proof_global.proof_object * proof_terminator * declaration_hook option)
  -> lemma:t
  -> unit

val save_lemma_proved
  :  ?proof:(Proof_global.proof_object * proof_terminator * declaration_hook option)
  -> ?lemma:t
  -> opaque:Proof_global.opacity_flag
  -> idopt:Names.lident option
  -> unit

(* API to build a terminator, should go away *)
type proof_ending =
  | Admitted of
      Names.Id.t *
      Decl_kinds.goal_kind *
      Entries.parameter_entry *
      UState.t *
      declaration_hook option
  | Proved of
      Proof_global.opacity_flag *
      lident option *
      Proof_global.proof_object *
      declaration_hook option

(** This stuff is internal and will be removed in the future.  *)
module Internal : sig

  (** Only needed due to the Proof_global compatibility layer. *)
  val get_terminator : t -> proof_terminator
  val get_hook : t -> declaration_hook option

  (** Only needed by obligations, should be reified soon *)
  val make_terminator : (proof_ending -> unit) -> proof_terminator
  val apply_terminator : proof_terminator -> proof_ending -> unit

end
