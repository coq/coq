(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Decl_kinds

(* Proofs that define a constant *)
type t
type lemma_possible_guards = int list list

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

  val copy_info : src:t -> tgt:t -> t
  (** Gets the current info without checking that the proof has been
     completed. Useful for the likes of [Admitted]. *)

end

val set_endline_tactic : Genarg.glob_generic_argument -> t -> t
val pf_map : (Proof_global.t -> Proof_global.t) -> t -> t
val pf_fold : (Proof_global.t -> 'a) -> t -> 'a

val by : unit Proofview.tactic -> t -> t * bool

(* Start of high-level proofs with an associated constant *)

module Proof_ending : sig

  type t =
    | Regular
    | End_obligation of DeclareObl.obligation_qed_info
    | End_derive of { f : Id.t; name : Id.t }
    | End_equations of { hook : Constant.t list -> Evd.evar_map -> unit
                       ; i : Id.t
                       ; types : (Environ.env * Evar.t * Evd.evar_info * EConstr.named_context * Evd.econstr) list
                       ; wits : EConstr.t list ref
                       ; sigma : Evd.evar_map
                       }

end

val start_lemma
  :  Id.t
  -> ?pl:UState.universe_decl
  -> goal_kind
  -> Evd.evar_map
  -> ?proof_ending:Proof_ending.t
  -> ?sign:Environ.named_context_val
  -> ?compute_guard:lemma_possible_guards
  -> ?hook:DeclareDef.Hook.t
  -> EConstr.types
  -> t

val start_dependent_lemma
  :  Id.t
  -> ?pl:UState.universe_decl
  -> goal_kind
  -> ?proof_ending:Proof_ending.t
  -> ?compute_guard:lemma_possible_guards
  -> ?hook:DeclareDef.Hook.t
  -> Proofview.telescope
  -> t

val start_lemma_com
  :  program_mode:bool
  -> ?inference_hook:Pretyping.inference_hook
  -> ?hook:DeclareDef.Hook.t -> goal_kind -> Vernacexpr.proof_expr list
  -> t

val start_lemma_with_initialization
  :  ?hook:DeclareDef.Hook.t
  -> goal_kind -> Evd.evar_map -> UState.universe_decl
  -> (bool * lemma_possible_guards * unit Proofview.tactic list option) option
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

type proof_info

val default_info : proof_info

val save_lemma_admitted
  :  ?proof:(Proof_global.proof_object * proof_info)
  -> lemma:t
  -> unit

val save_lemma_proved
  :  ?proof:(Proof_global.proof_object * proof_info)
  -> ?lemma:t
  -> opaque:Proof_global.opacity_flag
  -> idopt:Names.lident option
  -> unit

(* To be removed *)
module Internal : sig
  (** Only needed due to the Proof_global compatibility layer. *)
  val get_info : t -> proof_info
end
