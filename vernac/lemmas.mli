(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(** {4 Proofs attached to a constant} *)

type t
(** [Lemmas.t] represents a constant that is being proved, usually
    interactively *)

val set_endline_tactic : Genarg.glob_generic_argument -> t -> t
(** [set_endline_tactic tac lemma] set ending tactic for [lemma] *)

val pf_map : (Declare.Proof.t -> Declare.Proof.t) -> t -> t
(** [pf_map f l] map the underlying proof object *)

val pf_fold : (Declare.Proof.t -> 'a) -> t -> 'a
(** [pf_fold f l] fold over the underlying proof object *)

val by : unit Proofview.tactic -> t -> t * bool
(** [by tac l] apply a tactic to [l] *)

module Proof_ending = Declare.Proof_ending
module Info = Declare.Info

(** Starts the proof of a constant *)
val start_lemma
  :  name:Id.t
  -> poly:bool
  -> ?udecl:UState.universe_decl
  -> ?info:Info.t
  -> ?impargs:Impargs.manual_implicits
  -> Evd.evar_map
  -> EConstr.types
  -> t

val start_dependent_lemma
  :  name:Id.t
  -> poly:bool
  -> ?udecl:UState.universe_decl
  -> ?info:Info.t
  -> Proofview.telescope
  -> t

type lemma_possible_guards = int list list

(** Pretty much internal, used by the Lemma / Fixpoint vernaculars *)
val start_lemma_with_initialization
  :  ?hook:Declare.Hook.t
  -> poly:bool
  -> scope:Declare.locality
  -> kind:Decls.logical_kind
  -> udecl:UState.universe_decl
  -> Evd.evar_map
  -> (bool * lemma_possible_guards * Constr.t option list option) option
  -> Declare.Recthm.t list
  -> int list option
  -> t

(** {4 Saving proofs} *)

val save_lemma_admitted : lemma:t -> unit

val save_lemma_proved
  :  lemma:t
  -> opaque:Declare.opacity_flag
  -> idopt:Names.lident option
  -> unit

(** To be removed, don't use! *)
module Internal : sig
  val get_info : t -> Info.t
  (** Only needed due to the Declare compatibility layer. *)
end
