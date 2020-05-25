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

(** Starts the proof of a constant *)
val start_lemma
  :  name:Id.t
  -> poly:bool
  -> ?udecl:UState.universe_decl
  -> ?info:Declare.Info.t
  -> ?impargs:Impargs.manual_implicits
  -> Evd.evar_map
  -> EConstr.types
  -> Declare.Proof.t

val start_dependent_lemma
  :  name:Id.t
  -> poly:bool
  -> ?udecl:UState.universe_decl
  -> ?info:Declare.Info.t
  -> Proofview.telescope
  -> Declare.Proof.t

(** Pretty much internal, used by the Lemma / Fixpoint vernaculars *)
val start_lemma_with_initialization
  :  ?hook:Declare.Hook.t
  -> poly:bool
  -> scope:Declare.locality
  -> kind:Decls.logical_kind
  -> udecl:UState.universe_decl
  -> Evd.evar_map
  -> (bool * Declare.lemma_possible_guards * Constr.t option list option) option
  -> Declare.Recthm.t list
  -> int list option
  -> Declare.Proof.t
