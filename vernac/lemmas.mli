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
