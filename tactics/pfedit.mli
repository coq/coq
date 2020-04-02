(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Global proof state. A quite redundant wrapper on {!Proof_global}. *)

open Names
open Constr
open Environ

(** {6 ... } *)

(** [solve (SelectNth n) tac] applies tactic [tac] to the [n]th
    subgoal of the current focused proof. [solve SelectAll
    tac] applies [tac] to all subgoals. *)

val solve : ?with_end_tac:unit Proofview.tactic ->
      Goal_select.t -> int option -> unit Proofview.tactic ->
      Proof.t -> Proof.t * bool

(** Option telling if unification heuristics should be used. *)
val use_unification_heuristics : unit -> bool

val refine_by_tactic
  :  name:Id.t
  -> poly:bool
  -> env -> Evd.evar_map
  -> EConstr.types
  -> unit Proofview.tactic
  -> constr * Evd.evar_map
(** A variant of the above function that handles open terms as well.
    Caveat: all effects are purged in the returned term at the end, but other
    evars solved by side-effects are NOT purged, so that unexpected failures may
    occur. Ideally all code using this function should be rewritten in the
    monad. *)
