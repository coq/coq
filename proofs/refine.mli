(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The primitive refine tactic used to fill the holes in partial proofs. This
    is the recommanded way to write tactics when the proof term is easy to
    write down. Note that this is not the user-level refine tactic defined
    in Ltac which is actually based on the one below. *)

open Proofview

(** {6 The refine tactic} *)

(** Printer used to print the constr which refine refines. *)
val pr_constr :
  (Environ.env -> Evd.evar_map -> Constr.constr -> Pp.t) Hook.t

(** {7 Refinement primitives} *)

val refine : typecheck:bool -> (Evd.evar_map -> Evd.evar_map * EConstr.t) -> unit tactic
(** In [refine ~typecheck t], [t] is a term with holes under some
    [evar_map] context. The term [t] is used as a partial solution
    for the current goal (refine is a goal-dependent tactic), the
    new holes created by [t] become the new subgoals. Exceptions
    raised during the interpretation of [t] are caught and result in
    tactic failures. If [typecheck] is [true] [t] is type-checked beforehand. *)

val refine_one : typecheck:bool -> (Evd.evar_map -> Evd.evar_map * ('a * EConstr.t)) -> 'a tactic
(** A variant of [refine] which assumes exactly one goal under focus *)

val generic_refine : typecheck:bool -> ('a * EConstr.t) tactic ->
  Proofview.Goal.t -> 'a tactic
(** The general version of refine. *)

(** {7 Helper functions} *)

val with_type : Environ.env -> Evd.evar_map ->
  EConstr.constr -> EConstr.types -> Evd.evar_map * EConstr.constr
(** [with_type env sigma c t] ensures that [c] is of type [t]
    inserting a coercion if needed. *)

val refine_casted : typecheck:bool -> (Evd.evar_map -> Evd.evar_map * EConstr.t) -> unit tactic
(** Like {!refine} except the refined term is coerced to the conclusion of the
    current goal. *)

(** {7 Unification constraint handling} *)

val solve_constraints : unit tactic
(** Solve any remaining unification problems, applying heuristics. *)
