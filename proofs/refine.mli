(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** The primitive refine tactic used to fill the holes in partial proofs. This
    is the recommanded way to write tactics when the proof term is easy to
    write down. Note that this is not the user-level refine tactic defined
    in Ltac which is actually based on the one below. *)

open Proofview

(** {6 The refine tactic} *)

(** Printer used to print the constr which refine refines. *)
val pr_constr :
  (Environ.env -> Evd.evar_map -> Term.constr -> Pp.std_ppcmds) Hook.t

(** {7 Refinement primitives} *)

val refine : ?unsafe:bool -> Constr.t Sigma.run -> unit tactic
(** In [refine ?unsafe t], [t] is a term with holes under some
    [evar_map] context. The term [t] is used as a partial solution
    for the current goal (refine is a goal-dependent tactic), the
    new holes created by [t] become the new subgoals. Exceptions
    raised during the interpretation of [t] are caught and result in
    tactic failures. If [unsafe] is [false] (default is [true]) [t] is
    type-checked beforehand. *)

val refine_one : ?unsafe:bool -> ('a * Constr.t) Sigma.run -> 'a tactic
(** A generalization of [refine] which assumes exactly one goal under focus *)

(** {7 Helper functions} *)

val with_type : Environ.env -> Evd.evar_map ->
  Term.constr -> Term.types -> Evd.evar_map * EConstr.constr
(** [with_type env sigma c t] ensures that [c] is of type [t]
    inserting a coercion if needed. *)

val refine_casted : ?unsafe:bool -> Constr.t Sigma.run -> unit tactic
(** Like {!refine} except the refined term is coerced to the conclusion of the
    current goal. *)
