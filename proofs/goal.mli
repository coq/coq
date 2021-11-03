(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module implements the abstract interface to goals. Most of the code
    here is useless and should be eventually removed. Consider using
    {!Proofview.Goal} instead. *)

type goal = Evar.t

(* Gives a unique identifier to each goal. The identifier is
   guaranteed to contain no space. *)
val uid : goal -> string

(* Debugging help *)
val pr_goal : goal -> Pp.t

(* Layer to implement v8.2 tactic engine ontop of the new architecture.
   Types are different from what they used to be due to a change of the
   internal types. *)
module V82 : sig

  (* Old style env primitive *)
  val env : Evd.evar_map -> goal -> Environ.env
  [@@ocaml.deprecated "Use Evd.evar_filtered_env"]

  (* Old style hyps primitive *)
  val hyps : Evd.evar_map -> goal -> Environ.named_context_val
  [@@ocaml.deprecated "Use Evd.evar_filtered_hyps"]

  (* same as [hyps], but ensures that existential variables are
     normalised. *)
  val nf_hyps : Evd.evar_map -> goal -> Environ.named_context_val
  [@@ocaml.deprecated "Use Evd.evar_filtered_hyps"]

  (* Access to ".evar_concl" *)
  val concl : Evd.evar_map -> goal -> EConstr.constr
  [@@ocaml.deprecated "Use Evd.evar_concl"]

  (* Old style mk_goal primitive, returns a new goal with corresponding
       hypotheses and conclusion, together with a term which is precisely
       the evar corresponding to the goal, and an updated evar_map. *)
  val mk_goal : Evd.evar_map ->
                         Environ.named_context_val ->
                         EConstr.constr ->
                         goal * EConstr.constr * Evd.evar_map
  [@@ocaml.deprecated "Use the Refine.refine primitive and related API"]

  (* Instantiates a goal with an open term *)
  val partial_solution : Environ.env -> Evd.evar_map -> goal -> EConstr.constr -> Evd.evar_map
  [@@ocaml.deprecated "Use Refine.refine"]

  (* Used by the compatibility layer and typeclasses *)
  val nf_evar : Evd.evar_map -> goal -> goal * Evd.evar_map
  [@@ocaml.deprecated "This should be the identity now"]

end

module Set = Evar.Set
