(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

  (* Old style hyps primitive *)
  val hyps : Evd.evar_map -> goal -> Environ.named_context_val

  (* same as [hyps], but ensures that existential variables are
     normalised. *)
  val nf_hyps : Evd.evar_map -> goal -> Environ.named_context_val

  (* Access to ".evar_concl" *)
  val concl : Evd.evar_map -> goal -> EConstr.constr

  (* Access to ".evar_extra" *)
  val extra : Evd.evar_map -> goal -> Evd.Store.t

  (* Old style mk_goal primitive, returns a new goal with corresponding 
       hypotheses and conclusion, together with a term which is precisely
       the evar corresponding to the goal, and an updated evar_map. *)
  val mk_goal : Evd.evar_map -> 
                         Environ.named_context_val ->
                         EConstr.constr ->
                         Evd.Store.t ->
                         goal * EConstr.constr * Evd.evar_map

  (* Instantiates a goal with an open term *)
  val partial_solution : Evd.evar_map -> goal -> EConstr.constr -> Evd.evar_map

  (* Instantiates a goal with an open term, reusing name of goal for
     second goal *)
  val partial_solution_to : Evd.evar_map -> goal -> goal -> EConstr.constr -> Evd.evar_map

  (* Principal part of the progress tactical *)
  val progress : goal list Evd.sigma -> goal Evd.sigma -> bool

 (* Principal part of tclNOTSAMEGOAL *)
  val same_goal : Evd.evar_map -> goal -> Evd.evar_map -> goal -> bool

  (* Used by the compatibility layer and typeclasses *)
  val nf_evar : Evd.evar_map -> goal -> goal * Evd.evar_map

  (* Goal represented as a type, doesn't take into account section variables *)
  val abstract_type : Evd.evar_map -> goal -> EConstr.types 

end

module Set : sig include Set.S with type elt = goal end
