(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: goal.mli aspiwack $ *)

(* This module implements the abstract interface to goals *)


type goal

val build : ?name:string -> Evd.evar -> goal

val is_defined : Evd.evar_map -> goal -> bool


(*** Refine tactic ***)

(* return type of the Goal.refine function *)
(* it contains the new subgoals to produce, a function to reconstruct
   the proof to the current goal knowing the result of the subgoals,
   the type and constraint information about the evars of the proof
   (which has been extended with new ones), and the definitions of
   the evars to instantiate *)
type refinement = { subgoals: goal list ;
                    new_defs: Evd.evar_defs}


(* arnaud: à commenter un brin (comme le .ml quoi) *)
val refine : Evd.evar_defs -> Environ.env -> bool -> Rawterm.rawconstr -> goal -> refinement


(* arnaud: à remplacer par un print 
(* This function returns a new goal where the evars have been
   instantiated according to an evar_map *)
val instantiate : Evd.evar_map -> goal -> goal
*)
