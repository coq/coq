(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: proof.mli aspiwack $ *)

(* This module implements the actual proof datatype. It enforces strong
   invariants, and it is the only module that should access the module
   Subproof.
   Actually from outside the proofs/ subdirectory, this is the only module
   that should be used directly. *)

open Term

(* Type of a proof of return type ['a]. *)
type 'a proof


(* Interpretes the Undo command. *)
val undo : 'a proof -> unit


(* focus command (focuses on the [i]th subgoal) *)
(* there could also, easily be a focus-on-a-range tactic, is there 
   a need for it? *)
val focus : int -> 'a proof -> unit

(* unfocus command.
   Fails if the proof is not focused. *)
val unfocus : 'a proof -> unit


(*** ***)
(* arnaud: cette section, si courte qu'elle est, mérite probablement un titre *)

val run_tactic : Subproof.tactic -> 'a proof -> unit

(*** **)
(* arnaud: hack pour debugging *)
val start_proof : 
  Names.identifier -> 'a (*goal_kind*) -> Environ.named_context_val -> constr
    -> 'b (*declaration_hook*) -> unit

val pr_subgoals : (string option -> Evd.evar_map -> Goal.goal list -> Pp.std_ppcmds) -> Pp.std_ppcmds

val db_run_tactic_on : int -> Subproof.tactic -> unit

val hide_interp : (unit proof -> Tacexpr.raw_tactic_expr -> 'a option -> Subproof.tactic) -> Tacexpr.raw_tactic_expr -> 'a option -> Subproof.tactic

(* arnaud:fonction très temporaire*)
val subproof_of : 'a proof -> Subproof.subproof
