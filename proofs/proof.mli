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

(* arnaud: kill death kill, sauf run_tactic qui est juste à modifier 

(* Exception which represents a failure in a tactic.
   May be caught by the "try" tactical for instance. *)
exception TacticFailure of Pp.std_ppcmds

(* Function to raise a [TacticFailure]. *)
val fail : Pp.std_ppcmds -> 'a


(* Type of the tactics *)
(* arnaud: compléter les commentaires *)
type tactic

(* Executes a tactic on a proof *)
val run_tactic : tactic -> 'a proof -> unit


(* Internalizes a subproof-level tactic *)
val internalize : Subproof.tactic -> tactic 

(* Interpretes the ";" (semicolon) from the tactic scripts *)
val tac_then : tactic -> tactic -> tactic
*)
