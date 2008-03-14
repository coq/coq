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
type proof


(*** General proof functions ***)

val start : (Environ.env * Term.types * string option) list -> 
            (constr list -> Decl_kinds.proof_end -> unit) -> 
            proof 

(* arnaud: commenter*)
val is_done : proof -> bool

(* arnaud: commenter*)
val return : proof -> Decl_kinds.proof_end -> unit


(* Interpretes the Undo command. *)
val undo : proof -> unit


(* focus command (focuses on the [i]th subgoal) *)
(* there could also, easily be a focus-on-a-range tactic, is there 
   a need for it? *)
val focus : int -> proof -> unit

(* unfocus command.
   Fails if the proof is not focused. *)
val unfocus : proof -> unit


(*** ***)
(* arnaud: cette section, si courte qu'elle est, mérite probablement un titre *)

val run_tactic : Environ.env -> Subproof.tactic -> proof -> unit

(*** **)
(* arnaud: hack pour debugging *)

val pr_subgoals : proof -> (string option -> Evd.evar_map -> Goal.goal list -> Pp.std_ppcmds) -> Pp.std_ppcmds

(* arnaud:
val hide_interp : (proof -> Tacexpr.raw_tactic_expr -> 'a option -> Subproof.tactic) -> Tacexpr.raw_tactic_expr -> 'a option -> Subproof.tactic
*)

(* arnaud:fonction très temporaire*)
val subproof_of : proof -> Subproof.subproof
