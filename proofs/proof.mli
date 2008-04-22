(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: proof.mli aspiwack $ *)

(* Module defining the last essential tiles of interractive proofs.
   The focuses of the Proof module are undoing and focusing.
   A proof is a mutable object, it contains a proofview, and some information
   to be able to undo actions, and to unfocus the current view. All three
   of these being meant to evolve.
   - Proofview: a proof is primarily the data of the current view.
     That which is shown to the user (as a remainder, a proofview
     is mainly the logical state of the proof, together with the
     currently focused goals).
   - Focus: a proof has a focus stack: the top of the stack contains
     the context in which to unfocus the current view to a view focused
     with the rest of the stack.
     In addition, this contains, for each of the focus context,  a 
     "focus kind". This kind represents the intention of the focus.
     In particular, by giving ourselves a "Rigid" focus kind, that
     disallows unfocusing while there are still open goals in the 
     current view, we can implement the Begin Subproof/End Subproof
     feature.
   - Undo: since proofviews and focus stacks are immutable objects, 
     it suffices to hold the previous states, to allow to return to past.
*)

open Term

(* Type of a proof. *)
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

val run_tactic : Environ.env -> 'a Proofview.tactic -> proof -> unit

(*** **)
(* arnaud: hack pour debugging *)

val pr_subgoals : proof -> (string option -> Evd.evar_map -> Goal.goal list -> Pp.std_ppcmds) -> Pp.std_ppcmds

(* arnaud:
val hide_interp : (proof -> Tacexpr.raw_tactic_expr -> 'a option -> Proofview.tactic) -> Tacexpr.raw_tactic_expr -> 'a option -> Proofview.tactic
*)

(* arnaud:fonction très temporaire*)
val proofview_of : proof -> Proofview.proofview
