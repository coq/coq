(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Module defining the last essential tiles of interactive proofs.
   The features of the Proof module are undoing and focusing.
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
     "focus kind" and a "focus condition" (in practice, and for modularity,
     the focus kind is actually stored inside the condition). To unfocus, one
     needs to know the focus kind, and the condition (for instance "no condition" or
     the proof under focused must be complete) must be met.
   - Undo: since proofviews and focus stacks are immutable objects, 
     it could suffice to hold the previous states, to allow to return to the past.
     However, we also allow other modules to do actions that can be undone.
     Therefore the undo stack stores action to be ran to undo.
*)

open Term

(* Type of a proof. *)
type proof


(*** General proof functions ***)

val start : (Environ.env * Term.types) list -> proof

(* Returns [true] is the considered proof is completed, that is if no goal remain
    to be considered (this does not require that all evars have been solved). *)
val is_done : proof -> bool

(* Returns the list of partial proofs to initial goals. *)
val partial_proof : proof -> Term.constr list

(* Returns the proofs (with their type) of the initial goals.
    Raises [UnfinishedProof] is some goals remain to be considered.
    Raises [HasUnresolvedEvar] if some evars have been left undefined. *)
exception UnfinishedProof
exception HasUnresolvedEvar
val return : proof -> (Term.constr * Term.types) list

(* Interpretes the Undo command. Raises [EmptyUndoStack] if 
    the undo stack is empty. *)
exception EmptyUndoStack
val undo : proof -> unit

(* Adds an undo effect to the undo stack. Use it with care, errors here might result
    in inconsistent states. *)
val add_undo : (unit -> unit) -> proof -> unit

(*** Focusing actions ***)

(* [focus_kind] is the type used by focusing and unfocusing
    commands to synchronise. Focusing and unfocusing commands use
    a particular focus_kind, and if they don't match, the unfocusing command
    will fail. *)
type focus_kind
val new_focus_kind : unit -> focus_kind

(* To be authorized to unfocus one must meet the condition prescribed by
    the action which focused.*)
type focus_condition 
(* [no_cond] only checks that the unfocusing command uses the right
    [focus_kind]. *)
val no_cond : focus_kind -> focus_condition
(* [done_cond] checks that the unfocusing command uses the right [focus_kind]
    and that the focused proofview is complete. *)
val done_cond : focus_kind -> focus_condition

(* focus command (focuses on the [i]th subgoal) *)
(* there could also, easily be a focus-on-a-range tactic, is there 
   a need for it? *)
val focus : focus_condition -> int -> proof -> unit

exception FullyUnfocused
(* Unfocusing command.
   Raises [FullyUnfocused] if the proof is not focused. *)
val unfocus : focus_kind -> proof -> unit

(* returns [true] if there is no goal under focus. *)
val no_focused_goal : proof -> bool

(*** Function manipulation proof extra informations ***)

val get_proof_info : proof -> Store.t

val set_proof_info : Store.t -> proof -> unit


(*** Endline tactic ***)

(* Sets the tactic to be used when a tactic line is closed with [...] *)
val set_endline_tactic : unit Proofview.tactic -> proof -> unit

val with_end_tac : proof -> unit Proofview.tactic -> unit Proofview.tactic

(*** Tactics ***)

val run_tactic : Environ.env -> unit Proofview.tactic -> proof -> unit


(*** Compatibility layer with <=v8.2 ***)
module V82 : sig
  val subgoals : proof -> Goal.goal list Evd.sigma

  (* All the subgoals of the proof, including those which are not focused. *)
  val background_subgoals : proof -> Goal.goal list Evd.sigma

  val get_initial_conclusions : proof -> Term.types list 

  val depth : proof -> int 

  val top_goal : proof -> Goal.goal Evd.sigma

  (* Implements the Existential command *)
  val instantiate_evar : int -> Topconstr.constr_expr -> proof -> unit
end
