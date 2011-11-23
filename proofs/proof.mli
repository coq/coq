(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
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

(* Returns [true] if the considered proof is completed, that is if no goal remain
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
    in inconsistent states.
   An undo effect is meant to undo an effect on a proof (a canonical example
   of which is {!Proofglobal.set_proof_mode} which changes the current parser for
   tactics). Make sure it will work even if the effects have been only partially
   applied at the time of failure. *)
val add_undo : (unit -> unit) -> proof -> unit

(*** Focusing actions ***)

(* ['a focus_kind] is the type used by focusing and unfocusing
    commands to synchronise. Focusing and unfocusing commands use
    a particular ['a focus_kind], and if they don't match, the unfocusing command
    will fail.
    When focusing with an ['a focus_kind], an information of type ['a] is
    stored at the focusing point. An example use is the "induction" tactic
    of the declarative mode where sub-tactics must be aware of the current
    induction argument. *)
type 'a focus_kind
val new_focus_kind : unit -> 'a focus_kind

(* To be authorized to unfocus one must meet the condition prescribed by
    the action which focused.
    Conditions always carry a focus kind, and inherit their type parameter
    from it.*)
type 'a focus_condition 
(* [no_cond] only checks that the unfocusing command uses the right
    [focus_kind].
   If [loose_end] (default [false]) is [true], then if the [focus_kind]
   doesn't match, then unfocusing can occur, provided it unfocuses
   an earlier focus.
   For instance bullets can be unfocused in the following situation
   [{- solve_goal. }] because they use a loose-end condition. *)
val no_cond : ?loose_end:bool -> 'a focus_kind -> 'a focus_condition
(* [done_cond] checks that the unfocusing command uses the right [focus_kind]
    and that the focused proofview is complete.
   If [loose_end] (default [false]) is [true], then if the [focus_kind]
   doesn't match, then unfocusing can occur, provided it unfocuses
   an earlier focus.
   For instance bullets can be unfocused in the following situation
   [{ - solve_goal. }] because they use a loose-end condition.  *)
val done_cond : ?loose_end:bool -> 'a focus_kind -> 'a focus_condition

(* focus command (focuses on the [i]th subgoal) *)
(* spiwack: there could also, easily be a focus-on-a-range tactic, is there 
   a need for it? *)
val focus : 'a focus_condition -> 'a -> int -> proof -> unit

exception FullyUnfocused
exception CannotUnfocusThisWay
(* Unfocusing command.
   Raises [FullyUnfocused] if the proof is not focused.
   Raises [CannotUnfocusThisWay] if the proof the unfocusing condition
     is not met. *)
val unfocus : 'a focus_kind -> proof -> unit

(* [get_at_focus k] gets the information stored at the closest focus point
    of kind [k].
    Raises [NoSuchFocus] if there is no focus point of kind [k]. *)
exception NoSuchFocus
val get_at_focus : 'a focus_kind -> proof -> 'a

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


(*** Transactions ***)

(* A transaction chains several commands into a single one. For instance,
   a focusing command and a tactic. Transactions are such that if
   any of the atomic action fails, the whole transaction fails.

   During a transaction, the undo visible undo stack is constituted only
   of the actions performed done during the transaction.

   [transaction p f] can be called on an [f] using, itself, [transaction p].*)
val transaction : proof -> (unit -> unit) -> unit


(*** Commands ***)

val in_proof : proof -> (Evd.evar_map -> 'a) -> 'a

(*** Compatibility layer with <=v8.2 ***)
module V82 : sig
  val subgoals : proof -> Goal.goal list Evd.sigma

  (* All the subgoals of the proof, including those which are not focused. *)
  val background_subgoals : proof -> Goal.goal list Evd.sigma

  val get_initial_conclusions : proof -> Term.types list 

  val depth : proof -> int 

  val top_goal : proof -> Goal.goal Evd.sigma
  
  (* returns the existential variable used to start the proof *)
  val top_evars : proof -> Evd.evar list

  (* Implements the Existential command *)
  val instantiate_evar : int -> Topconstr.constr_expr -> proof -> unit
end
