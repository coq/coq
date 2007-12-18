(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: subproof.mli aspiwack $ *)

(* arnaud: conceptuali-commenter *)
open Term

type subproof 

(* Starts a subproof in a given environement, with initial subgoals
   whose conclusion type is given by a list.
   The subgoals of the returned subproof are in the same order as
   the list of conclusion. *)
val start : Environ.env -> Term.types list -> subproof

(* Initialises a subproof, the argument is a list of environement, 
   conclusion types, and optional names, creating that many initial goals.
   It is a more elaborated version of {!start}. *)
val init : (Environ.env * Term.types * string option) list -> subproof

(* Returns the open goals of the subproof *)
val goals : subproof -> Goal.goal list

(* Returns whether this subproof is finished or not. *)
val finished : subproof -> bool

(* Returns the current value of the subproof return terms *)
val return : subproof -> constr list


(*** Focusing operations ***)

(* type of the contexts allowing to unfocus a focused subgoal *)
type focus_context

(* [focus i j] focuses a subproof on the goals from index [i] to index [j] 
   (inclusive). (i.e. goals number [i] to [j] become the only goals of the
   returned subproof).
   It returns the focus proof, and a context for the focus trace. *)
val focus : int -> int -> subproof -> subproof * focus_context

(* Unfocuses a subproof with respect to a context. *)
val unfocus : focus_context -> subproof -> subproof


(* arnaud: donner un nom à la section *)
(*** ***)

(* Reorders the open goals of the given pointer, according to the 
   permutation *)
val reorder : Permutation.permutation -> subproof -> subproof





(******************************************************************)
(***                                                            ***)
(***                Definition related to tactics               ***)
(***                                                            ***)
(******************************************************************)


type tactic 

(* Transforms a function of type 
   [Evd.evar_defs -> Goal.goal -> Goal.refinement] (i.e.
   a tactic that operates on a single goal) into an actual tactic.
   It operates by iterating the single-tactic from the last goal to 
   the first one. *)
val single_tactic : (Evd.evar_defs -> Goal.goal -> Goal.refinement) -> tactic
