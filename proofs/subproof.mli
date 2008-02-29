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





(******************************************************************)
(***                                                            ***)
(***                Definition related to tactics               ***)
(***                                                            ***)
(******************************************************************)


type tactic 

(* arnaud: exportée pour Proof. *)
(* exception which represent a failure in a command *)
exception TacticFailure of Pp.std_ppcmds

(* [fail s] raises [TacticFailure s].  *)
val fail : Pp.std_ppcmds -> 'a

(* Applies a tactic to the current subproof. *)
val apply : Environ.env -> tactic -> subproof -> subproof

(* arnaud: à recommenter *)
(* Transforms a function of type 
   [Evd.evar_defs -> Goal.goal -> Goal.refinement] (i.e.
   a tactic that operates on a single goal) into an actual tactic.
   It operates by iterating the single-tactic from the last goal to 
   the first one. *)
val tactic_of_goal_tactic : Goal.tactic -> tactic

(* arnaud: à commenter, ainsi que dans le .ml *)
val goal_tactic_of_tactic : tactic -> Goal.tactic


(* Focuses a tactic at a single subgoal, found by it's index. *)
(* There could easily be such a tactical for a range of goals. *)
val choose_one : int -> tactic -> tactic

(* Makes a list of tactic into a tactic (interpretes the [ | ] construct).
   It applies the tactics from the last one to the first one.
   Fails on the proofs with a number of subgoals not matching the length
   of the list.*)
val list_of_tactics : tactic list -> tactic

(* arnaud: syntax de la construction ? *)
(* Interpretes the [ t1 | t2 | ... | t3 | t4 ] construct.
   That is it applies [t1] to the first goal, [t3] and [t4] to the 
   last two, and [t2] to the rest (this generalizes to two lists
   of tactics and a tactic to be repeated.
   As in the other constructions, the tactics are applied from the last
   goal to the first. *)
val extend_list_of_tactics : tactic list -> tactic -> tactic list -> tactic



(*** tacticals ***)

(* Interpetes the ";" (semicolon) of Ltac. *)
val tclTHEN : tactic -> tactic -> tactic

(* Interpretes the "solve" tactical. *)
val tclSOLVE : tactic -> tactic


(* Interpretes the or-else tactical. (denoted "||") *)
val tclORELSE : tactic -> tactic -> tactic

(* Interpretes the repeat tactical *)
val tclREPEAT : tactic -> tactic


(*** tactics ***)

(* Reorders the open goals of the given pointer, according to the 
   permutation *)
val reorder : Permutation.permutation -> tactic

(* [idtac] tactic *)
val idtac : string option -> tactic


(*** **)
(* arnaud: hack pour debugging *)
val pr_subgoals : subproof -> (string option -> Evd.evar_map -> Goal.goal list -> Pp.std_ppcmds) -> Pp.std_ppcmds

val defs_of : subproof -> Evd.evar_defs
