(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: proofview.mli aspiwack $ *)

(* The proofview datastructure is a pure datastructure underlying the notion
   of proof (namely, a proof is a proofview which can evolve and has safety
   mechanisms attached).
   The general idea of the structure is that it is composed of a chemical
   solution: an unstructured bag of stuff which has some relations with 
   one another, which represents the various subnodes of the proof, together
   with a comb: a datastructure that gives order to some of these nodes, 
   namely the open goals. 
   The natural candidate for the solution is an {!Evd.evar_defs}, that is
   a calculus of evars. The comb is then a list of goals (evars wrapped 
   with some extra information, like possible name anotations).
   There is also need of a list of the evars which initialised the proofview
   to be able to return information about the proofview. *)

open Term

type proofview 

(* Initialises a proofview, the argument is a list of environement, 
   conclusion types, and optional names, creating that many initial goals. *)
val init : (Environ.env * Term.types * string option) list -> proofview

(* Returns the open goals of the proofview *)
val goals : proofview -> Goal.goal list

(* Returns whether this proofview is finished or not.That is,
   if it has empty subgoals in the comb. There could still be unsolved
   subgoaled, but they would then be out of the view, focused out. *)
val finished : proofview -> bool

(* Returns the current value of the proofview return terms *)
(* arnaud: synchroniser d'une façon ou d'une autre sur le commentaire
   dans le .ml *)
val return : proofview -> constr list


(*** Focusing operations ***)

(* Type of the object which allow to unfocus a view.*)
type focus_context

(* [focus i j] focuses a proofview on the goals from index [i] to index [j] 
   (inclusive). (i.e. goals number [i] to [j] become the only goals of the
   returned proofview).
   It returns the focus proof, and a context for the focus trace. *)
val focus : int -> int -> proofview -> proofview * focus_context

(* Unfocuses a proofview with respect to a context. *)
val unfocus : focus_context -> proofview -> proofview



(*** Exceptions of the proof engine ***)

(* arnaud: il faudra voir si elles ont toutes du sens, et si la classification
           est encore à l'ordre du jour. Peut-être même faut-il les mettre
           dans goal.ml. *)
type refiner_error =
  (* Errors raised by the refiner *)
  | BadType of constr * constr * constr
  | OccurMeta of constr
  | OccurMetaGoal of constr
  | CannotApply of constr * constr
  | NotWellTyped of constr
  | NonLinearProof of constr

  (* Errors raised by the tactics *)
  | IntroNeedsProduct
  | DoesNotOccurIn of constr * Names.identifier

exception RefinerError of refiner_error

val catchable_exception : exn -> bool

(******************************************************************)
(***                                                            ***)
(***                Definition related to tactics               ***)
(***                                                            ***)
(******************************************************************)


(* The tactic monad:
   - Tactics are objects which apply a transformation to all
     the subgoals of the current view at the same time. By opposed
     to the old vision of applying it to a single goal. It mostly 
     allows to consider tactic like [reorder] to reorder the goals
     in the current view (which might be useful for the tactic designer)
     (* spiwack: the ordering of goals, though, is actually very
        brittle. It would be much more interesting to find a more
        robust way to adress goals, I have no idea at this time 
        though*) 
     or global automation tactic for dependent subgoals (instantiating
     an evar has influences on the other goals of the proof in progress,
     not being able to take that into account causes the current eauto
     tactic to fail on some instances where it could succeed).
   - Tactics are a monad ['a tactic], in a sense a tactic can be 
     seens as a function (without argument) which returns a value
     of type 'a and modifies the environement (in our case: the view).
     Tactics of course have arguments, but these are given at the 
     meta-level as OCaml functions.
     Most tactics in the sense we are used to return [ () ], that is
     no really interesting values. But some might, to pass information 
     around; for instance [Proofview.freeze] allows to store a certain
     goal sensitive value "at the present time" (which means, considering the
     structure of the dynamics of proofs, [Proofview.freeze s] will have,
     for every current goal [gl], and for any of its descendent [g'] in 
     the future the same value in [g'] that in [gl]). 
     (* spiwack: I don't know how much all this relates to F. Kirchner and 
        C. Muñoz. I wasn't able to understand how they used the monad
        structure in there developpement.
     *)
     The tactics seen in Coq's Ltac are (for now at least) only 
     [unit tactic], the return values are kept for the OCaml toolkit.
     The operation or the monad are [Proofview.tclIDTAC] (which is the 
     "return" of the tactic monad) [Proofview.tclBIND] (which is
     the "bind") and [Proofview.tclTHEN] (which is a specialized
     bind on unit-returning tactics).
*)


type +'a tactic 

(* arnaud: exportée pour Proof. 
  Abandon de tactic failure, on revient à Error, trop pénible de changer
  tout le code existant, et c'est essentiellement cosmétique.
(* exception which represent a failure in a command *)
exception TacticFailure of Pp.std_ppcmds
  *)

(* [fail s] raises [TacticFailure s].  *)
val fail : Pp.std_ppcmds -> 'a

(* Applies a tactic to the current proofview. *)
val apply : Environ.env -> 'a tactic -> proofview -> proofview


(* A [proof_step Goal.sensitive] can be seen as a tactic by
   contatenating its value inside each individual goal of the
   current view. *)
val tactic_of_sensitive_proof_step : Goal.proof_step Goal.sensitive -> 
                                     unit tactic

(* arnaud: abandonnée en faveur de "sensitive_tactic"
(* arnaud: à commenter, ainsi que dans le .ml *)
val goal_tactic_of_tactic : unit tactic -> Goal.proof_step Goal.sensitive
*)

(* This tactical is included for compatibitility with the previous
   way of building tactic. It corresponds to a very natural way of building
   tactic according to it, far less now, though it may be unavoidable (
   if we want to really get rid of it, it might be necessary to have
   some clever ways or "focusing" or such).
   It takes a [unit tactic Goal.sensitive] that is a value that becomes
   a tactic inside a goal and make it a tactic by applying it individually
   to a view containing a single goal (it peeks inside the goal to figure
   which tactic it should apply, then applies it). *)
val sensitive_tactic : unit tactic Goal.sensitive -> unit tactic



(*** tacticals ***)

(* A special exception for levels for the Fail tactic *)
exception FailError of int * Pp.std_ppcmds

(* Fail if there is some goal *)
val tclFAIL : Pp.std_ppcmds -> unit tactic

(* Fail if there is no goal *)
val tclEMPTY : Pp.std_ppcmds -> unit tactic

(* Interpetes the ";" (semicolon) of Ltac.
   As a monadic operation, it's a specialized "bind"
   on unit-returning tactic (meaning "there is no value to bind") *)
val tclTHEN : unit tactic -> 'a tactic -> 'a tactic

(* Bind operation of the tactic monad.*)
(* For now it is used only for the OCaml tactic toolkit, no 
   equivalent in Ltac. *)
val tclBIND : 'a tactic -> ('a -> 'b tactic) -> 'b tactic

(* [tclIGNORE t] has the same operational content as [t],
   but drops the value at the end. *)
val tclIGNORE : 'a tactic -> unit tactic


(* Focuses a tactic at a single subgoal, found by it's index. *)
(* There could easily be such a tactical for a range of goals. *)
val tclFOCUS : int -> unit tactic -> unit tactic

(* Makes a list of tactic into a tactic (interpretes the [ | ] construct).
   It applies the tactics from the last one to the first one.
   Fails on the proofs with a number of subgoals not matching the length
   of the list.*)
val tclLIST : unit tactic list -> unit tactic

(* arnaud: syntax de la construction ? *)
(* Interpretes the [ t1 | t2 | ... | t3 | t4 ] construct.
   That is it applies [t1] to the first goal, [t3] and [t4] to the 
   last two, and [t2] to the rest (this generalizes to two lists
   of tactics and a tactic to be repeated.
   As in the other constructions, the tactics are applied from the last
   goal to the first. *)
val tclEXTEND : unit tactic list -> unit tactic -> unit tactic list -> unit tactic

(* Interpretes the "solve" tactical. *)
val tclSOLVE : 'a tactic -> 'a tactic


(* Interpretes the or-else tactical. (denoted "||") *)
val tclORELSE : unit tactic -> unit tactic -> unit tactic

(* Interpretes the repeat tactical *)
val tclREPEAT : unit tactic -> unit tactic


(*** tactics ***)

(* Prototype to the [idtac] tactic, also plays the role of 
   "return" in the tactic monad *)
val tclIDTAC : 'a -> 'a tactic

(* Freezes a goal sensitive value to its "current value".
   Its value will be the same inside a goal than inside its 
   ancestor among current goal.
   If there is no such parent then it raises an error to evaluate
   it, better be careful not to use it after unfocusing. *)
(* arnaud: I believe it raises a simple tactic failure when
   incorrectly evaluated. *)
val freeze : 'a Goal.sensitive -> 'a Goal.sensitive tactic

(* Reorders the open goals of the given pointer, according to the 
   permutation *)
val reorder : Permutation.permutation -> unit tactic


(*** **)
(* arnaud: hack pour debugging *)
val pr_subgoals : proofview -> (string option -> Evd.evar_map -> Goal.goal list -> Pp.std_ppcmds) -> Pp.std_ppcmds

val defs_of : proofview -> Evd.evar_defs
