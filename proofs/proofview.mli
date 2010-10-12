(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* The proofview datastructure is a pure datastructure underlying the notion
   of proof (namely, a proof is a proofview which can evolve and has safety
   mechanisms attached).
   The general idea of the structure is that it is composed of a chemical
   solution: an unstructured bag of stuff which has some relations with 
   one another, which represents the various subnodes of the proof, together
   with a comb: a datastructure that gives order to some of these nodes, 
   namely the open goals. 
   The natural candidate for the solution is an {!Evd.evar_map}, that is
   a calculus of evars. The comb is then a list of goals (evars wrapped 
   with some extra information, like possible name anotations).
   There is also need of a list of the evars which initialised the proofview
   to be able to return information about the proofview. *)

open Term

type proofview 

(* Initialises a proofview, the argument is a list of environement, 
   conclusion types, creating that many initial goals. *)
val init : (Environ.env * Term.types) list -> proofview

(* Returns whether this proofview is finished or not.That is,
   if it has empty subgoals in the comb. There could still be unsolved
   subgoaled, but they would then be out of the view, focused out. *)
val finished : proofview -> bool

(* Returns the current value of the proofview partial proofs. *)
val return : proofview -> (constr*types) list


(*** Focusing operations ***)

(* [IndexOutOfRange] occurs in case of malformed indices
   with respect to list lengths. *)
exception IndexOutOfRange

(* Type of the object which allow to unfocus a view.*)
type focus_context

(* [focus i j] focuses a proofview on the goals from index [i] to index [j] 
   (inclusive). (i.e. goals number [i] to [j] become the only goals of the
   returned proofview).
   It returns the focus proof, and a context for the focus trace. *)
val focus : int -> int -> proofview -> proofview * focus_context

(* Unfocuses a proofview with respect to a context. *)
val unfocus : focus_context -> proofview -> proofview

(* The tactic monad:
   - Tactics are objects which apply a transformation to all
     the subgoals of the current view at the same time. By opposed
     to the old vision of applying it to a single goal. It mostly 
     allows to consider tactic like [reorder] to reorder the goals
     in the current view (which might be useful for the tactic designer)
     (* spiwack: the ordering of goals, though, is actually rather
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

(* Applies a tactic to the current proofview. *)
val apply : Environ.env -> 'a tactic -> proofview -> proofview

(*** tacticals ***)

(* Unit of the tactic monad *)
val tclUNIT : 'a -> 'a tactic

(* Bind operation of the tactic monad *)
val tclBIND : 'a tactic -> ('a -> 'b tactic) -> 'b tactic

(* Interpetes the ";" (semicolon) of Ltac.
   As a monadic operation, it's a specialized "bind"
   on unit-returning tactic (meaning "there is no value to bind") *)
val tclTHEN : unit tactic -> 'a tactic -> 'a tactic

(* [tclIGNORE t] has the same operational content as [t],
   but drops the value at the end. *)
val tclIGNORE : 'a tactic -> unit tactic

(* [tclOR t1 t2 = t1] if t1 succeeds and [tclOR t1 t2 = t2] if t2 fails. 
    No interleaving at this point. *)
val tclOR : 'a tactic -> 'a tactic -> 'a tactic

(* [tclZERO] always fails *)
val tclZERO : exn -> 'a tactic

(* Focuses a tactic at a range of subgoals, found by their indices. *)
val tclFOCUS : int -> int -> 'a tactic -> 'a tactic

(* Dispatch tacticals are used to apply a different tactic to each goal under
    consideration. They come in two flavours:
    [tclDISPATCH] takes a list of [unit tactic]-s and build a [unit tactic].
    [tclDISPATCHS] takes a list of ['a sensitive tactic] and returns and returns
    and ['a sensitive tactic] where the ['a sensitive] interpreted in a goal [g]
    corresponds to that of the tactic which created [g].
    It is to be noted that the return value of [tclDISPATCHS ts] makes only
    sense in the goals immediatly built by it, and would cause an anomaly
    is used otherwise. *)
val tclDISPATCH : unit tactic list -> unit tactic
val tclDISPATCHS : 'a Goal.sensitive tactic list -> 'a Goal.sensitive tactic

(* [tclEXTEND b r e] is a variant to [tclDISPATCH], where the [r] tactic
    is "repeated" enough time such that every goal has a tactic assigned to it
    ([b] is the list of tactics applied to the first goals, [e] to the last goals, and [r]
    is applied to every goal in between. *)
val tclEXTEND : unit tactic list -> unit tactic -> unit tactic list -> unit tactic

(* A sort of bind which takes a [Goal.sensitive] as a first argument, 
    the tactic then acts on each goal separately.
    Allows backtracking between goals. *)
val tclGOALBIND : 'a Goal.sensitive -> ('a -> 'b Goal.sensitive tactic) -> 'b Goal.sensitive tactic
val tclGOALBINDU : 'a Goal.sensitive -> ('a -> unit tactic) -> unit tactic

(* [tclSENSITIVE] views goal-type tactics as a special kind of tactics.*)
val tclSENSITIVE : Goal.subgoals Goal.sensitive -> unit tactic 

(* Notations for building tactics. *)
module Notations : sig
  (* Goal.bind *)
  val (>-) : 'a Goal.sensitive -> ('a -> 'b Goal.sensitive) -> 'b Goal.sensitive
  (* tclGOALBINDU *)
  val (>>-) : 'a Goal.sensitive -> ('a -> unit tactic) -> unit tactic
  (* tclGOALBIND *)
  val (>>--) : 'a Goal.sensitive -> ('a -> 'b Goal.sensitive tactic) -> 'b Goal.sensitive tactic

  (* tclBIND *)
  val (>=) : 'a tactic -> ('a -> 'b tactic) -> 'b tactic

  (* [(>>=)] (and its goal sensitive variant [(>>==)]) "binds" in one step the
      tactic monad and the goal-sensitive monad.
      It is strongly advised to use it everytieme an ['a Goal.sensitive tactic]
      needs a bind, since it usually avoids to delay the interpretation of the
      goal sensitive value to a location where it does not make sense anymore. *)
  val (>>=) : 'a Goal.sensitive tactic -> ('a -> unit tactic) -> unit tactic
  val (>>==) : 'a Goal.sensitive tactic -> ('a -> 'b Goal.sensitive tactic) -> 'b Goal.sensitive tactic

  (* tclTHEN *)
  val (<*>) : unit tactic -> 'a tactic -> 'a tactic
  (* tclOR *)
  val (<+>) : 'a tactic -> 'a tactic -> 'a tactic
end

(*** Compatibility layer with <= 8.2 tactics ***)
module V82 : sig
  type tac = Goal.goal Evd.sigma -> Goal.goal list Evd.sigma 
  val tactic : tac -> unit tactic

  val has_unresolved_evar : proofview -> bool

  (* Returns the open goals of the proofview together with the evar_map to 
     interprete them. *)
  val goals : proofview -> Goal.goal list Evd.sigma

  val top_goals : proofview -> Goal.goal list Evd.sigma
    
  (* Implements the Existential command *)
  val instantiate_evar : int -> Topconstr.constr_expr -> proofview -> proofview

  (* spiwack: [purify] might be useful while writing tactics manipulating exception 
     explicitely or from the [V82] submodule (neither being advised, though *)
  val purify : 'a tactic -> 'a tactic
end
