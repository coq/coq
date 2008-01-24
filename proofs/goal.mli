(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: goal.mli aspiwack $ *)

(* This module implements the abstract interface to goals *)


type goal

(*arnaud: virer build quand on aura trouvé une meilleure primitive
          pour Subproof.init. *)
val build : ?name:string -> Evd.evar -> goal 

val is_defined : Evd.evar_map -> goal -> bool


(* arnaud: mieux commenter *)
(* invariant : [e] must exist in [em] *)
val content : Evd.evar_map -> goal -> Evd.evar_info

(*** Goal tactics ***)


(* return type of the execution of goal tactics *)
(* it contains the new subgoals to produce, and the definitions of
   the evars to instantiate *)
type refinement = { subgoals: goal list ;
                    new_defs: Evd.evar_defs}

(* type of the base elements of the goal API.*)
type 'a expression

(* type of the goal tactics*)
type tactic = refinement expression

val run : tactic -> Evd.evar_defs -> goal -> refinement


(* arnaud: à commenter un brin (comme le .ml quoi) *)
val refine : Environ.env -> bool -> Rawterm.rawconstr -> tactic


(*arnaud: commenter plus sans doute. Pareil dans le .ml *)
(* Implements the clear tactics *)
val clear : Names.identifier list -> tactic


(*** Expressions & Tacticals ***)


(* The following combinators allow to construct tactical expressions 
   for reasoning abstractly on subgoals. As one can see in the 
   [run] function, only the tactics are extractible.
   This allows intermediate values never to be exposed, and
   hopefully prevent the implementation details from leaking inside 
   the code. *)
(* Note that this naturally builds a monad (see Haskell wiki for tutorial).
   There is pa_monad camlp4 extension which gives syntax facilities
   for monads, if using camlp4 in Coq's source code becomes an opportunity
   then it could be an idea to integrate pa_monad. *)


(* if then else on expressions *)
val cond : bool expression -> ~thn:'a expression -> 
                              ~els:'a expression ->  'a expression

(* monadic bind on expressions *)
val bind : 'a expression -> ('a -> 'b expression) -> 'b expression

(* monadic return on expressions *)
val return : 'a -> 'a expression

(* arnaud: à remplacer par un print 
(* This function returns a new goal where the evars have been
   instantiated according to an evar_map *)
val instantiate : Evd.evar_map -> goal -> goal
*)
