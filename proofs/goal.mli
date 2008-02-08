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

val run : tactic -> Environ.env -> Evd.evar_defs -> goal -> refinement


(* arnaud: à commenter un brin (comme le .ml quoi) *)
val refine : bool -> Rawterm.rawconstr -> tactic


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
val cond : bool expression -> thn:'a expression -> 
                              els:'a expression ->  'a expression

(* monadic bind on expressions *)
val bind : 'a expression -> ('a -> 'b expression) -> 'b expression

(* monadic return on expressions *)
val return : 'a -> 'a expression

(* changes a list of expressions into an list expression *)
val expr_of_list : 'a expression list -> 'a list expression

(* arnaud : à virer ? (ainsi que dans le .ml) 
(* map combinator which may usefully complete [bind] *)
val map : ('a -> 'b) -> 'a expression -> 'b expression

(* binary map combinator *)
val map2 : ('a -> 'b -> 'c) -> 'a expression -> 'b expression -> 'c expression
*)

(* [concl] is the conclusion of the current goal *)
val concl : Term.constr expression

(* [hyps] is the [named_context_val] representing the hypotheses
   of the current goal *)
val hyps : Environ.named_context_val expression

(* [env] is the current [Environ.env] containing both the 
   environment in which the proof is ran, and the goal hypotheses *)
val env : Environ.env expression

(* [defs] is the [Evd.evar_defs] at the current evaluation point *)
val defs : Evd.evar_defs expression


(* arnaud: à remplacer par un print 
(* This function returns a new goal where the evars have been
   instantiated according to an evar_map *)
val instantiate : Evd.evar_map -> goal -> goal
*)
