(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Environ
open Evd
open Names
open Term
open Util
open Tacexpr
open Rawterm
open Genarg
(*i*)

(* This module defines the structure of proof tree and the tactic type. So, it
   is used by [Proof_tree] and [Refiner] *)

type pf_status =
  | Complete_proof
  | Incomplete_proof

type prim_rule =
  | Intro of identifier
  | Intro_replacing of identifier
  | Cut of bool * identifier * types
  | FixRule of identifier * int * (identifier * int * constr) list
  | Cofix of identifier * (identifier * constr) list
  | Refine of constr
  | Convert_concl of types
  | Convert_hyp of named_declaration
  | Thin of identifier list
  | ThinBody of identifier list
  | Move of bool * identifier * identifier
  | Rename of identifier * identifier

(* The type [goal sigma] is the type of subgoal. It has the following form
\begin{verbatim}
   it    = { evar_concl = [the conclusion of the subgoal]
             evar_hyps = [the hypotheses of the subgoal]
             evar_body = Evar_Empty;
             evar_info = { pgm    : [The Realizer pgm if any]
                           lc     : [Set of evar num occurring in subgoal] }}
   sigma = { stamp = [an int characterizing the ed field, for quick compare]
             ed : [A set of existential variables depending in the subgoal]
               number of first evar,
               it = { evar_concl = [the type of first evar]
                      evar_hyps = [the context of the evar]
                      evar_body = [the body of the Evar if any]
                      evar_info = { pgm    : [Useless ??]
                                    lc     : [Set of evars occurring
                                              in the type of evar] } };
               ...
               number of last evar, 
               it = { evar_concl = [the type of evar]
                      evar_hyps = [the context of the evar]
                      evar_body = [the body of the Evar if any]
                      evar_info = { pgm    : [Useless ??]
                                    lc     : [Set of evars occurring
                                              in the type of evar] } } }
   }
\end{verbatim}
*)

(* The type constructor ['a sigma] adds an evar map to an object of
  type ['a] (see below the form of a [goal sigma] *)
type 'a sigma = { 
  it : 'a ; 
  sigma : evar_map}

(*s Proof trees. 
  [ref] = [None] if the goal has still to be proved, 
  and [Some (r,l)] if the rule [r] was applied to the goal
  and gave [l] as subproofs to be completed. 
  [subproof] = [(Some p)] if [ref = (Some(Tactic t,l))]; 
  [p] is then the proof that the goal can be proven if the goals
  in [l] are solved. *)
type proof_tree = {
  status : pf_status;
  goal : goal;
  ref : (rule * proof_tree list) option }

and rule =
  | Prim of prim_rule
  | Tactic of tactic_expr * proof_tree
  | Change_evars

and goal = evar_info

and tactic = goal sigma -> (goal list sigma * validation)

and validation = (proof_tree list -> proof_tree)

and tactic_expr =
  (constr,
   Closure.evaluable_global_reference,
   inductive or_metanum,
   identifier)
     Tacexpr.gen_tactic_expr

and atomic_tactic_expr =
  (constr,
   Closure.evaluable_global_reference,
   inductive or_metanum,
   identifier)
     Tacexpr.gen_atomic_tactic_expr

and tactic_arg =
  (constr,
   Closure.evaluable_global_reference,
   inductive or_metanum,
   identifier)
     Tacexpr.gen_tactic_arg

type hyp_location = identifier Tacexpr.raw_hyp_location

type open_generic_argument =
    (constr,raw_tactic_expr) generic_argument
type closed_generic_argument =
    (constr,raw_tactic_expr) generic_argument

type 'a closed_abstract_argument_type =
    ('a,constr,raw_tactic_expr) abstract_argument_type

type declaration_hook = Decl_kinds.strength -> Nametab.global_reference -> unit
