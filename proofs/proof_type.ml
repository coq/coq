(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ *)

(*i*)
open Environ
open Evd
open Names
open Libnames
open Term
open Util
open Tacexpr
open Rawterm
open Genarg
(*i*)

(* This module defines the structure of proof tree and the tactic type. So, it
   is used by Proof_tree and Refiner *)

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


(* Signature useful to define the tactic type *)
type 'a sigma = { 
  it : 'a ; 
  sigma : evar_map }

(*s Proof trees. 
  [ref] = [None] if the goal has still to be proved, 
  and [Some (r,l)] if the rule [r] was applied to the goal
  and gave [l] as subproofs to be completed. 
  if [ref = (Some(Tactic (t,p),l))] then [p] is the proof 
  that the goal can be proven if the goals in [l] are solved. *)
type proof_tree = {
  open_subgoals : int;
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
   evaluable_global_reference,
   inductive or_metanum,
   identifier)
     Tacexpr.gen_tactic_expr

and atomic_tactic_expr =
  (constr,
   evaluable_global_reference,
   inductive or_metanum,
   identifier)
     Tacexpr.gen_atomic_tactic_expr

and tactic_arg =
  (constr,
   evaluable_global_reference,
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
