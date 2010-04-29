(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

(*i $Id$ i*)

open Environ
open Evd
open Names
open Libnames
open Term
open Util
open Tacexpr
open Rawterm
open Genarg
open Nametab
open Pattern

(** This module defines the structure of proof tree and the tactic type. So, it
   is used by [Proof_tree] and [Refiner] *)

type goal = Goal.goal

type tactic = goal sigma -> goal list sigma

type prim_rule =
  | Intro of identifier
  | Cut of bool * bool * identifier * types
  | FixRule of identifier * int * (identifier * int * constr) list * int
  | Cofix of identifier * (identifier * constr) list * int
  | Refine of constr
  | Convert_concl of types * cast_kind
  | Convert_hyp of named_declaration
  | Thin of identifier list
  | ThinBody of identifier list
  | Move of bool * identifier * identifier move_location
  | Order of identifier list
  | Rename of identifier * identifier
  | Change_evars

(** The type [goal sigma] is the type of subgoal. It has the following form
{v   it    = \{ evar_concl = [the conclusion of the subgoal]
             evar_hyps = [the hypotheses of the subgoal]
             evar_body = Evar_Empty;
             evar_info = \{ pgm    : [The Realizer pgm if any]
                           lc     : [Set of evar num occurring in subgoal] \}\}
   sigma = \{ stamp = [an int chardacterizing the ed field, for quick compare]
             ed : [A set of existential variables depending in the subgoal]
               number of first evar,
               it = \{ evar_concl = [the type of first evar]
                      evar_hyps = [the context of the evar]
                      evar_body = [the body of the Evar if any]
                      evar_info = \{ pgm    : [Useless ??]
                                    lc     : [Set of evars occurring
                                              in the type of evar] \} \};
               ...
               number of last evar,
               it = \{ evar_concl = [the type of evar]
                      evar_hyps = [the context of the evar]
                      evar_body = [the body of the Evar if any]
                      evar_info = \{ pgm    : [Useless ??]
                                    lc     : [Set of evars occurring
                                              in the type of evar] \} \} \} v}
*)

(** {6 Sect } *)
(** Proof trees.
  [ref] = [None] if the goal has still to be proved,
  and [Some (r,l)] if the rule [r] was applied to the goal
  and gave [l] as subproofs to be completed.
  if [ref = (Some(Nested(Tactic t,p),l))] then [p] is the proof
  that the goal can be proven if the goals in [l] are solved. *)
type proof_tree = {
  open_subgoals : int;
  goal : goal;
  ref : (rule * proof_tree list) option }

and rule =
  | Prim of prim_rule
  | Nested of compound_rule * proof_tree
  | Decl_proof of bool
  | Daimon

and compound_rule=
  (** the boolean of Tactic tells if the default tactic is used *)
  | Tactic of tactic_expr * bool

and tactic_expr =
  (constr,
   constr_pattern,
   evaluable_global_reference,
   inductive,
   ltac_constant,
   identifier,
   glob_tactic_expr,
   tlevel)
     Tacexpr.gen_tactic_expr

and atomic_tactic_expr =
  (constr,
   constr_pattern,
   evaluable_global_reference,
   inductive,
   ltac_constant,
   identifier,
   glob_tactic_expr,
   tlevel)
     Tacexpr.gen_atomic_tactic_expr

and tactic_arg =
  (constr,
   constr_pattern,
   evaluable_global_reference,
   inductive,
   ltac_constant,
   identifier,
   glob_tactic_expr,
   tlevel)
     Tacexpr.gen_tactic_arg

type ltac_call_kind =
  | LtacNotationCall of string
  | LtacNameCall of ltac_constant
  | LtacAtomCall of glob_atomic_tactic_expr * atomic_tactic_expr option ref
  | LtacVarCall of identifier * glob_tactic_expr
  | LtacConstrInterp of rawconstr *
      ((identifier * constr) list * (identifier * identifier option) list)

type ltac_trace = (int * loc * ltac_call_kind) list

exception LtacLocated of (int * ltac_call_kind * ltac_trace * loc) * exn

val abstract_tactic_box : atomic_tactic_expr option ref ref
