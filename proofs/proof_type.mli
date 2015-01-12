(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Evd
open Names
open Term
open Context
open Tacexpr
open Glob_term
open Nametab
open Misctypes

(** This module defines the structure of proof tree and the tactic type. So, it
   is used by [Proof_tree] and [Refiner] *)

type prim_rule =
  | Cut of bool * bool * Id.t * types
  | FixRule of Id.t * int * (Id.t * int * constr) list * int
  | Cofix of Id.t * (Id.t * constr) list * int
  | Refine of constr
  | Thin of Id.t list
  | Move of Id.t * Id.t move_location

(** Nowadays, the only rules we'll consider are the primitive rules *)

type rule = prim_rule

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

type goal = Goal.goal

type tactic = goal sigma -> goal list sigma

(** Ltac traces *)

(** TODO: Move those definitions somewhere sensible *)

type ltac_call_kind =
  | LtacMLCall of glob_tactic_expr
  | LtacNotationCall of KerName.t
  | LtacNameCall of ltac_constant
  | LtacAtomCall of glob_atomic_tactic_expr
  | LtacVarCall of Id.t * glob_tactic_expr
  | LtacConstrInterp of glob_constr * Pretyping.ltac_var_map

type ltac_trace = (Loc.t * ltac_call_kind) list

val ltac_trace_info : ltac_trace Exninfo.t
