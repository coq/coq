(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Evd
open Names
open Term
open Context
open Tacexpr
open Glob_term
open Nametab
open Misctypes
(*i*)

(* This module defines the structure of proof tree and the tactic type. So, it
   is used by Proof_tree and Refiner *)

(** Types of goals, tactics, rules ... *)

type goal = Goal.goal

type tactic = goal sigma -> goal list sigma 

type prim_rule =
  | Cut of bool * bool * Id.t * types
  | FixRule of Id.t * int * (Id.t * int * constr) list * int
  | Cofix of Id.t * (Id.t * constr) list * int
  | Refine of constr
  | Thin of Id.t list
  | Move of Id.t * Id.t move_location

(** Nowadays, the only rules we'll consider are the primitive rules *)

type rule = prim_rule

(** Ltac traces *)

type ltac_call_kind =
  | LtacMLCall of glob_tactic_expr
  | LtacNotationCall of KerName.t
  | LtacNameCall of ltac_constant
  | LtacAtomCall of glob_atomic_tactic_expr
  | LtacVarCall of Id.t * glob_tactic_expr
  | LtacConstrInterp of glob_constr * Pretyping.ltac_var_map

type ltac_trace = (Loc.t * ltac_call_kind) list

let (ltac_trace_info : ltac_trace Exninfo.t) = Exninfo.make ()
