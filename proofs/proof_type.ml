(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Evd
open Names
open Term
open Tacexpr
open Glob_term
open Nametab
open Pattern
open Misctypes
(*i*)

(* This module defines the structure of proof tree and the tactic type. So, it
   is used by Proof_tree and Refiner *)

(** Types of goals, tactics, rules ... *)

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

(** Nowadays, the only rules we'll consider are the primitive rules *)

type rule = prim_rule

(** Ltac traces *)

type ltac_call_kind =
  | LtacNotationCall of string
  | LtacNameCall of ltac_constant
  | LtacAtomCall of glob_atomic_tactic_expr
  | LtacVarCall of identifier * glob_tactic_expr
  | LtacConstrInterp of glob_constr *
      (extended_patvar_map * (identifier * identifier option) list)

type ltac_trace = (int * Loc.t * ltac_call_kind) list

exception LtacLocated of (int * ltac_call_kind * ltac_trace * Loc.t) * exn

