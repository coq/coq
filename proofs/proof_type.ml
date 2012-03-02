(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Environ
open Evd
open Names
open Libnames
open Term
open Pp
open Tacexpr
(* open Decl_expr *)
open Glob_term
open Genarg
open Nametab
open Pattern
(*i*)

(* This module defines the structure of proof tree and the tactic type. So, it
   is used by Proof_tree and Refiner *)

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

type proof_tree = {
  goal : goal;
  ref : (rule * proof_tree list) option }

and rule =
  | Prim of prim_rule
  | Nested of compound_rule * proof_tree
  | Decl_proof of bool
  | Daimon

and compound_rule=
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
  | LtacConstrInterp of glob_constr *
      (extended_patvar_map * (identifier * identifier option) list)

type ltac_trace = (int * loc * ltac_call_kind) list

exception LtacLocated of (int * ltac_call_kind * ltac_trace * loc) * exn

let abstract_tactic_box = ref (ref None)
