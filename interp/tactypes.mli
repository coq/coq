(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Tactic-related types that are not totally Ltac specific and still used in
    lower API. It's not clear whether this is a temporary API or if this is
    meant to stay. *)

open Loc
open Names
open Constrexpr
open Pattern
open Misctypes

(** In globalize tactics, we need to keep the initial [constr_expr] to recompute
   in the environment by the effective calls to Intro, Inversion, etc 
   The [constr_expr] field is [None] in TacDef though *)
type glob_constr_and_expr = Glob_term.glob_constr * constr_expr option
type glob_constr_pattern_and_expr = Id.Set.t * glob_constr_and_expr * constr_pattern

type 'a delayed_open = Environ.env -> Evd.evar_map -> Evd.evar_map * 'a

type delayed_open_constr = EConstr.constr delayed_open
type delayed_open_constr_with_bindings = EConstr.constr with_bindings delayed_open

type intro_pattern = delayed_open_constr intro_pattern_expr located
type intro_patterns = delayed_open_constr intro_pattern_expr located list
type or_and_intro_pattern = delayed_open_constr or_and_intro_pattern_expr located
type intro_pattern_naming = intro_pattern_naming_expr located
