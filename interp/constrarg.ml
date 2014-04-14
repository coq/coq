(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Tacexpr
open Term
open Misctypes
open Genarg

(** This is a hack for now, to break the dependency of Genarg on constr-related
    types. We should use dedicated functions someday. *)

let loc_of_or_by_notation f = function
  | AN c -> f c
  | ByNotation (loc,s,_) -> loc

let unsafe_of_type (t : argument_type) : ('a, 'b, 'c) Genarg.genarg_type =
  Obj.magic t

let wit_int_or_var = unsafe_of_type IntOrVarArgType

let wit_intro_pattern : intro_pattern_expr located uniform_genarg_type =
  Genarg.make0 None "intropattern"

let wit_tactic : (raw_tactic_expr, glob_tactic_expr, glob_tactic_expr) genarg_type =
  Genarg.make0 None "tactic"

let wit_ident = unsafe_of_type IdentArgType

let wit_var = unsafe_of_type VarArgType

let wit_ref = Genarg.make0 None "ref"

let wit_quant_hyp = unsafe_of_type QuantHypArgType

let wit_genarg = unsafe_of_type GenArgType

let wit_sort : (glob_sort, glob_sort, sorts) genarg_type =
  Genarg.make0 None "sort"

let wit_constr = unsafe_of_type ConstrArgType

let wit_constr_may_eval = unsafe_of_type ConstrMayEvalArgType

let wit_open_constr = unsafe_of_type OpenConstrArgType

let wit_constr_with_bindings = unsafe_of_type ConstrWithBindingsArgType

let wit_bindings = unsafe_of_type BindingsArgType

let wit_red_expr = unsafe_of_type RedExprArgType

let wit_clause_dft_concl  =
  Genarg.make0 None "clause_dft_concl"

(** Register location *)

let () =
  register_name0 wit_ref "Constrarg.wit_ref";
  register_name0 wit_intro_pattern "Constrarg.wit_intro_pattern";
  register_name0 wit_tactic "Constrarg.wit_tactic";
  register_name0 wit_sort "Constrarg.wit_sort";
  register_name0 wit_clause_dft_concl "Constrarg.wit_clause_dft_concl";
