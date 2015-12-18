(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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

let wit_int_or_var =
  Genarg.make0 ~dyn:(val_tag (topwit Stdarg.wit_int)) None "int_or_var"

let wit_intro_pattern : (Constrexpr.constr_expr intro_pattern_expr located, glob_constr_and_expr intro_pattern_expr located, intro_pattern) genarg_type =
  Genarg.make0 None "intropattern"

let wit_tactic : (raw_tactic_expr, glob_tactic_expr, glob_tactic_expr) genarg_type =
  Genarg.make0 None "tactic"

let wit_ident = unsafe_of_type IdentArgType

let wit_var = unsafe_of_type VarArgType

let wit_ref = Genarg.make0 None "ref"

let wit_quant_hyp = Genarg.make0 None "quant_hyp"

let wit_sort : (glob_sort, glob_sort, sorts) genarg_type =
  Genarg.make0 None "sort"

let wit_constr = unsafe_of_type ConstrArgType

let wit_constr_may_eval =
  Genarg.make0 ~dyn:(val_tag (topwit wit_constr)) None "constr_may_eval"

let wit_uconstr = Genarg.make0 None "uconstr"

let wit_open_constr = unsafe_of_type OpenConstrArgType

let wit_constr_with_bindings = Genarg.make0 None "constr_with_bindings"

let wit_bindings = Genarg.make0 None "bindings"

let wit_hyp_location_flag : 'a Genarg.uniform_genarg_type =
  Genarg.make0 None "hyp_location_flag"

let wit_red_expr = Genarg.make0 None "redexpr"

let wit_clause_dft_concl  =
  Genarg.make0 None "clause_dft_concl"

(** Register location *)

let () =
  register_name0 wit_int_or_var "Constrarg.wit_int_or_var";
  register_name0 wit_ref "Constrarg.wit_ref";
  register_name0 wit_intro_pattern "Constrarg.wit_intro_pattern";
  register_name0 wit_tactic "Constrarg.wit_tactic";
  register_name0 wit_sort "Constrarg.wit_sort";
  register_name0 wit_uconstr "Constrarg.wit_uconstr";
  register_name0 wit_constr_may_eval "Constrarg.wit_constr_may_eval";
  register_name0 wit_red_expr "Constrarg.wit_red_expr";
  register_name0 wit_clause_dft_concl "Constrarg.wit_clause_dft_concl";
  register_name0 wit_quant_hyp "Constrarg.wit_quant_hyp";
  register_name0 wit_bindings "Constrarg.wit_bindings";
  register_name0 wit_constr_with_bindings "Constrarg.wit_constr_with_bindings";
