(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
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

let wit_int_or_var =
  Genarg.make0 ~dyn:(val_tag (topwit Stdarg.wit_int)) "int_or_var"

let wit_intro_pattern : (Constrexpr.constr_expr intro_pattern_expr located, glob_constr_and_expr intro_pattern_expr located, intro_pattern) genarg_type =
  Genarg.make0 "intropattern"

let wit_tactic : (raw_tactic_expr, glob_tactic_expr, Val.t) genarg_type =
  Genarg.make0 "tactic"

let wit_ident =
  Genarg.make0 "ident"

let wit_var =
  Genarg.make0 ~dyn:(val_tag (topwit wit_ident)) "var"

let wit_ref = Genarg.make0 "ref"

let wit_quant_hyp = Genarg.make0 "quant_hyp"

let wit_sort : (glob_sort, glob_sort, sorts) genarg_type =
  Genarg.make0 "sort"

let wit_constr =
  Genarg.make0 "constr"

let wit_constr_may_eval =
  Genarg.make0 ~dyn:(val_tag (topwit wit_constr)) "constr_may_eval"

let wit_uconstr = Genarg.make0 "uconstr"

let wit_open_constr = Genarg.make0 ~dyn:(val_tag (topwit wit_constr)) "open_constr"

let wit_constr_with_bindings = Genarg.make0 "constr_with_bindings"

let wit_bindings = Genarg.make0 "bindings"

let wit_hyp_location_flag : 'a Genarg.uniform_genarg_type =
  Genarg.make0 "hyp_location_flag"

let wit_red_expr = Genarg.make0 "redexpr"

let wit_clause_dft_concl  =
  Genarg.make0 "clause_dft_concl"

(** Register location *)

let () =
  register_name0 wit_int_or_var "Constrarg.wit_int_or_var";
  register_name0 wit_ref "Constrarg.wit_ref";
  register_name0 wit_ident "Constrarg.wit_ident";
  register_name0 wit_var "Constrarg.wit_var";
  register_name0 wit_intro_pattern "Constrarg.wit_intro_pattern";
  register_name0 wit_tactic "Constrarg.wit_tactic";
  register_name0 wit_sort "Constrarg.wit_sort";
  register_name0 wit_constr "Constrarg.wit_constr";
  register_name0 wit_uconstr "Constrarg.wit_uconstr";
  register_name0 wit_open_constr "Constrarg.wit_open_constr";
  register_name0 wit_constr_may_eval "Constrarg.wit_constr_may_eval";
  register_name0 wit_red_expr "Constrarg.wit_red_expr";
  register_name0 wit_clause_dft_concl "Constrarg.wit_clause_dft_concl";
  register_name0 wit_quant_hyp "Constrarg.wit_quant_hyp";
  register_name0 wit_bindings "Constrarg.wit_bindings";
  register_name0 wit_constr_with_bindings "Constrarg.wit_constr_with_bindings";
  ()

(** Aliases *)

let wit_reference = wit_ref
let wit_global = wit_ref
let wit_clause = wit_clause_dft_concl
let wit_quantified_hypothesis = wit_quant_hyp
let wit_intropattern = wit_intro_pattern
let wit_redexpr = wit_red_expr
