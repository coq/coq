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

let wit_tactic0 : (raw_tactic_expr, glob_tactic_expr, Val.t) genarg_type =
  Genarg.make0 "tactic0"

let wit_tactic1 : (raw_tactic_expr, glob_tactic_expr, Val.t) genarg_type =
  Genarg.make0 "tactic1"

let wit_tactic2 : (raw_tactic_expr, glob_tactic_expr, Val.t) genarg_type =
  Genarg.make0 "tactic2"

let wit_tactic3 : (raw_tactic_expr, glob_tactic_expr, Val.t) genarg_type =
  Genarg.make0 "tactic3"

let wit_tactic4 : (raw_tactic_expr, glob_tactic_expr, Val.t) genarg_type =
  Genarg.make0 "tactic4"

let wit_tactic5 : (raw_tactic_expr, glob_tactic_expr, Val.t) genarg_type =
  Genarg.make0 "tactic5"

let wit_ltac = Genarg.make0 ~dyn:(val_tag (topwit Stdarg.wit_unit)) "ltac"

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

(** Aliases *)

let wit_reference = wit_ref
let wit_global = wit_ref
let wit_clause = wit_clause_dft_concl
let wit_quantified_hypothesis = wit_quant_hyp
let wit_intropattern = wit_intro_pattern
let wit_redexpr = wit_red_expr
