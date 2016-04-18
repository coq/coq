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
open Geninterp

let make0 ?dyn name =
  let wit = Genarg.make0 name in
  let () = Geninterp.register_val0 wit dyn in
  wit

(** This is a hack for now, to break the dependency of Genarg on constr-related
    types. We should use dedicated functions someday. *)

let loc_of_or_by_notation f = function
  | AN c -> f c
  | ByNotation (loc,s,_) -> loc

let wit_int_or_var =
  make0 ~dyn:(val_tag (topwit Stdarg.wit_int)) "int_or_var"

let wit_intro_pattern : (Constrexpr.constr_expr intro_pattern_expr located, glob_constr_and_expr intro_pattern_expr located, intro_pattern) genarg_type =
  make0 "intropattern"

let wit_tactic : (raw_tactic_expr, glob_tactic_expr, Val.t) genarg_type =
  make0 "tactic"

let wit_ltac = make0 ~dyn:(val_tag (topwit Stdarg.wit_unit)) "ltac"

let wit_ident =
  make0 "ident"

let wit_var =
  make0 ~dyn:(val_tag (topwit wit_ident)) "var"

let wit_ref = make0 "ref"

let wit_quant_hyp = make0 "quant_hyp"

let wit_sort : (glob_sort, glob_sort, sorts) genarg_type =
  make0 "sort"

let wit_constr =
  make0 "constr"

let wit_constr_may_eval =
  make0 ~dyn:(val_tag (topwit wit_constr)) "constr_may_eval"

let wit_uconstr = make0 "uconstr"

let wit_open_constr = make0 ~dyn:(val_tag (topwit wit_constr)) "open_constr"

let wit_constr_with_bindings = make0 "constr_with_bindings"

let wit_bindings = make0 "bindings"

let wit_hyp_location_flag : 'a Genarg.uniform_genarg_type =
  make0 "hyp_location_flag"

let wit_red_expr = make0 "redexpr"

let wit_clause_dft_concl  =
  make0 "clause_dft_concl"

(** Aliases *)

let wit_reference = wit_ref
let wit_global = wit_ref
let wit_clause = wit_clause_dft_concl
let wit_quantified_hypothesis = wit_quant_hyp
let wit_intropattern = wit_intro_pattern
let wit_redexpr = wit_red_expr
