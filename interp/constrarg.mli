(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Generic arguments based on [constr]. We put them here to avoid a dependency
    of Genarg in [constr]-related interfaces. *)

open Loc
open Names
open Term
open Libnames
open Globnames
open Genredexpr
open Pattern
open Constrexpr
open Tacexpr
open Misctypes
open Genarg

(** FIXME: nothing to do there. *)
val loc_of_or_by_notation : ('a -> Loc.t) -> 'a or_by_notation -> Loc.t

(** {5 Additional generic arguments} *)

val wit_int_or_var : int or_var uniform_genarg_type

val wit_intro_pattern : intro_pattern_expr located uniform_genarg_type


val wit_ident : Id.t uniform_genarg_type

val wit_var : (Id.t located, Id.t located, Id.t) genarg_type

val wit_ref : (reference, global_reference located or_var, global_reference) genarg_type

val wit_quant_hyp : quantified_hypothesis uniform_genarg_type

val wit_genarg : (raw_generic_argument, glob_generic_argument, typed_generic_argument) genarg_type

val wit_sort : (glob_sort, glob_sort, sorts) genarg_type

val wit_constr : (constr_expr, glob_constr_and_expr, constr) genarg_type

val wit_constr_may_eval :
  ((constr_expr,reference or_by_notation,constr_expr) may_eval,
  (glob_constr_and_expr,evaluable_global_reference and_short_name or_var,glob_constr_pattern_and_expr) may_eval,
  constr) genarg_type

val wit_open_constr :
  (open_constr_expr, open_glob_constr, Evd.open_constr) genarg_type

val wit_constr_with_bindings :
  (constr_expr with_bindings,
  glob_constr_and_expr with_bindings,
  constr with_bindings Evd.sigma) genarg_type

val wit_bindings :
  (constr_expr bindings,
  glob_constr_and_expr bindings,
  constr bindings Evd.sigma) genarg_type

val wit_red_expr :
  ((constr_expr,reference or_by_notation,constr_expr) red_expr_gen,
  (glob_constr_and_expr,evaluable_global_reference and_short_name or_var,glob_constr_pattern_and_expr) red_expr_gen,
  (constr,evaluable_global_reference,constr_pattern) red_expr_gen) genarg_type

val wit_tactic : (raw_tactic_expr, glob_tactic_expr, glob_tactic_expr) genarg_type

val wit_clause_dft_concl :  (Names.Id.t Loc.located Tacexpr.or_metaid Locus.clause_expr,Names.Id.t Loc.located Locus.clause_expr,Names.Id.t Locus.clause_expr) genarg_type
