(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Basic generic arguments. *)

open Loc
open Names
open EConstr
open Libnames
open Globnames
open Genredexpr
open Pattern
open Constrexpr
open Misctypes
open Tactypes
open Genarg

(** FIXME: nothing to do there. *)
val loc_of_or_by_notation : ('a -> Loc.t option) -> 'a or_by_notation -> Loc.t option

val wit_unit : unit uniform_genarg_type

val wit_bool : bool uniform_genarg_type

val wit_int : int uniform_genarg_type

val wit_string : string uniform_genarg_type

val wit_pre_ident : string uniform_genarg_type

(** {5 Additional generic arguments} *)

val wit_int_or_var : (int or_var, int or_var, int) genarg_type

val wit_intro_pattern : (constr_expr intro_pattern_expr located, glob_constr_and_expr intro_pattern_expr located, intro_pattern) genarg_type

val wit_ident : Id.t uniform_genarg_type

val wit_var : (Id.t located, Id.t located, Id.t) genarg_type

val wit_ref : (reference, global_reference located or_var, global_reference) genarg_type

val wit_quant_hyp : quantified_hypothesis uniform_genarg_type

val wit_constr : (constr_expr, glob_constr_and_expr, constr) genarg_type

val wit_uconstr : (constr_expr , glob_constr_and_expr, Glob_term.closed_glob_constr) genarg_type

val wit_open_constr :
  (constr_expr, glob_constr_and_expr, constr) genarg_type

val wit_constr_with_bindings :
  (constr_expr with_bindings,
  glob_constr_and_expr with_bindings,
  constr with_bindings delayed_open) genarg_type

val wit_bindings :
  (constr_expr bindings,
  glob_constr_and_expr bindings,
  constr bindings delayed_open) genarg_type

val wit_red_expr :
  ((constr_expr,reference or_by_notation,constr_expr) red_expr_gen,
  (glob_constr_and_expr,evaluable_global_reference and_short_name or_var,glob_constr_pattern_and_expr) red_expr_gen,
  (constr,evaluable_global_reference,constr_pattern) red_expr_gen) genarg_type

val wit_clause_dft_concl :  (Names.Id.t Loc.located Locus.clause_expr,Names.Id.t Loc.located Locus.clause_expr,Names.Id.t Locus.clause_expr) genarg_type

(** Aliases for compatibility *)

val wit_integer : int uniform_genarg_type
val wit_preident : string uniform_genarg_type
val wit_reference : (reference, global_reference located or_var, global_reference) genarg_type
val wit_global : (reference, global_reference located or_var, global_reference) genarg_type
val wit_clause :  (Names.Id.t Loc.located Locus.clause_expr,Names.Id.t Loc.located Locus.clause_expr,Names.Id.t Locus.clause_expr) genarg_type
val wit_quantified_hypothesis : quantified_hypothesis uniform_genarg_type
val wit_intropattern : (constr_expr intro_pattern_expr located, glob_constr_and_expr intro_pattern_expr located, intro_pattern) genarg_type
val wit_redexpr :
  ((constr_expr,reference or_by_notation,constr_expr) red_expr_gen,
  (glob_constr_and_expr,evaluable_global_reference and_short_name or_var,glob_constr_pattern_and_expr) red_expr_gen,
  (constr,evaluable_global_reference,constr_pattern) red_expr_gen) genarg_type
