(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Grammar_API
open Tacexpr
open Names
open Constrexpr
open Glob_term
open Misctypes

val wit_orient : bool Genarg.uniform_genarg_type
val orient : bool Pcoq.Gram.entry
val pr_orient : bool -> Pp.std_ppcmds

val wit_rename : (Id.t * Id.t) Genarg.uniform_genarg_type

val occurrences : (int list or_var) Pcoq.Gram.entry
val wit_occurrences : (int list or_var, int list or_var, int list) Genarg.genarg_type
val pr_occurrences : int list or_var -> Pp.std_ppcmds
val occurrences_of : int list -> Locus.occurrences

val wit_natural : int Genarg.uniform_genarg_type

val wit_glob :
  (constr_expr,
  Tacexpr.glob_constr_and_expr,
  Tacinterp.interp_sign * glob_constr) Genarg.genarg_type

val wit_lglob :
  (constr_expr,
  Tacexpr.glob_constr_and_expr,
  Tacinterp.interp_sign * glob_constr) Genarg.genarg_type

val wit_lconstr :
  (constr_expr,
  Tacexpr.glob_constr_and_expr,
  EConstr.t) Genarg.genarg_type

val wit_casted_constr :
  (constr_expr,
  Tacexpr.glob_constr_and_expr,
  EConstr.t) Genarg.genarg_type

val glob : constr_expr Pcoq.Gram.entry
val lglob : constr_expr Pcoq.Gram.entry

type 'id gen_place= ('id * Locus.hyp_location_flag,unit) location

type loc_place = Id.t Loc.located gen_place
type place = Id.t gen_place

val wit_hloc : (loc_place, loc_place, place) Genarg.genarg_type
val hloc : loc_place Pcoq.Gram.entry
val pr_hloc : loc_place -> Pp.std_ppcmds

val by_arg_tac : Tacexpr.raw_tactic_expr option Pcoq.Gram.entry
val wit_by_arg_tac :
  (raw_tactic_expr option,
  glob_tactic_expr option,
  Geninterp.Val.t option) Genarg.genarg_type

val pr_by_arg_tac : 
  (int * Ppextend.parenRelation -> raw_tactic_expr -> Pp.std_ppcmds) ->
  raw_tactic_expr option -> Pp.std_ppcmds

val test_lpar_id_colon : unit Pcoq.Gram.entry

val wit_test_lpar_id_colon : (unit, unit, unit) Genarg.genarg_type

(** Spiwack: Primitive for retroknowledge registration *)

val retroknowledge_field : Retroknowledge.field Pcoq.Gram.entry
val wit_retroknowledge_field : (Retroknowledge.field, unit, unit) Genarg.genarg_type

val wit_in_clause :
  (Id.t Loc.located Locus.clause_expr,
  Id.t Loc.located Locus.clause_expr,
  Id.t Locus.clause_expr) Genarg.genarg_type
