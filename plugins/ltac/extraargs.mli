(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Tacexpr
open Names
open Constrexpr
open Glob_term

val wit_orient : bool Genarg.uniform_genarg_type
val orient : bool Pcoq.Entry.t
val pr_orient : bool -> Pp.t

val wit_rename : (Id.t * Id.t) Genarg.uniform_genarg_type

val occurrences : (int list Locus.or_var) Pcoq.Entry.t
val wit_occurrences : (int list Locus.or_var, int list Locus.or_var, int list) Genarg.genarg_type
val pr_occurrences : int list Locus.or_var -> Pp.t
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

val glob : constr_expr Pcoq.Entry.t
val lglob : constr_expr Pcoq.Entry.t

type 'id gen_place= ('id * Locus.hyp_location_flag,unit) location

type loc_place = lident gen_place
type place = Id.t gen_place

val wit_hloc : (loc_place, loc_place, place) Genarg.genarg_type
val hloc : loc_place Pcoq.Entry.t
val pr_hloc : loc_place -> Pp.t

val by_arg_tac : Tacexpr.raw_tactic_expr option Pcoq.Entry.t
val wit_by_arg_tac :
  (raw_tactic_expr option,
  glob_tactic_expr option,
  Geninterp.Val.t option) Genarg.genarg_type

val pr_by_arg_tac : 
  (int * Notation_gram.parenRelation -> raw_tactic_expr -> Pp.t) ->
  raw_tactic_expr option -> Pp.t

val test_lpar_id_colon : unit Pcoq.Entry.t

val wit_test_lpar_id_colon : (unit, unit, unit) Genarg.genarg_type

(** Spiwack: Primitive for retroknowledge registration *)

val retroknowledge_field : Retroknowledge.field Pcoq.Entry.t
val wit_retroknowledge_field : (Retroknowledge.field, unit, unit) Genarg.genarg_type

val wit_in_clause :
  (lident Locus.clause_expr,
   lident Locus.clause_expr,
   Id.t   Locus.clause_expr) Genarg.genarg_type
