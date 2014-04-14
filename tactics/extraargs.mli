(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Tacexpr
open Names
open Constrexpr
open Glob_term
open Misctypes

val wit_orient : bool Genarg.uniform_genarg_type
val orient : bool Pcoq.Gram.entry
val pr_orient : bool -> Pp.std_ppcmds

val occurrences : (int list or_var) Pcoq.Gram.entry
val wit_occurrences : (int list or_var, int list or_var, int list) Genarg.genarg_type
val pr_occurrences : int list or_var -> Pp.std_ppcmds
val occurrences_of : int list -> Locus.occurrences

val wit_glob :
  (constr_expr,
  Tacexpr.glob_constr_and_expr,
  Tacinterp.interp_sign * glob_constr) Genarg.genarg_type

val wit_lglob :
  (constr_expr,
  Tacexpr.glob_constr_and_expr,
  Tacinterp.interp_sign * glob_constr) Genarg.genarg_type

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
  glob_tactic_expr option) Genarg.genarg_type

val pr_by_arg_tac : 
  (int * Ppextend.parenRelation -> raw_tactic_expr -> Pp.std_ppcmds) ->
  raw_tactic_expr option -> Pp.std_ppcmds


(** Spiwack: Primitive for retroknowledge registration *)

val retroknowledge_field : Retroknowledge.field Pcoq.Gram.entry
val wit_retroknowledge_field : Retroknowledge.field Genarg.uniform_genarg_type
