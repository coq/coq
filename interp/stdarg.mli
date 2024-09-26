(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Basic generic arguments. *)

open Loc
open Names
open EConstr
open Libnames
open Constrexpr
open Genarg
open Genintern
open Locus

val wit_unit : unit uniform_genarg_type

val wit_bool : bool uniform_genarg_type

val wit_nat : int uniform_genarg_type

val wit_int : int uniform_genarg_type

val wit_string : string uniform_genarg_type

val wit_pre_ident : string uniform_genarg_type

(** {5 Additional generic arguments} *)

val wit_int_or_var : (int or_var, int or_var, int) genarg_type

val wit_nat_or_var : (int or_var, int or_var, int) genarg_type

val wit_ident : Id.t uniform_genarg_type

val wit_identref : (lident, lident, Id.t) genarg_type

val wit_hyp : (lident, lident, Id.t) genarg_type

val wit_var : (lident, lident, Id.t) genarg_type
[@@ocaml.deprecated "(8.13) Use Stdarg.wit_hyp"]

val wit_ref : (qualid, GlobRef.t located or_var, GlobRef.t) genarg_type

val wit_smart_global : (qualid or_by_notation, GlobRef.t located or_var, GlobRef.t) genarg_type

val wit_sort_family : (Sorts.family, unit, unit) genarg_type

val wit_constr : (constr_expr, glob_constr_and_expr, constr) genarg_type

val wit_uconstr : (constr_expr , glob_constr_and_expr, Ltac_pretype.closed_glob_constr) genarg_type

val wit_open_constr :
  (constr_expr, glob_constr_and_expr, constr) genarg_type

val wit_clause_dft_concl :  (lident Locus.clause_expr, lident Locus.clause_expr, Names.Id.t Locus.clause_expr) genarg_type

val wit_open_binders : local_binder_expr list uniform_genarg_type

(** {5 All generic arguments} *)

type (_, _, _) t =
  | WUnit : (unit, unit, unit) t
  | WBool : (bool, bool, bool) t
  | WNat : (int, int, int) t
  | WInt : (int, int, int) t
  | WString : (string, string, string) t
  | WPre_ident : (string, string, string) t
  | WInt_or_var : (int or_var, int or_var, int) t
  | WNat_or_var : (int or_var, int or_var, int) t
  | WIdent : (Id.t, Id.t, Id.t) t
  | WIdentref : (lident, lident, Id.t) t
  | WHyp : (lident, lident, Id.t) t
  | WRef : (qualid, GlobRef.t located or_var, GlobRef.t) t
  | WSmart_global : (qualid or_by_notation, GlobRef.t located or_var, GlobRef.t) t
  | WSort_family : (Sorts.family, unit, unit) t
  | WConstr : (constr_expr, glob_constr_and_expr, constr) t
  | WUconstr : (constr_expr, glob_constr_and_expr, Ltac_pretype.closed_glob_constr) t
  | WOpen_constr : (constr_expr, glob_constr_and_expr, constr) t
  | WClause_dft_concl :  (lident Locus.clause_expr, lident Locus.clause_expr, Names.Id.t Locus.clause_expr) t
  | WOpen_binders : (local_binder_expr list, local_binder_expr list, local_binder_expr list) t

val wit_for : ('a, 'b, 'c) t -> ('a, 'b, 'c) genarg_type

type any_t = Any : (_, _, _) t -> any_t

val all_wits : any_t list

(** Aliases for compatibility *)

val wit_natural : int uniform_genarg_type
val wit_integer : int uniform_genarg_type
val wit_preident : string uniform_genarg_type
val wit_reference : (qualid, GlobRef.t located or_var, GlobRef.t) genarg_type
val wit_global : (qualid, GlobRef.t located or_var, GlobRef.t) genarg_type
val wit_clause :  (lident Locus.clause_expr, lident Locus.clause_expr, Names.Id.t Locus.clause_expr) genarg_type
