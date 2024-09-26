(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Loc
open Names
open EConstr
open Libnames
open Constrexpr
open Genarg
open Genintern
open Geninterp
open Locus

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

type any_t = Any : (_, _, _) t -> any_t

let all_wits_ref : any_t list ref = ref []

let make0 (type a b c) (code : (a, b, c) t) ?dyn name : (a, b, c) genarg_type =
  let wit = Genarg.make0 name in
  let () = register_val0 wit dyn in
  let () = all_wits_ref := Any code :: !all_wits_ref in
  wit

let wit_unit : unit uniform_genarg_type =
  make0 WUnit "unit"

let wit_bool : bool uniform_genarg_type =
  make0 WBool "bool"

let wit_int : int uniform_genarg_type =
  make0 WInt "int"

let wit_nat : int uniform_genarg_type =
  make0 WNat "nat"

let wit_string : string uniform_genarg_type =
  make0 WString "string"

let wit_pre_ident : string uniform_genarg_type =
  make0 WPre_ident "preident"

let wit_int_or_var =
  make0 WInt_or_var ~dyn:(val_tag (topwit wit_int)) "int_or_var"

let wit_nat_or_var =
  make0 WNat_or_var ~dyn:(val_tag (topwit wit_nat)) "nat_or_var"

let wit_ident =
  make0 WIdent "ident"

let wit_identref =
  make0 WIdentref "identref"

let wit_hyp =
  make0 WHyp ~dyn:(val_tag (topwit wit_ident)) "hyp"

let wit_var = wit_hyp

let wit_ref = make0 WRef "ref"

let wit_smart_global = make0 WSmart_global ~dyn:(val_tag (topwit wit_ref)) "smart_global"

let wit_sort_family = make0 WSort_family "sort_family"

let wit_constr =
  make0 WConstr "constr"

let wit_uconstr = make0 WUconstr "uconstr"

let wit_open_constr = make0 WOpen_constr ~dyn:(val_tag (topwit wit_constr)) "open_constr"

let wit_clause_dft_concl =
  make0 WClause_dft_concl "clause_dft_concl"

let wit_open_binders =
  make0 WOpen_binders "open_binders"

let all_wits = !all_wits_ref

let wit_for : type a b c . (a, b, c) t -> (a, b, c) genarg_type
= function
  | WUnit -> wit_unit
  | WBool -> wit_bool
  | WNat -> wit_nat
  | WInt -> wit_int
  | WString -> wit_string
  | WPre_ident -> wit_pre_ident
  | WInt_or_var -> wit_int_or_var
  | WNat_or_var -> wit_nat_or_var
  | WIdent -> wit_ident
  | WIdentref -> wit_identref
  | WHyp -> wit_hyp
  | WRef -> wit_ref
  | WSmart_global -> wit_smart_global
  | WSort_family -> wit_sort_family
  | WConstr -> wit_constr
  | WUconstr -> wit_uconstr
  | WOpen_constr -> wit_open_constr
  | WClause_dft_concl -> wit_clause_dft_concl
  | WOpen_binders -> wit_open_binders

(** Aliases for compatibility *)

let wit_integer = wit_int
let wit_natural = wit_nat
let wit_preident = wit_pre_ident
let wit_reference = wit_ref
let wit_global = wit_ref
let wit_clause = wit_clause_dft_concl
