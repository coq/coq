(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Genarg
open Geninterp

type 'a and_short_name = 'a * Names.lident option

let make0 ?dyn name =
  let wit = Genarg.make0 name in
  let () = register_val0 wit dyn in
  wit

let wit_unit : unit uniform_genarg_type =
  make0 "unit"

let wit_bool : bool uniform_genarg_type =
  make0 "bool"

let wit_int : int uniform_genarg_type =
  make0 "int"

let wit_string : string uniform_genarg_type =
  make0 "string"

let wit_pre_ident : string uniform_genarg_type =
  make0 "preident"

let wit_int_or_var =
  make0 ~dyn:(val_tag (topwit wit_int)) "int_or_var"

let wit_ident =
  make0 "ident"

let wit_var =
  make0 ~dyn:(val_tag (topwit wit_ident)) "var"

let wit_ref = make0 "ref"

let wit_sort_family = make0 "sort_family"

let wit_constr =
  make0 "constr"

let wit_uconstr = make0 "uconstr"

let wit_open_constr = make0 ~dyn:(val_tag (topwit wit_constr)) "open_constr"

let wit_red_expr = make0 "redexpr"

let wit_clause_dft_concl  =
  make0 "clause_dft_concl"

(** Aliases for compatibility *)

let wit_integer = wit_int
let wit_preident = wit_pre_ident
let wit_reference = wit_ref
let wit_global = wit_ref
let wit_clause = wit_clause_dft_concl
let wit_redexpr = wit_red_expr
