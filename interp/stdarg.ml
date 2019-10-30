(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Genarg
open Geninterp

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

let wit_nat : int uniform_genarg_type =
  make0 "nat"

let wit_string : string uniform_genarg_type =
  make0 "string"

let wit_preident : string uniform_genarg_type =
  make0 "preident"

let wit_int_or_var =
  make0 ~dyn:(val_tag (topwit wit_int)) "int_or_var"

let wit_nat_or_var =
  make0 ~dyn:(val_tag (topwit wit_int)) "nat_or_var"

let wit_ident =
  make0 "ident"

let wit_identref =
  make0 "identref"

let wit_hyp =
  make0 ~dyn:(val_tag (topwit wit_ident)) "hyp"

let wit_var = wit_hyp

let wit_reference = make0 "reference"

let wit_smart_global = make0 ~dyn:(val_tag (topwit wit_reference)) "smart_global"

let wit_sort_family = make0 "sort_family"

let wit_constr =
  make0 "constr"

let wit_uconstr = make0 "uconstr"

let wit_open_constr = make0 ~dyn:(val_tag (topwit wit_constr)) "open_constr"

let wit_clause = make0 "clause"
