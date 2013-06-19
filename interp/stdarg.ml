(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Genarg

let def_uniform name pr = { (default_uniform_arg0 name) with
  arg0_rprint = pr;
  arg0_gprint = pr;
  arg0_tprint = pr;
}

let wit_unit : unit uniform_genarg_type =
  let pr_unit _ = str "()" in
  let arg = def_uniform "unit" pr_unit in
  make0 None "unit" arg

let wit_bool : bool uniform_genarg_type =
  let pr_bool b = str (if b then "true" else "false") in
  let arg = def_uniform "bool" pr_bool in
  make0 None "bool" arg

let () = register_name0 wit_bool "Stdarg.wit_bool"

let wit_int : int uniform_genarg_type =
  let pr_int = int in
  let arg = def_uniform "int" pr_int in
  make0 None "int" arg

let () = register_name0 wit_int "Stdarg.wit_int"

let wit_string : string uniform_genarg_type =
  let pr_string s = str "\"" ++ str s ++ str "\"" in
  let arg = def_uniform "string" pr_string in
  make0 None "string" arg

let () = register_name0 wit_string "Stdarg.wit_string"

let wit_pre_ident : string uniform_genarg_type =
  let pr_pre_ident = str in
  let arg = def_uniform "preident" pr_pre_ident in
  make0 None "preident" arg

let () = register_name0 wit_pre_ident "Stdarg.wit_pre_ident"
