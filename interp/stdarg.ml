(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Genarg

let wit_unit : unit uniform_genarg_type =
  make0 None "unit"

let wit_bool : bool uniform_genarg_type =
  make0 None "bool"

let wit_int : int uniform_genarg_type =
  make0 None "int"

let wit_string : string uniform_genarg_type =
  make0 None "string"

let wit_pre_ident : string uniform_genarg_type =
  make0 None "preident"

let () = register_name0 wit_unit "Stdarg.wit_unit"
let () = register_name0 wit_bool "Stdarg.wit_bool"
let () = register_name0 wit_int "Stdarg.wit_int"
let () = register_name0 wit_string "Stdarg.wit_string"
let () = register_name0 wit_pre_ident "Stdarg.wit_pre_ident"
