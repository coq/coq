(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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

let wit_string : string uniform_genarg_type =
  make0 "string"

let wit_pre_ident : string uniform_genarg_type =
  make0 ~dyn:(val_tag (topwit wit_string)) "preident"

(** Aliases for compatibility *)

let wit_integer = wit_int
let wit_preident = wit_pre_ident
