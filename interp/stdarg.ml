(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Misctypes
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

let loc_of_or_by_notation f = function
  | AN c -> f c
  | ByNotation (loc,(s,_)) -> loc

let wit_int_or_var =
  make0 ~dyn:(val_tag (topwit wit_int)) "int_or_var"

let wit_intro_pattern =
  make0 "intropattern"

let wit_ident =
  make0 "ident"

let wit_var =
  make0 ~dyn:(val_tag (topwit wit_ident)) "var"

let wit_ref = make0 "ref"

let wit_quant_hyp = make0 "quant_hyp"

let wit_constr =
  make0 "constr"

let wit_uconstr = make0 "uconstr"

let wit_open_constr = make0 ~dyn:(val_tag (topwit wit_constr)) "open_constr"

let wit_constr_with_bindings = make0 "constr_with_bindings"

let wit_bindings = make0 "bindings"

let wit_red_expr = make0 "redexpr"

let wit_clause_dft_concl  =
  make0 "clause_dft_concl"

(** Aliases for compatibility *)

let wit_integer = wit_int
let wit_preident = wit_pre_ident
let wit_reference = wit_ref
let wit_global = wit_ref
let wit_clause = wit_clause_dft_concl
let wit_quantified_hypothesis = wit_quant_hyp
let wit_intropattern = wit_intro_pattern
let wit_redexpr = wit_red_expr
