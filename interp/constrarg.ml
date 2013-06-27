(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Pp
open Names
open Term
open Libnames
open Globnames
open Glob_term
open Genredexpr
open Pattern
open Constrexpr
open Term
open Misctypes
open Genarg

(** This is a hack for now, to break the dependency of Genarg on constr-related
    types. We should use dedicated functions someday. *)

let loc_of_or_by_notation f = function
  | AN c -> f c
  | ByNotation (loc,s,_) -> loc

let unsafe_of_type (t : argument_type) : ('a, 'b, 'c) Genarg.genarg_type =
  Obj.magic t

let wit_int_or_var = unsafe_of_type IntOrVarArgType

let wit_intro_pattern : intro_pattern_expr located uniform_genarg_type =
  Genarg.make0 None "intropattern"

let wit_ident_gen b = unsafe_of_type (IdentArgType b)

let wit_ident = wit_ident_gen true

let wit_pattern_ident = wit_ident_gen false

let wit_var = unsafe_of_type VarArgType

let wit_ref = unsafe_of_type RefArgType

let wit_quant_hyp = unsafe_of_type QuantHypArgType

let wit_genarg = unsafe_of_type GenArgType

let wit_sort = unsafe_of_type SortArgType

let wit_constr = unsafe_of_type ConstrArgType

let wit_constr_may_eval = unsafe_of_type ConstrMayEvalArgType

let wit_open_constr_gen b = unsafe_of_type (OpenConstrArgType b)

let wit_open_constr = wit_open_constr_gen false

let wit_casted_open_constr = wit_open_constr_gen true

let wit_constr_with_bindings = unsafe_of_type ConstrWithBindingsArgType

let wit_bindings = unsafe_of_type BindingsArgType

let wit_red_expr = unsafe_of_type RedExprArgType

(** Register location *)

let () = register_name0 wit_intro_pattern "Constrarg.wit_intro_pattern"
