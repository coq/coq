(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Names
open Environ
open Declarations
open Term
open Symbol
open Entries

(* check that a symbol declaration is correct *)
val check_symbol : env -> types -> symbol_entry -> symbol_info

(* say if a constr is headed by a symbol *)
val is_symbol_headed : env -> constr -> bool

(* check that the addition of some rules is correct *)
val check_rules : env -> rules_entry -> rules_body
