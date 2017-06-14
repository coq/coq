(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Generic arguments based on Ltac. *)

open Genarg
open Geninterp
open Tacexpr

let make0 ?dyn name =
  let wit = Genarg.make0 name in
  let () = Geninterp.register_val0 wit dyn in
  wit

let wit_tactic : (raw_tactic_expr, glob_tactic_expr, Val.t) genarg_type =
  make0 "tactic"

let wit_ltac = make0 ~dyn:(val_tag (topwit Stdarg.wit_unit)) "ltac"

let wit_destruction_arg =
  make0 "destruction_arg"
