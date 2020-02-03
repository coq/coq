(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Generic arguments based on Ltac. *)

open Genarg
open Geninterp
open Tacexpr

let make0 ?dyn name =
  let wit = Genarg.make0 name in
  let () = Geninterp.register_val0 wit dyn in
  wit

let wit_intropattern = make0 "intropattern" (* To keep after deprecation phase but it will get a different parsing semantics (Tactic Notation and TACTIC EXTEND) in pltac.ml *)
let wit_simple_intropattern = make0 ~dyn:(val_tag (topwit wit_intropattern)) "simple_intropattern"
let wit_quant_hyp = make0 "quant_hyp"
let wit_constr_with_bindings = make0 "constr_with_bindings"
let wit_open_constr_with_bindings = make0 "open_constr_with_bindings"
let wit_bindings = make0 "bindings"
let wit_quantified_hypothesis = wit_quant_hyp

(* A convenient common part to simple_intropattern and intropattern
   usable when no parsing rule is concerned: indeed
   simple_intropattern and intropattern are in the same type and have
   the same interp/intern/subst methods *)
let wit_intro_pattern = wit_intropattern

let wit_tactic : (raw_tactic_expr, glob_tactic_expr, Val.t) genarg_type =
  make0 "tactic"

let wit_ltac = make0 ~dyn:(val_tag (topwit Stdarg.wit_unit)) "ltac"

let wit_destruction_arg =
  make0 "destruction_arg"
