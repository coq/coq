(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pcoq

(* Main entry for extensions *)
let simple_tactic = Entry.create "tactic:simple_tactic"

let make_gen_entry _ name = Entry.create ("tactic:" ^ name)

(* Typically for tactic user extensions *)
let open_constr =
  make_gen_entry utactic "open_constr"
let constr_with_bindings =
  make_gen_entry utactic "constr_with_bindings"
let bindings =
  make_gen_entry utactic "bindings"
let hypident = Entry.create "hypident"
let constr_may_eval = make_gen_entry utactic "constr_may_eval"
let constr_eval = make_gen_entry utactic "constr_eval"
let uconstr =
  make_gen_entry utactic "uconstr"
let quantified_hypothesis =
  make_gen_entry utactic "quantified_hypothesis"
let destruction_arg = make_gen_entry utactic "destruction_arg"
let int_or_var = make_gen_entry utactic "int_or_var"
let simple_intropattern =
  make_gen_entry utactic "simple_intropattern"
let in_clause = make_gen_entry utactic "in_clause"
let clause_dft_concl = 
  make_gen_entry utactic "clause"


(* Main entries for ltac *)
let tactic_arg = Entry.create "tactic:tactic_arg"
let tactic_expr = make_gen_entry utactic "tactic_expr"
let binder_tactic = make_gen_entry utactic "binder_tactic"

let tactic = make_gen_entry utactic "tactic"

(* Main entry for quotations *)
let tactic_eoi = eoi_entry tactic

let () =
  let open Stdarg in
  let open Tacarg in
  register_grammar wit_int_or_var (int_or_var);
  register_grammar wit_intro_pattern (simple_intropattern);
  register_grammar wit_quant_hyp (quantified_hypothesis);
  register_grammar wit_uconstr (uconstr);
  register_grammar wit_open_constr (open_constr);
  register_grammar wit_constr_with_bindings (constr_with_bindings);
  register_grammar wit_bindings (bindings);
  register_grammar wit_tactic (tactic);
  register_grammar wit_ltac (tactic);
  register_grammar wit_clause_dft_concl (clause_dft_concl);
  register_grammar wit_destruction_arg (destruction_arg);
  ()
