(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Procq

(* Main entry for extensions *)
let simple_tactic = Entry.make "simple_tactic"

(* Typically for tactic user extensions *)
let open_constr =
  Entry.make "open_constr"
let constr_with_bindings =
  Entry.make "constr_with_bindings"
let bindings =
  Entry.make "bindings"
let hypident = Entry.make "hypident"
let constr_eval = Entry.make "constr_eval"
let uconstr =
  Entry.make "uconstr"
let quantified_hypothesis =
  Entry.make "quantified_hypothesis"
let destruction_arg = Entry.make "destruction_arg"
let nat_or_var = G_redexpr.nat_or_var
let simple_intropattern =
  Entry.make "simple_intropattern"
let in_clause = Entry.make "in_clause"
let clause_dft_concl =
  Entry.make "clause"


(* Main entries for ltac *)
let tactic_value = Entry.make "tactic_value"
let ltac_expr = Entry.make "ltac_expr"

let tactic = Entry.make "tactic"

(* Main entry for quotations *)
let tactic_eoi = eoi_entry tactic

let () =
  let open Stdarg in
  let open Tacarg in
  let open G_redexpr in
  register_grammar wit_int_or_var (int_or_var);
  register_grammar wit_nat_or_var (nat_or_var);
  register_grammar wit_intro_pattern (simple_intropattern); (* To remove at end of deprecation phase *)
(* register_grammar wit_intropattern (intropattern); *) (* To be added at end of deprecation phase *)
  register_grammar wit_simple_intropattern (simple_intropattern);
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
