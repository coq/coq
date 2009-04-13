(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Term
open Tacexpr
open Tacmach
(*i*)

(* Rewriting rules before tactic interpretation *)
type raw_rew_rule = Term.constr * bool * Tacexpr.raw_tactic_expr

(* To add rewriting rules to a base *)
val add_rew_rules : string -> raw_rew_rule list -> unit

(* The AutoRewrite tactic *)
val autorewrite : tactic -> string list -> tactic
val autorewrite_in : Names.identifier -> tactic -> string list -> tactic

(* Rewriting rules *)
(* the type is the statement of the lemma constr. Used to elim duplicates. *)
type rew_rule = constr * types * bool * glob_tactic_expr

val find_base : string -> rew_rule list

val auto_multi_rewrite : string list -> Tacticals.clause -> tactic

val auto_multi_rewrite_with : tactic -> string list -> Tacticals.clause -> tactic

val print_rewrite_hintdb : string -> unit
