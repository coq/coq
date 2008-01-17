(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
(*i*)

(*arnaud: trucs factices *)
type tactic = Tacticals.tactic
(* arnaud: /trucs factices *)

(* Rewriting rules before tactic interpretation *)
type raw_rew_rule = Term.constr * bool * Tacexpr.raw_tactic_expr

(* To add rewriting rules to a base *)
val add_rew_rules : string -> raw_rew_rule list -> unit

(* The AutoRewrite tactic *)
val autorewrite : tactic -> string list -> tactic
val autorewrite_in : Names.identifier -> tactic -> string list -> tactic


val auto_multi_rewrite : string list -> Tacticals.clause -> tactic

val auto_multi_rewrite_with : tactic -> string list -> Tacticals.clause -> tactic

val print_rewrite_hintdb : string -> unit
