
(*i $Id$ i*)

open Tacmach

(* Rewriting rules before tactic interpretation *)
type raw_rew_rule = Term.constr * bool * Coqast.t

(* To add rewriting rules to a base *)
val add_rew_rules : string -> raw_rew_rule list -> unit

(* The AutoRewrite tactic *)
val autorewrite : tactic -> string list -> tactic
