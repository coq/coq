
(*i $Id$ i*)

open Tacmach
open Term

(* Rewriting rules *)
type rew_rule = constr * bool * tactic

(* To add rewriting rules to a base *)
val add_rew_rules : string -> rew_rule list -> unit

(* The AutoRewrite tactic *)
val autorewrite : tactic -> string list -> tactic
