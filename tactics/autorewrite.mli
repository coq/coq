(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Tacmach

(* Rewriting rules before tactic interpretation *)
type raw_rew_rule = Term.constr * bool * Coqast.t

(* To add rewriting rules to a base *)
val add_rew_rules : string -> raw_rew_rule list -> unit

(* The AutoRewrite tactic *)
val autorewrite : tactic -> string list -> tactic
