(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Tacexpr
open Tacmach
open Equality

(** Rewriting rules before tactic interpretation *)
type raw_rew_rule = Util.loc * Term.constr * bool * Tacexpr.raw_tactic_expr

(** To add rewriting rules to a base *)
val add_rew_rules : string -> raw_rew_rule list -> unit

(** The AutoRewrite tactic.
   The optional conditions tell rewrite how to handle matching and side-condition solving.
   Default is Naive: first match in the clause, don't look at the side-conditions to
   tell if the rewrite succeeded. *)
val autorewrite : ?conds:conditions -> tactic -> string list -> tactic
val autorewrite_in : ?conds:conditions -> Names.identifier -> tactic -> string list -> tactic

(** Rewriting rules *)
type rew_rule = { rew_lemma: constr;
		  rew_type: types;
		  rew_pat: constr;
		  rew_l2r: bool;
		  rew_tac: glob_tactic_expr }

val find_rewrites : string -> rew_rule list

val find_matches : string -> constr -> rew_rule list

val auto_multi_rewrite : ?conds:conditions -> string list -> Tacticals.clause -> tactic

val auto_multi_rewrite_with : ?conds:conditions -> tactic -> string list -> Tacticals.clause -> tactic

val print_rewrite_hintdb : string -> unit

open Clenv


type hypinfo = {
  hyp_cl : clausenv;
  hyp_prf : constr;
  hyp_ty : types;
  hyp_car : constr;
  hyp_rel : constr;
  hyp_l2r : bool;
  hyp_left : constr;
  hyp_right : constr;
}

val find_applied_relation : bool ->
  Util.loc ->
  Environ.env -> Evd.evar_map -> Term.constr -> bool -> hypinfo

