(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This files implements the autorewrite tactic. *)

open Constr
open Equality

(** Rewriting rules before tactic interpretation *)
type raw_rew_rule = (constr Univ.in_universe_context_set * bool * Genarg.raw_generic_argument option) CAst.t

(** To add rewriting rules to a base *)
val add_rew_rules : string -> raw_rew_rule list -> unit

(** The AutoRewrite tactic.
   The optional conditions tell rewrite how to handle matching and side-condition solving.
   Default is Naive: first match in the clause, don't look at the side-conditions to
   tell if the rewrite succeeded. *)
val autorewrite : ?conds:conditions -> unit Proofview.tactic -> string list -> unit Proofview.tactic
val autorewrite_in : ?conds:conditions -> Names.Id.t -> unit Proofview.tactic -> string list -> unit Proofview.tactic

(** Rewriting rules *)
type rew_rule = { rew_lemma: constr;
		  rew_type: types;
		  rew_pat: constr;
		  rew_ctx: Univ.ContextSet.t;
		  rew_l2r: bool;
		  rew_tac: Genarg.glob_generic_argument option }

val find_rewrites : string -> rew_rule list

val find_matches : string -> constr -> rew_rule list

val auto_multi_rewrite : ?conds:conditions -> string list -> Locus.clause -> unit Proofview.tactic

val auto_multi_rewrite_with : ?conds:conditions -> unit Proofview.tactic -> string list -> Locus.clause -> unit Proofview.tactic

val print_rewrite_hintdb : Environ.env -> Evd.evar_map -> string -> Pp.t

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

val find_applied_relation :
  ?loc:Loc.t -> bool ->
  Environ.env -> Evd.evar_map -> constr -> bool -> hypinfo

