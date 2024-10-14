(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
val add_rew_rules : locality:Hints.hint_locality -> string -> raw_rew_rule list -> unit

(** The AutoRewrite tactic.
   The optional conditions tell rewrite how to handle matching and side-condition solving.
   Default is Naive: first match in the clause, don't look at the side-conditions to
   tell if the rewrite succeeded. *)
val autorewrite : ?conds:conditions -> unit Proofview.tactic -> string list -> unit Proofview.tactic
val autorewrite_in : ?conds:conditions -> Names.Id.t -> unit Proofview.tactic -> string list -> unit Proofview.tactic

(** Rewriting rules *)
module RewRule :
sig
   type t
   val rew_lemma : t -> Univ.ContextSet.t * constr
   val rew_l2r : t -> bool
   val rew_tac : t -> Genarg.glob_generic_argument option
end

val find_rewrites : string -> RewRule.t list

val find_matches : Environ.env -> string -> constr -> RewRule.t list

val auto_multi_rewrite : ?conds:conditions -> string list -> Locus.clause -> unit Proofview.tactic

val auto_multi_rewrite_with : ?conds:conditions -> unit Proofview.tactic -> string list -> Locus.clause -> unit Proofview.tactic

val print_rewrite_hintdb : string -> Pp.t
