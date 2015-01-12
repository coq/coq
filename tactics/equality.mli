(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Names
open Term
open Evd
open Environ
open Tacmach
open Tacexpr
open Ind_tables
open Locus
open Misctypes
(*i*)

type dep_proof_flag = bool (* true = support rewriting dependent proofs *)
type freeze_evars_flag = bool (* true = don't instantiate existing evars *)

type orientation = bool

type conditions =
  | Naive (* Only try the first occurence of the lemma (default) *)
  | FirstSolved (* Use the first match whose side-conditions are solved *)
  | AllMatches (* Rewrite all matches whose side-conditions are solved *)

val general_rewrite_bindings :
  orientation -> occurrences -> freeze_evars_flag -> dep_proof_flag ->
  ?tac:(unit Proofview.tactic * conditions) -> constr with_bindings -> evars_flag -> unit Proofview.tactic
val general_rewrite :
  orientation -> occurrences -> freeze_evars_flag -> dep_proof_flag ->
  ?tac:(unit Proofview.tactic * conditions) -> constr -> unit Proofview.tactic

(* Equivalent to [general_rewrite l2r] *)
val rewriteLR : ?tac:(unit Proofview.tactic * conditions) -> constr -> unit Proofview.tactic
val rewriteRL : ?tac:(unit Proofview.tactic * conditions) -> constr  -> unit Proofview.tactic

(* Warning: old [general_rewrite_in] is now [general_rewrite_bindings_in] *)

val general_setoid_rewrite_clause :
  (Id.t option -> orientation -> occurrences -> constr with_bindings ->
   new_goals:constr list -> unit Proofview.tactic) Hook.t

val general_rewrite_ebindings_clause : Id.t option ->
  orientation -> occurrences -> freeze_evars_flag -> dep_proof_flag ->
  ?tac:(unit Proofview.tactic * conditions) -> constr with_bindings -> evars_flag -> unit Proofview.tactic

val general_rewrite_bindings_in :
  orientation -> occurrences -> freeze_evars_flag -> dep_proof_flag ->
  ?tac:(unit Proofview.tactic * conditions) ->
  Id.t -> constr with_bindings -> evars_flag -> unit Proofview.tactic
val general_rewrite_in          :
  orientation -> occurrences -> freeze_evars_flag -> dep_proof_flag -> 
  ?tac:(unit Proofview.tactic * conditions) -> Id.t -> constr -> evars_flag -> unit Proofview.tactic

val general_rewrite_clause :
  orientation -> evars_flag -> ?tac:(unit Proofview.tactic * conditions) -> constr with_bindings -> clause -> unit Proofview.tactic

val general_multi_rewrite :
  evars_flag -> (bool * multi * clear_flag * delayed_open_constr_with_bindings) list ->
    clause -> (unit Proofview.tactic * conditions) option -> unit Proofview.tactic

val replace_in_clause_maybe_by : constr -> constr -> clause -> unit Proofview.tactic option -> unit Proofview.tactic
val replace    : constr -> constr -> unit Proofview.tactic
val replace_by : constr -> constr -> unit Proofview.tactic -> unit Proofview.tactic

val discr        : evars_flag -> constr with_bindings -> unit Proofview.tactic
val discrConcl   : unit Proofview.tactic
val discrHyp     : Id.t -> unit Proofview.tactic
val discrEverywhere : evars_flag -> unit Proofview.tactic
val discr_tac    : evars_flag ->
  constr with_bindings induction_arg option -> unit Proofview.tactic
val inj          : intro_patterns option -> evars_flag ->
  clear_flag -> constr with_bindings -> unit Proofview.tactic
val injClause    : intro_patterns option -> evars_flag ->
  constr with_bindings induction_arg option -> unit Proofview.tactic
val injHyp       : clear_flag -> Id.t -> unit Proofview.tactic
val injConcl     : unit Proofview.tactic

val dEq : evars_flag -> constr with_bindings induction_arg option -> unit Proofview.tactic
val dEqThen : evars_flag -> (clear_flag -> constr -> int -> unit Proofview.tactic) -> constr with_bindings induction_arg option -> unit Proofview.tactic

val make_iterated_tuple :
  env -> evar_map -> constr -> (constr * types) -> evar_map * (constr * constr * constr)

(* The family cutRewriteIn expect an equality statement *)
val cutRewriteInHyp : bool -> types -> Id.t -> unit Proofview.tactic
val cutRewriteInConcl : bool -> constr -> unit Proofview.tactic

(* The family rewriteIn expect the proof of an equality *)
val rewriteInHyp : bool -> constr -> Id.t -> unit Proofview.tactic
val rewriteInConcl : bool -> constr -> unit Proofview.tactic

val discriminable : env -> evar_map -> constr -> constr -> bool
val injectable : env -> evar_map -> constr -> constr -> bool

(* Subst *)

(* val unfold_body : Id.t -> tactic *)

type subst_tactic_flags = {
  only_leibniz : bool;
  rewrite_dependent_proof : bool
}
val subst_gen : bool -> Id.t list -> unit Proofview.tactic
val subst : Id.t list -> unit Proofview.tactic
val subst_all : ?flags:subst_tactic_flags -> unit -> unit Proofview.tactic

(* Replace term *)
(* [replace_term dir_opt c cl]
   perfoms replacement of [c] by the first value found in context
   (according to [dir] if given to get the rewrite direction)  in the clause [cl]
*)
val replace_term : bool option -> constr -> clause -> unit Proofview.tactic

val set_eq_dec_scheme_kind : mutual scheme_kind -> unit
