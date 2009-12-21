(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Names
open Term
open Sign
open Evd
open Environ
open Proof_type
open Tacmach
open Hipattern
open Pattern
open Tacticals
open Tactics
open Tacexpr
open Termops
open Rawterm
open Genarg
open Ind_tables
(*i*)

type dep_proof_flag = bool (* true = support rewriting dependent proofs *)

type orientation = bool

type conditions =
  | Naive (* Only try the first occurence of the lemma (default) *)
  | FirstSolved (* Use the first match whose side-conditions are solved *)
  | AllMatches (* Rewrite all matches whose side-conditions are solved *)

val general_rewrite_bindings :
  orientation -> occurrences -> dep_proof_flag ->
  ?tac:(tactic * conditions) -> constr with_bindings -> evars_flag -> tactic
val general_rewrite :
  orientation -> occurrences -> dep_proof_flag ->
  ?tac:(tactic * conditions) -> constr -> tactic

(* Equivalent to [general_rewrite l2r] *)
val rewriteLR : ?tac:(tactic * conditions) -> constr -> tactic
val rewriteRL : ?tac:(tactic * conditions) -> constr  -> tactic

(* Warning: old [general_rewrite_in] is now [general_rewrite_bindings_in] *)

val register_general_rewrite_clause :
  (identifier option -> orientation ->
    occurrences -> constr with_bindings -> new_goals:constr list -> tactic) -> unit
val register_is_applied_rewrite_relation : (env -> evar_map -> rel_context -> constr -> constr option) -> unit

val general_rewrite_ebindings_clause : identifier option ->
  orientation -> occurrences -> dep_proof_flag -> ?tac:(tactic * conditions) ->
  constr with_bindings -> evars_flag -> tactic

val general_rewrite_bindings_in :
  orientation -> occurrences -> dep_proof_flag -> ?tac:(tactic * conditions) ->
  identifier -> constr with_bindings -> evars_flag -> tactic
val general_rewrite_in          :
  orientation -> occurrences -> dep_proof_flag -> ?tac:(tactic * conditions) ->
  identifier -> constr -> evars_flag -> tactic

val general_multi_rewrite :
  orientation -> evars_flag -> ?tac:(tactic * conditions) -> constr with_bindings -> clause -> tactic
val general_multi_multi_rewrite :
  evars_flag -> (bool * multi * constr with_bindings sigma) list -> clause ->
  (tactic * conditions) option -> tactic

val replace_in_clause_maybe_by : constr -> constr -> clause -> tactic option -> tactic
val replace    : constr -> constr -> tactic
val replace_in : identifier -> constr -> constr -> tactic
val replace_by : constr -> constr -> tactic -> tactic
val replace_in_by : identifier -> constr -> constr -> tactic -> tactic

val discr        : evars_flag -> constr with_bindings -> tactic
val discrConcl   : tactic
val discrClause  : evars_flag -> clause -> tactic
val discrHyp     : identifier -> tactic
val discrEverywhere : evars_flag -> tactic
val discr_tac    : evars_flag ->
  constr with_bindings induction_arg option -> tactic
val inj          : intro_pattern_expr located list -> evars_flag ->
  constr with_bindings -> tactic
val injClause    : intro_pattern_expr located list -> evars_flag ->
  constr with_bindings induction_arg option -> tactic
val injHyp       : identifier -> tactic
val injConcl     : tactic

val dEq : evars_flag -> constr with_bindings induction_arg option -> tactic
val dEqThen : evars_flag -> (int -> tactic) -> constr with_bindings induction_arg option -> tactic

val make_iterated_tuple :
  env -> evar_map -> constr -> (constr * types) -> constr * constr * constr

(* The family cutRewriteIn expect an equality statement *)
val cutRewriteInHyp : bool -> types -> identifier -> tactic
val cutRewriteInConcl : bool -> constr -> tactic

(* The family rewriteIn expect the proof of an equality *)
val rewriteInHyp : bool -> constr -> identifier -> tactic
val rewriteInConcl : bool -> constr -> tactic

(* Expect the proof of an equality; fails with raw internal errors *)
val substClause : bool -> constr -> identifier option -> tactic

val discriminable : env -> evar_map -> constr -> constr -> bool
val injectable : env -> evar_map -> constr -> constr -> bool

(* Subst *)

val unfold_body : identifier -> tactic

type subst_tactic_flags = {
  only_leibniz : bool;
  rewrite_dependent_proof : bool
}
val subst_gen : bool -> identifier list -> tactic
val subst : identifier list -> tactic
val subst_all : ?flags:subst_tactic_flags -> tactic

(* Replace term *)
(* [replace_multi_term dir_opt c cl]
   perfoms replacement of [c] by the first value found in context
   (according to [dir] if given to get the rewrite direction)  in the clause [cl]
*)
val replace_multi_term : bool option -> constr -> clause -> tactic

val set_eq_dec_scheme_kind : mutual scheme_kind -> unit
