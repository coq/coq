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
(*i*)

val general_rewrite_bindings : 
  bool -> occurrences -> constr with_bindings -> evars_flag -> tactic
val general_rewrite : 
  bool -> occurrences -> constr -> tactic

(* Obsolete, use [general_rewrite_bindings l2r]
[val rewriteLR_bindings       : constr with_bindings -> tactic]
[val rewriteRL_bindings       : constr with_bindings -> tactic]
*)

(* Equivalent to [general_rewrite l2r] *)
val rewriteLR   : constr -> tactic
val rewriteRL   : constr  -> tactic

(* Warning: old [general_rewrite_in] is now [general_rewrite_bindings_in] *)

val register_general_setoid_rewrite_clause :
  (identifier option -> bool ->
    occurrences -> open_constr -> new_goals:constr list -> tactic) -> unit
val register_is_applied_setoid_relation : (constr -> bool) -> unit

val general_rewrite_bindings_in :
  bool -> occurrences -> identifier -> constr with_bindings -> evars_flag -> tactic
val general_rewrite_in          :
  bool -> occurrences -> identifier -> constr -> evars_flag -> tactic

val general_multi_rewrite : 
  bool -> evars_flag -> open_constr with_bindings -> clause -> tactic
val general_multi_multi_rewrite : 
  evars_flag -> (bool * multi * open_constr with_bindings) list -> clause -> 
  tactic option -> tactic

val conditional_rewrite : bool -> tactic -> open_constr with_bindings -> tactic
val conditional_rewrite_in :
  bool -> identifier -> tactic -> open_constr with_bindings -> tactic

val replace_in_clause_maybe_by : constr -> constr -> clause -> tactic option -> tactic
val replace    : constr -> constr -> tactic
val replace_in : identifier -> constr -> constr -> tactic
val replace_by : constr -> constr -> tactic -> tactic
val replace_in_by : identifier -> constr -> constr -> tactic -> tactic

val discr        : evars_flag -> constr with_ebindings -> tactic
val discrConcl   : tactic
val discrClause  : evars_flag -> clause -> tactic
val discrHyp     : identifier -> tactic
val discrEverywhere : evars_flag -> tactic
val discr_tac    : evars_flag -> 
  constr with_ebindings induction_arg option -> tactic
val inj          : intro_pattern_expr located list -> evars_flag ->
  constr with_ebindings -> tactic
val injClause    : intro_pattern_expr located list -> evars_flag -> 
  constr with_ebindings induction_arg option -> tactic
val injHyp       : identifier -> tactic
val injConcl     : tactic

val dEq : evars_flag -> constr with_ebindings induction_arg option -> tactic
val dEqThen : evars_flag -> (int -> tactic) -> constr with_ebindings induction_arg option -> tactic

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

(*
(* [substHypInConcl l2r id] is obsolete: use [rewriteInConcl l2r (mkVar id)] *)
val substHypInConcl : bool -> identifier -> tactic

(* [substConcl] is an obsolete synonym for [cutRewriteInConcl] *)
val substConcl : bool -> constr -> tactic

(* [substHyp] is an obsolete synonym of [cutRewriteInHyp] *)
val substHyp : bool -> types -> identifier -> tactic
*)

(* Obsolete, use [rewriteInConcl lr (mkVar id)] in concl
              or [rewriteInHyp lr (mkVar id) (Some hyp)] in hyp
   (which, if they fail, raise only UserError, not PatternMatchingFailure)
   or [substClause lr (mkVar id) None]
   or [substClause lr (mkVar id) (Some hyp)]
[val hypSubst_LR : identifier -> clause -> tactic]
[val hypSubst_RL : identifier -> clause -> tactic]
*)

val discriminable : env -> evar_map -> constr -> constr -> bool
val injectable : env -> evar_map -> constr -> constr -> bool

(* Subst *)

val unfold_body : identifier -> tactic

val subst : identifier list -> tactic
val subst_all : tactic

(* Replace term *)
(* [replace_multi_term dir_opt c cl] 
   perfoms replacement of [c] by the first value found in context
   (according to [dir] if given to get the rewrite direction)  in the clause [cl]
*)
val replace_multi_term : bool option -> constr -> clause -> tactic
