(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
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
open Rawterm
(*i*)

val find_eq_pattern : sorts -> sorts -> constr

val general_rewrite_bindings : bool -> constr with_bindings -> tactic
val general_rewrite          : bool -> constr -> tactic
val rewriteLR_bindings       : constr with_bindings -> tactic
val rewriteRL_bindings       : constr with_bindings -> tactic

val rewriteLR   : constr -> tactic
val rewriteRL   : constr  -> tactic

val conditional_rewrite : bool -> tactic -> constr with_bindings -> tactic
val general_rewrite_in : bool -> identifier -> constr with_bindings -> tactic
val conditional_rewrite_in :
  bool -> identifier -> tactic -> constr with_bindings -> tactic

val replace    : constr -> constr -> tactic
val replace_in : identifier -> constr -> constr -> tactic

val discr        : identifier -> tactic
val discrConcl   : tactic
val discrClause  : clause -> tactic
val discrHyp     : identifier -> tactic
val discrEverywhere     : tactic
val discr_tac    : quantified_hypothesis option -> tactic
val inj          : identifier -> tactic
val injClause    : quantified_hypothesis option -> tactic

val dEq : quantified_hypothesis option -> tactic
val dEqThen : (int -> tactic) -> quantified_hypothesis option -> tactic

val make_iterated_tuple : 
  env -> evar_map -> (constr * constr) -> (constr * constr) 
    -> constr * constr * constr

val substHypInConcl : bool -> identifier -> tactic
val substConcl : bool -> constr -> tactic
val substHyp : bool -> constr -> identifier -> tactic

val hypSubst_LR : identifier -> clause -> tactic
val hypSubst_RL : identifier -> clause -> tactic

val discriminable : env -> evar_map -> constr -> constr -> bool

(* Subst *)

val unfold_body : identifier -> tactic

val subst : identifier list -> tactic
val subst_all : tactic

(* Replace term *)
val replace_term_left : constr -> tactic
val replace_term_right : constr -> tactic
val replace_term : constr -> tactic
val replace_term_in_left : constr -> identifier -> tactic
val replace_term_in_right : constr -> identifier -> tactic
val replace_term_in : constr -> identifier -> tactic
