(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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
open Wcclausenv
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

(* usage : abstract_replace (eq,sym_eq) (eqt,sym_eqt) c2 c1 unsafe gl
   
   eq,symeq : equality on Set and its symmetry theorem
   eqt,sym_eqt : equality on Type and its symmetry theorem
   c2 c1 : c1 is to be replaced by c2
   unsafe : If true, do not check that c1 and c2 are convertible
   gl : goal
*)

val abstract_replace : 
  constr * constr -> constr * constr -> constr -> constr -> bool -> tactic

val replace   : constr -> constr -> tactic

type elimination_types =
  | Set_Type
  | Type_Type
  | Set_SetorProp
  | Type_SetorProp 


(* necessary_elimination [sort_of_arity] [sort_of_goal] *)
val necessary_elimination : sorts -> sorts -> elimination_types 

val discr        : identifier -> tactic
val discrClause  : clause -> tactic
val discrConcl   : tactic
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

(***************)
(* AutoRewrite *)
(***************)

(****Dealing with the rewriting rules****)

(*A rewriting is typically an equational constr with an orientation (true=LR
  and false=RL)*)
type rewriting_rule = constr * bool

(*Adds a list of rules to the rule table*)
val add_list_rules : identifier -> rewriting_rule list -> unit

(****The tactic****)

(*For the Step options*)
type option_step =
  | Solve
  | Use
  | All

(* the user can give a base either by a name of by its full definition
  The definition is an Ast that will find its meaning only in the context
  of a given goal *)
type hint_base = 
  | By_name of identifier
  | Explicit of (Coqast.t * bool) list

val explicit_hint_base : goal sigma -> hint_base -> rewriting_rule list

(*AutoRewrite cannot be expressed with a combination of tacticals (due to the
  options). So, we make it in a primitive way*)
val autorewrite :
  hint_base list -> tactic list option -> option_step 
    -> tactic list option -> bool -> int -> tactic
