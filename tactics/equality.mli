
(* $Id$ *)

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
(*i*)

type leibniz_eq = {
  eq   : marked_term;
  ind  : marked_term;
  rrec : marked_term option;
  rect : marked_term option;
  congr: marked_term;
  sym  : marked_term }

val eq  : leibniz_eq
val eqT : leibniz_eq
val idT : leibniz_eq

val eq_pattern  : unit -> constr_pattern
val eqT_pattern : unit -> constr_pattern
val idT_pattern : unit -> constr_pattern

val find_eq_pattern : sorts -> sorts -> constr

val general_rewrite_bindings : bool -> (constr * constr substitution) -> tactic
val general_rewrite          : bool -> constr -> tactic
val rewriteLR_bindings       : (constr * constr substitution) -> tactic
val h_rewriteLR_bindings     : (constr * constr substitution) -> tactic
val rewriteRL_bindings       : (constr * constr substitution) -> tactic
val h_rewriteRL_bindings     : (constr * constr substitution) -> tactic

val rewriteLR   : constr -> tactic
val h_rewriteLR : constr -> tactic
val rewriteRL   : constr  -> tactic
val h_rewriteRL : constr  -> tactic

val conditional_rewrite : 
  bool -> tactic -> (constr * constr substitution) -> tactic
val general_rewrite_in : 
  bool -> identifier -> (constr * constr substitution) -> tactic
val conditional_rewrite_in :
  bool -> identifier -> tactic -> (constr * constr substitution) -> tactic


(* usage : abstract_replace (eq,sym_eq) (eqt,sym_eqt) c2 c1 unsafe gl
   
   eq,symeq : equality on Set and its symmetry theorem
   eqt,sym_eqt : equality on Type and its symmetry theorem
   c2 c1 : c1 is to be replaced by c2
   unsafe : If true, do not check that c1 and c2 are convertible
   gl : goal
*)

val abstract_replace : 
  constr * constr -> constr * constr -> constr -> constr -> bool -> tactic

(* Only for internal use *)
val unsafe_replace : constr -> constr -> tactic

val replace   : constr -> constr -> tactic
val h_replace : constr -> constr -> tactic

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
val h_discrConcl : tactic
val h_discrHyp   : identifier -> tactic
val h_discrConcl : tactic
val h_discr      : tactic
val inj          : identifier -> tactic
val h_injHyp     : identifier -> tactic
val h_injConcl   : tactic

val dEq : clause -> tactic
val dEqThen : (int -> tactic) -> clause -> tactic

val make_iterated_tuple : 
  env -> 'a evar_map -> (constr * constr) -> (constr * constr) 
    -> constr * constr * constr

val subst : constr -> clause -> tactic
val hypSubst : identifier -> clause -> tactic
val revSubst : constr -> clause -> tactic
val revHypSubst : identifier -> clause -> tactic

val discriminable : env -> 'a evar_map -> constr -> constr -> bool

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

