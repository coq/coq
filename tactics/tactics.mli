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
open Environ
open Tacmach
open Proof_type
open Reduction
open Evd
open Evar_refiner
open Clenv
open Tacred
open Tacticals
(*i*)

(* Main tactics. *)

(*s General functions. *)

val type_clenv_binding : walking_constraints ->
  constr * constr -> constr substitution  -> constr

val string_of_inductive : constr -> string
val head_constr       : constr -> constr list
val head_constr_bound : constr -> constr list -> constr list
val bad_tactic_args : string -> tactic_arg list -> 'a

exception Bound

(*s Primitive tactics. *)

val introduction    : identifier -> tactic
val refine          : constr -> tactic
val convert_concl   : constr -> tactic
val convert_hyp     : identifier -> constr -> tactic
val thin            : identifier list -> tactic
val mutual_fix      : identifier list -> int list -> constr list -> tactic
val fix             : identifier -> int -> tactic
val mutual_cofix    : identifier list -> constr list -> tactic
val cofix           : identifier -> tactic

val dyn_mutual_fix   : tactic_arg list -> tactic
val dyn_mutual_cofix : tactic_arg list -> tactic

(*s Introduction tactics. *)

val next_global_ident_away : identifier -> identifier list -> identifier
val fresh_id : identifier list -> identifier -> goal sigma -> identifier

val intro                : tactic
val introf               : tactic
val intro_force          : bool -> tactic
val dyn_intro            : tactic_arg list -> tactic

val dyn_intro_move       : tactic_arg list -> tactic

val intro_replacing      : identifier -> tactic
val intro_using          : identifier -> tactic
val intro_mustbe         : identifier -> tactic
val intros_using         : identifier list -> tactic
val intro_erasing        : identifier -> tactic
val intros_replacing     : identifier list -> tactic

val intros               : tactic

(*i Obsolete, subsumed by Elim.dyn_intro_pattern
val dyn_intros_using : tactic_arg list -> tactic
i*)

val intros_until         : identifier -> tactic
val intros_until_n       : int -> tactic
val intros_until_n_wored : int -> tactic
val dyn_intros_until     : tactic_arg list -> tactic

val intros_clearing      : bool list -> tactic

(* Assuming a tactic [tac] depending on an hypothesis identifier,
   [tactic_try_intros_until tac arg] first assumes that arg denotes a
   quantified hypothesis (denoted by name or by index) and try to
   introduce it in context before to apply [tac], otherwise assume the
   hypothesis is already in context and directly apply [tac] *)
val tactic_try_intros_until : (identifier,tactic_arg) parse_combinator


(*s Exact tactics. *)

val assumption         : tactic
val dyn_assumption     : tactic_arg list -> tactic

val exact_no_check      : constr -> tactic
val dyn_exact_no_check  : tactic_arg list -> tactic

val exact_check      : constr -> tactic
val dyn_exact_check  : tactic_arg list -> tactic

(*s Reduction tactics. *)

type 'a tactic_reduction = env -> enamed_declarations -> constr -> constr

val reduct_in_hyp     : 'a tactic_reduction -> hyp_location -> tactic
val reduct_option     : 'a tactic_reduction -> hyp_location option -> tactic
val reduct_in_concl   : 'a tactic_reduction -> tactic
val change_in_concl   : constr -> tactic

val change_in_hyp     : constr -> hyp_location -> tactic
val change_option     : constr -> hyp_location option -> tactic
val red_in_concl      : tactic
val red_in_hyp        : hyp_location        -> tactic
val red_option        : hyp_location option -> tactic
val hnf_in_concl      : tactic
val hnf_in_hyp        : hyp_location        -> tactic
val hnf_option        : hyp_location option -> tactic
val simpl_in_concl    : tactic
val simpl_in_hyp      : hyp_location        -> tactic
val simpl_option      : hyp_location option -> tactic
val normalise_in_concl: tactic
val normalise_in_hyp  : hyp_location        -> tactic
val normalise_option  : hyp_location option -> tactic
val unfold_in_concl   : (int list * Closure.evaluable_global_reference) list
  -> tactic
val unfold_in_hyp     : 
  (int list * Closure.evaluable_global_reference) list -> hyp_location -> tactic
val unfold_option     : 
  (int list * Closure.evaluable_global_reference) list -> hyp_location option
    -> tactic
val reduce            : red_expr -> hyp_location list -> tactic
val dyn_reduce        : tactic_arg list -> tactic
val dyn_change        : tactic_arg list -> tactic

val unfold_constr     : global_reference -> tactic
val pattern_option    : 
  (int list * constr * constr) list -> hyp_location option -> tactic

(*s Modification of the local context. *)

val clear         : identifier list -> tactic
val clear_one     : identifier -> tactic
val dyn_clear     : tactic_arg list -> tactic

val clear_body    : identifier list -> tactic
val dyn_clear_body : tactic_arg list -> tactic

val clear_clauses : identifier list -> tactic
val clear_clause  : identifier -> tactic

val new_hyp       : int option ->constr -> constr substitution -> tactic
val dyn_new_hyp   : tactic_arg list -> tactic

val dyn_move      : tactic_arg list -> tactic
val dyn_move_dep  : tactic_arg list -> tactic

(*s Resolution tactics. *)

val apply_type : constr -> constr list -> tactic
val apply_term : constr -> constr list -> tactic
val bring_hyps : identifier list -> tactic

val apply                 : constr      -> tactic
val apply_without_reduce  : constr      -> tactic
val apply_list            : constr list -> tactic
val apply_with_bindings   : (constr * constr substitution) -> tactic
val dyn_apply             : tactic_arg list -> tactic

val cut_and_apply         : constr -> tactic
val dyn_cut_and_apply     : tactic_arg list -> tactic

(*s Elimination tactics. *)

val general_elim   : constr * constr substitution ->
                     constr * constr substitution -> tactic
val default_elim   : constr * constr substitution -> tactic
val simplest_elim  : constr -> tactic
val dyn_elim       : tactic_arg list -> tactic

val old_induct       : identifier -> tactic
val old_induct_nodep : int        -> tactic
val dyn_old_induct : tactic_arg list -> tactic
val dyn_new_induct : tactic_arg list -> tactic

(*s Case analysis tactics. *)

val general_case_analysis : constr * constr substitution ->  tactic
val simplest_case         : constr -> tactic
val dyn_case              : tactic_arg list -> tactic

val destruct              : identifier -> tactic
val destruct_nodep        : int -> tactic
val dyn_destruct          : tactic_arg list -> tactic
val dyn_new_destruct      : tactic_arg list -> tactic

(*s Eliminations giving the type instead of the proof. *)

val case_type         : constr  -> tactic
val dyn_case_type     : tactic_arg list -> tactic

val elim_type         : constr  -> tactic
val dyn_elim_type     : tactic_arg list -> tactic


(*s Some eliminations which are frequently used. *)

val impE : identifier -> tactic
val andE : identifier -> tactic
val orE  : identifier -> tactic
val dImp : clause -> tactic
val dAnd : clause -> tactic
val dorE : bool -> clause ->tactic


(*s Introduction tactics. *)

val constructor_checking_bound : int option -> int -> 
                                 constr substitution  -> tactic
val one_constructor            : int -> constr substitution  -> tactic
val any_constructor            : tactic
val left                       : constr substitution -> tactic
val simplest_left              : tactic
val right                      : constr substitution -> tactic
val simplest_right             : tactic
val split                      : constr substitution -> tactic
val simplest_split             : tactic

val dyn_constructor        : tactic_arg list -> tactic
val dyn_left               : tactic_arg list -> tactic
val dyn_right              : tactic_arg list -> tactic
val dyn_split              : tactic_arg list -> tactic

(*s Logical connective tactics. *)

val absurd                      : constr          -> tactic
val dyn_absurd                  : tactic_arg list -> tactic

val contradiction_on_hyp        : identifier -> tactic
val contradiction               : tactic
val dyn_contradiction           : tactic_arg list -> tactic

val reflexivity    : tactic
val intros_reflexivity          : tactic
val dyn_reflexivity             : tactic_arg list -> tactic
 
val symmetry                    : tactic
val intros_symmetry             : tactic
val dyn_symmetry                : tactic_arg list -> tactic

val transitivity                : constr -> tactic
val intros_transitivity         : constr -> tactic
val dyn_transitivity            : tactic_arg list -> tactic

val cut                         : constr -> tactic
val cut_intro                   : constr -> tactic
val cut_replacing               : identifier -> constr -> tactic
val cut_in_parallel             : constr list -> tactic
val dyn_cut                     : tactic_arg list -> tactic
val dyn_true_cut                : tactic_arg list -> tactic
val dyn_lettac                  : tactic_arg list -> tactic
val dyn_forward                 : tactic_arg list -> tactic

val generalize                  : constr list -> tactic
val dyn_generalize              : tactic_arg list -> tactic 
val dyn_generalize_dep          : tactic_arg list -> tactic 

val tclABSTRACT : identifier option -> tactic -> tactic
