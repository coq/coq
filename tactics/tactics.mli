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
open Sign
open Tacmach
open Proof_type
open Reduction
open Evd
open Evar_refiner
open Clenv
open Tacred
open Tacticals
open Libnames
open Tacexpr
open Nametab
open Rawterm

(* Main tactics. *)

(*s General functions. *)

val type_clenv_binding : named_context sigma ->
  constr * constr -> constr substitution  -> constr

val string_of_inductive : constr -> string
val head_constr       : constr -> constr list
val head_constr_bound : constr -> constr list -> constr list
val is_quantified_hypothesis : identifier -> goal sigma -> bool

exception Bound

(*s Primitive tactics. *)

val introduction    : identifier -> tactic
val refine          : constr -> tactic
val convert_concl   : constr -> tactic
val convert_hyp     : named_declaration -> tactic
val thin            : identifier list -> tactic
val mutual_fix      :
  identifier -> int -> (identifier * int * constr) list -> tactic
val fix             : identifier option -> int -> tactic
val mutual_cofix    : identifier -> (identifier * constr) list -> tactic
val cofix           : identifier option -> tactic

(*s Introduction tactics. *)

val next_global_ident_away : identifier -> identifier list -> identifier
val fresh_id : identifier list -> identifier -> goal sigma -> identifier

val intro                : tactic
val introf               : tactic
val intro_force          : bool -> tactic
val intro_move           : identifier option -> identifier option -> tactic

val intro_replacing      : identifier -> tactic
val intro_using          : identifier -> tactic
val intro_mustbe_force   : identifier -> tactic
val intros_using         : identifier list -> tactic
val intro_erasing        : identifier -> tactic
val intros_replacing     : identifier list -> tactic

val intros               : tactic

(* [depth_of_quantified_hypothesis b h g] returns the index of [h] in
   the conclusion of goal [g], up to head-reduction if [b] is [true] *)
val depth_of_quantified_hypothesis :
  bool -> quantified_hypothesis -> goal sigma -> int

val intros_until_n_wored : int -> tactic
val intros_until         : quantified_hypothesis -> tactic

val intros_clearing      : bool list -> tactic

(* Assuming a tactic [tac] depending on an hypothesis identifier,
   [try_intros_until tac arg] first assumes that arg denotes a
   quantified hypothesis (denoted by name or by index) and try to
   introduce it in context before to apply [tac], otherwise assume the
   hypothesis is already in context and directly apply [tac] *)

val try_intros_until :
  (identifier -> tactic) -> quantified_hypothesis -> tactic

(*s Exact tactics. *)

val assumption         : tactic
val exact_no_check      : constr -> tactic
val exact_check      : constr -> tactic
val exact_proof      : Coqast.t -> tactic

(*s Reduction tactics. *)

type tactic_reduction = env -> evar_map -> constr -> constr

val reduct_in_hyp     : tactic_reduction -> hyp_location -> tactic
val reduct_option     : tactic_reduction -> hyp_location option -> tactic
val reduct_in_concl   : tactic_reduction -> tactic
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
val change            : constr -> hyp_location list -> tactic

val unfold_constr     : global_reference -> tactic
val pattern_option  : (int list * constr) list -> hyp_location option -> tactic

(*s Modification of the local context. *)

val clear         : identifier list -> tactic

val clear_body    : identifier list -> tactic

val new_hyp       : int option ->constr -> constr substitution -> tactic

val move_hyp      : bool -> identifier -> identifier -> tactic
val rename_hyp    : identifier -> identifier -> tactic

(*s Resolution tactics. *)

val apply_type : constr -> constr list -> tactic
val apply_term : constr -> constr list -> tactic
val bring_hyps : named_context -> tactic

val apply                 : constr      -> tactic
val apply_without_reduce  : constr      -> tactic
val apply_list            : constr list -> tactic
val apply_with_bindings   : constr with_bindings -> tactic

val cut_and_apply         : constr -> tactic

(*s Elimination tactics. *)

val general_elim  : constr with_bindings -> constr with_bindings -> tactic
val default_elim  : constr with_bindings -> tactic
val simplest_elim : constr -> tactic
val elim          : constr with_bindings -> constr with_bindings option -> tactic
val general_elim_in : identifier -> constr * constr substitution ->
                      constr * constr substitution -> tactic

val old_induct     : quantified_hypothesis -> tactic
val general_elim_in : identifier -> constr * constr substitution ->
                      constr * constr substitution -> tactic

val new_induct     : constr induction_arg -> tactic

(*s Case analysis tactics. *)

val general_case_analysis : constr with_bindings ->  tactic
val simplest_case         : constr -> tactic

val old_destruct          : quantified_hypothesis -> tactic
val new_destruct          : constr induction_arg -> tactic

(*s Eliminations giving the type instead of the proof. *)

val case_type         : constr  -> tactic
val elim_type         : constr  -> tactic

(*s Some eliminations which are frequently used. *)

val impE : identifier -> tactic
val andE : identifier -> tactic
val orE  : identifier -> tactic
val dImp : clause -> tactic
val dAnd : clause -> tactic
val dorE : bool -> clause ->tactic


(*s Introduction tactics. *)

val constructor_tac            : int option -> int -> 
                                 constr substitution  -> tactic
val one_constructor            : int -> constr substitution  -> tactic
val any_constructor            : tactic option -> tactic
val left                       : constr substitution -> tactic
val simplest_left              : tactic
val right                      : constr substitution -> tactic
val simplest_right             : tactic
val split                      : constr substitution -> tactic
val simplest_split             : tactic

(*s Logical connective tactics. *)

val reflexivity                 : tactic
val intros_reflexivity          : tactic

val symmetry                    : tactic
val intros_symmetry             : tactic

val transitivity                : constr -> tactic
val intros_transitivity         : constr -> tactic

val cut                         : constr -> tactic
val cut_intro                   : constr -> tactic
val cut_replacing               : identifier -> constr -> tactic
val cut_in_parallel             : constr list -> tactic

val true_cut                    : identifier option -> constr -> tactic
val letin_tac                   : bool -> name -> constr -> 
                                  identifier clause_pattern -> tactic
val forward                     : bool -> name -> constr -> tactic
val generalize                  : constr list -> tactic
val generalize_dep              : constr  -> tactic

val tclABSTRACT : identifier option -> tactic -> tactic
