(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)


(* arnaud: fichier temporaire, pour éviter de tout casser sur le chemin 
   de Tactic du premier coup. Destiné à devenir tactic.mli. *)

(*i*)
open Names
open Term
open Environ
open Sign
open Reduction
open Evd
open Clenv
open Redexpr
open Ntacticals
open Proofview
open Libnames
open Genarg
open Tacexpr
open Nametab
open Rawterm
(*i*)

(* arnaud: trucs factices *)
type hyp_location = (int list list list * Names.identifier) * Tacexpr.hyp_location_flag
(* arnaud: /trucs factices *)

val inj_red_expr : red_expr -> (Goal.open_constr, evaluable_global_reference) red_expr_gen
val inj_ebindings : constr bindings -> Goal.open_constr bindings

(* Main tactics. *)

(*s General functions. *)

(* arnaud: à restaurer ?
val type_clenv_binding : goal sigma ->
  constr * constr -> Goal.open_constr bindings  -> constr
*)

val string_of_inductive : constr -> string
val head_constr       : constr -> constr list
val head_constr_bound : constr -> constr list -> constr list



exception Bound

(*** arnaud: commenté plus ou moins jusqu'à la fin, 
             virer les doublons avec intros.mli

(*s Primitive tactics. *)

val introduction    : identifier -> tactic
val refine          : constr -> tactic
val convert_concl   : constr -> cast_kind -> tactic
val convert_hyp     : named_declaration -> tactic
val thin            : identifier list -> tactic
val mutual_fix      :
  identifier -> int -> (identifier * int * constr) list -> tactic
val fix             : identifier option -> int -> tactic
val mutual_cofix    : identifier -> (identifier * constr) list -> tactic
val cofix           : identifier option -> tactic

(*s Introduction tactics. *)

val fresh_id : identifier list -> identifier -> goal sigma -> identifier
val find_intro_names : rel_context -> goal sigma -> identifier list

val intro                : tactic
val introf               : tactic
val intro_force          : bool -> tactic
val intro_move           : identifier option -> identifier option -> tactic
  (* [intro_avoiding idl] acts as intro but prevents the new identifier
     to belong to [idl] *)
val intro_avoiding       : identifier list -> tactic

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

(*s Introduction tactics with eliminations. *)

val intro_pattern     : identifier option -> intro_pattern_expr      -> tactic
val intro_patterns    : intro_pattern_expr list -> tactic
val intros_pattern    : identifier option -> intro_pattern_expr list -> tactic

(*s Exact tactics. *)

val assumption       : tactic
val exact_no_check   : constr -> tactic
val vm_cast_no_check : constr -> tactic
val exact_check      : constr -> tactic
val exact_proof      : Topconstr.constr_expr -> tactic

(*s Reduction tactics. *)

type tactic_reduction = env -> evar_map -> constr -> constr

val reduct_in_hyp     : tactic_reduction -> hyp_location -> tactic
val reduct_option     : tactic_reduction * cast_kind -> simple_clause -> tactic
val reduct_in_concl   : tactic_reduction * cast_kind -> tactic
val change_in_concl   : (int list * constr) option -> constr -> tactic
val change_in_hyp     : (int list * constr) option -> constr -> hyp_location ->
  tactic
val red_in_concl      : tactic
val red_in_hyp        : hyp_location        -> tactic
val red_option        : simple_clause -> tactic
val hnf_in_concl      : tactic
val hnf_in_hyp        : hyp_location        -> tactic
val hnf_option        : simple_clause -> tactic
val simpl_in_concl    : tactic
val simpl_in_hyp      : hyp_location        -> tactic
val simpl_option      : simple_clause -> tactic
val normalise_in_concl : tactic
val normalise_in_hyp  : hyp_location        -> tactic
val normalise_option  : simple_clause -> tactic
val normalise_vm_in_concl : tactic
val unfold_in_concl   : (int list * evaluable_global_reference) list -> tactic
val unfold_in_hyp     : 
  (int list * evaluable_global_reference) list -> hyp_location -> tactic
val unfold_option     : 
  (int list * evaluable_global_reference) list -> simple_clause
    -> tactic
val reduce            : red_expr -> clause -> tactic
val change            :
  (int list * constr) option -> constr -> clause -> tactic

val unfold_constr     : global_reference -> tactic
val pattern_option  : (int list * constr) list -> simple_clause -> tactic

(*s Modification of the local context. *)

val clear         : identifier list -> tactic
val clear_body    : identifier list -> tactic
val keep          : identifier list -> tactic

val new_hyp       : int option -> constr with_ebindings -> tactic

val move_hyp      : bool -> identifier -> identifier -> tactic
val rename_hyp    : (identifier * identifier) list -> tactic

(*s Resolution tactics. *)

val apply_type : constr -> constr list -> tactic
val apply_term : constr -> constr list -> tactic
val bring_hyps : named_context -> tactic

val apply                 : constr      -> tactic
val apply_without_reduce  : constr      -> tactic
val apply_list            : constr list -> tactic
val apply_with_ebindings_gen : evars_flag -> constr with_ebindings -> tactic
val apply_with_bindings   : constr with_bindings -> tactic
val apply_with_ebindings  : constr with_ebindings -> tactic
val eapply_with_bindings  : constr with_bindings -> tactic
val eapply_with_ebindings : constr with_ebindings -> tactic

val cut_and_apply         : constr -> tactic

val apply_in : evars_flag -> identifier -> constr with_ebindings list -> tactic

(*s Elimination tactics. *)


(*
   The general form of an induction principle is the following:
   
   forall prm1 prm2 ... prmp,                          (induction parameters)
   forall Q1...,(Qi:Ti_1 -> Ti_2 ->...-> Ti_ni),...Qq, (predicates)
   branch1, branch2, ... , branchr,                    (branches of the principle)
   forall (x1:Ti_1) (x2:Ti_2) ... (xni:Ti_ni),         (induction arguments)
   (HI: I prm1..prmp x1...xni)                         (optional main induction arg)
   -> (Qi x1...xni HI        (f prm1...prmp x1...xni)).(conclusion)
                   ^^        ^^^^^^^^^^^^^^^^^^^^^^^^
               optional                optional
               even if HI      argument added if principle
             present above   generated by functional induction
             [indarg]          [farg]

  HI is not present when the induction principle does not come directly from an
  inductive type (like when it is generated by functional induction for
  example). HI is present otherwise BUT may not appear in the conclusion
  (dependent principle). HI and (f...) cannot be both present.

  Principles taken from functional induction have the final (f...).
*)

(* [rel_contexts] and [rel_declaration] actually contain triples, and
   lists are actually in reverse order to fit [compose_prod]. *)
type elim_scheme = { 
  elimc: constr with_ebindings option;
  elimt: types;
  indref: global_reference option;
  params: rel_context;     (* (prm1,tprm1);(prm2,tprm2)...(prmp,tprmp) *)
  nparams: int;            (* number of parameters *)
  predicates: rel_context; (* (Qq, (Tq_1 -> Tq_2 ->...-> Tq_nq)), (Q1,...) *)
  npredicates: int;        (* Number of predicates *)
  branches: rel_context;   (* branchr,...,branch1 *)
  nbranches: int;          (* Number of branches *) 
  args: rel_context;       (* (xni, Ti_ni) ... (x1, Ti_1) *)
  nargs: int;              (* number of arguments *)
  indarg: rel_declaration option; (* Some (H,I prm1..prmp x1...xni) 
				     if HI is in premisses, None otherwise *)
  concl: types;            (* Qi x1...xni HI (f...), HI and (f...) 
			      are optional and mutually exclusive *)
  indarg_in_concl: bool;   (* true if HI appears at the end of conclusion *)
  farg_in_concl: bool;     (* true if (f...) appears at the end of conclusion *)
}


val compute_elim_sig : ?elimc: constr with_ebindings -> types -> elim_scheme

val general_elim  : evars_flag ->
  constr with_ebindings -> constr with_ebindings -> ?allow_K:bool -> tactic
val general_elim_in : evars_flag -> 
  identifier -> constr with_ebindings -> constr with_ebindings -> tactic

val default_elim  : evars_flag -> constr with_ebindings -> tactic
val simplest_elim : constr -> tactic
*)

val elim : evars_flag -> 
           constr with_ebindings Goal.sensitive -> 
           constr with_ebindings option Goal.sensitive -> 
           unit tactic

(*
val simple_induct : quantified_hypothesis -> tactic

val new_induct : evars_flag -> constr with_ebindings induction_arg list -> 
  constr with_ebindings option -> intro_pattern_expr -> tactic

(*s Case analysis tactics. *)

val general_case_analysis : evars_flag -> constr with_ebindings ->  tactic
val simplest_case         : constr -> tactic

val simple_destruct          : quantified_hypothesis -> tactic
*)
val new_destruct : evars_flag Goal.sensitive -> 
                   constr with_ebindings induction_arg list Goal.sensitive -> 
                   constr with_ebindings option Goal.sensitive -> 
                   intro_pattern_expr Goal.sensitive -> 
                   unit tactic

(*
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
                                 Goal.open_constr bindings  -> tactic
val one_constructor            : int -> Goal.open_constr bindings  -> tactic
val any_constructor            : tactic option -> tactic

val left                       : constr bindings -> tactic
val right                      : constr bindings -> tactic
val split                      : constr bindings -> tactic

val left_with_ebindings        : Goal.open_constr bindings -> tactic
val right_with_ebindings       : Goal.open_constr bindings -> tactic
val split_with_ebindings       : Goal.open_constr bindings -> tactic

val simplest_left              : tactic
val simplest_right             : tactic
val simplest_split             : tactic

(*s Logical connective tactics. *)

val register_setoid_reflexivity : tactic -> unit
val reflexivity_red             : bool -> tactic
val reflexivity                 : tactic
val intros_reflexivity          : tactic

val register_setoid_symmetry : tactic -> unit
val symmetry_red                : bool -> tactic
val symmetry                    : tactic
val register_setoid_symmetry_in : (identifier -> tactic) -> unit
val symmetry_in                 : identifier -> tactic
val intros_symmetry             : clause -> tactic

val register_setoid_transitivity : (constr -> tactic) -> unit
val transitivity_red            : bool -> constr -> tactic
val transitivity                : constr -> tactic
val intros_transitivity         : constr -> tactic

val cut                         : constr -> tactic
val cut_intro                   : constr -> tactic
val cut_replacing               : 
  identifier -> constr -> (tactic -> tactic) -> tactic
val cut_in_parallel             : constr list -> tactic

val assert_as : bool -> intro_pattern_expr -> constr -> tactic
val forward   : tactic option -> intro_pattern_expr -> constr -> tactic

val true_cut                    : name -> constr -> tactic
val letin_tac                   : bool -> name -> constr -> clause -> tactic
val assert_tac                  : bool -> name -> constr -> tactic
val generalize                  : constr list -> tactic
val generalize_dep              : constr  -> tactic

val tclABSTRACT : identifier option -> tactic -> tactic

val admit_as_an_axiom : tactic

val abstract_generalize : identifier -> tactic
***)
