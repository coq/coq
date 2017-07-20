(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Warning, this file should respect the dependency order established
   in Coq. To see such order issue the comand:

   ```
   bash -c 'for i in kernel intf library engine pretyping interp proofs parsing printing tactics vernac stm toplevel; do echo -e "\n## $i files" && cat ${i}/${i}.mllib; done && echo -e "\n## highparsing files" && cat parsing/highparsing.mllib' > API/link
   ```

   Note however that files in intf/ are located manually now as their
   conceptual linking order in the Coq codebase is incorrect (but it
   works due to these files being implementation-free.

   See below in the file for their concrete position.
*)

open Kernel_API
open Intf_API
open Engine_API
open Library_API
open Interp_API
open Pretyping_API
open Proofs_API

(************************************************************************)
(* Modules from tactics/                                                *)
(************************************************************************)

module Tacticals :
sig
  open Proof_type

  val tclORELSE        : tactic -> tactic -> tactic
  val tclDO : int -> tactic -> tactic
  val tclIDTAC : tactic
  val tclFAIL : int -> Pp.std_ppcmds -> tactic
  val tclTHEN : tactic -> tactic -> tactic
  val tclTHENLIST      : tactic list -> tactic
  val pf_constr_of_global :
    Globnames.global_reference -> (EConstr.constr -> Proof_type.tactic) -> Proof_type.tactic
  val tclMAP : ('a -> tactic) -> 'a list -> tactic
  val tclTRY           : tactic -> tactic
  val tclCOMPLETE      : tactic -> tactic
  val tclTHENS : tactic -> tactic list -> tactic
  val tclFIRST         : tactic list -> tactic
  val tclTHENFIRST     : tactic -> tactic -> tactic
  val tclTHENLAST      : tactic -> tactic -> tactic
  val tclTHENSFIRSTn   : tactic -> tactic array -> tactic -> tactic
  val tclTHENSLASTn    : tactic -> tactic -> tactic array -> tactic
  val tclSOLVE         : tactic list -> tactic

  val onClause   : (Names.Id.t option -> tactic) -> Locus.clause -> tactic
  val onAllHypsAndConcl : (Names.Id.t option -> tactic) -> tactic
  val onLastHypId : (Names.Id.t -> tactic) -> tactic
  val onNthHypId : int -> (Names.Id.t -> tactic) -> tactic
  val onNLastHypsId : int -> (Names.Id.t list -> tactic) -> tactic

  val tclTHENSEQ : tactic list -> tactic
  [@@ocaml.deprecated "alias of API.Tacticals.tclTHENLIST"]

  val nLastDecls : int -> Goal.goal Evd.sigma -> EConstr.named_context

  val tclTHEN_i : tactic -> (int -> tactic) -> tactic

  val tclPROGRESS : tactic -> tactic

  val elimination_sort_of_goal : Goal.goal Evd.sigma -> Sorts.family

  module New :
  sig
    open Proofview
    val tclORELSE0 : unit tactic -> unit tactic -> unit tactic
    val tclFAIL : int -> Pp.std_ppcmds -> 'a tactic
    val pf_constr_of_global : Globnames.global_reference -> EConstr.constr tactic
    val tclTHEN : unit tactic -> unit tactic -> unit tactic
    val tclTHENS : unit tactic -> unit tactic list -> unit tactic
    val tclFIRST : unit tactic list -> unit tactic
    val tclZEROMSG : ?loc:Loc.t -> Pp.std_ppcmds -> 'a tactic
    val tclORELSE  : unit tactic -> unit tactic -> unit tactic
    val tclREPEAT : unit tactic -> unit tactic
    val tclTRY : unit tactic -> unit tactic
    val tclTHENFIRST : unit tactic -> unit tactic -> unit tactic
    val tclPROGRESS :  unit Proofview.tactic -> unit Proofview.tactic
    val tclTHENS3PARTS : unit tactic -> unit tactic array -> unit tactic -> unit tactic array -> unit tactic
    val tclDO : int -> unit tactic -> unit tactic
    val tclTIMEOUT : int -> unit tactic -> unit tactic
    val tclTIME : string option -> 'a tactic -> 'a tactic
    val tclOR : unit tactic -> unit tactic -> unit tactic
    val tclONCE : unit tactic -> unit tactic
    val tclEXACTLY_ONCE : unit tactic -> unit tactic
    val tclIFCATCH :
      unit tactic  ->
      (unit -> unit tactic) ->
      (unit -> unit tactic) -> unit tactic
    val tclSOLVE : unit tactic list -> unit tactic
    val tclCOMPLETE : 'a tactic -> 'a tactic
    val tclSELECT : Vernacexpr.goal_selector -> 'a tactic -> 'a tactic
    val tclWITHHOLES : bool -> 'a tactic -> Evd.evar_map -> 'a tactic
    val tclDELAYEDWITHHOLES : bool -> 'a Tactypes.delayed_open -> ('a -> unit tactic) -> unit tactic
    val tclTHENLIST : unit tactic list -> unit tactic
    val tclTHENLAST  : unit tactic -> unit tactic -> unit tactic
    val tclMAP : ('a -> unit tactic) -> 'a list -> unit tactic
    val tclIDTAC : unit tactic
    val tclIFTHENELSE : unit tactic -> unit tactic -> unit tactic -> unit tactic
    val tclIFTHENSVELSE : unit tactic -> unit tactic array -> unit tactic -> unit tactic
  end
end

module Hipattern :
sig
  exception NoEquationFound
  type 'a matching_function = Evd.evar_map -> EConstr.constr -> 'a option
  type testing_function = Evd.evar_map -> EConstr.constr -> bool
  val is_disjunction : ?strict:bool -> ?onlybinary:bool -> testing_function
  val match_with_disjunction : ?strict:bool -> ?onlybinary:bool -> (EConstr.constr * EConstr.constr list) matching_function
  val match_with_equality_type : (EConstr.constr * EConstr.constr list) matching_function
  val is_empty_type : testing_function
  val is_unit_type : testing_function
  val is_unit_or_eq_type : testing_function
  val is_conjunction : ?strict:bool -> ?onlybinary:bool -> testing_function
  val match_with_conjunction : ?strict:bool -> ?onlybinary:bool -> (EConstr.constr * EConstr.constr list) matching_function
  val match_with_imp_term : (EConstr.constr * EConstr.constr) matching_function
  val match_with_forall_term : (Names.Name.t * EConstr.constr * EConstr.constr) matching_function
  val match_with_nodep_ind : (EConstr.constr * EConstr.constr list * int) matching_function
  val match_with_sigma_type : (EConstr.constr * EConstr.constr list) matching_function
end

module Ind_tables :
sig
  type individual
  type 'a scheme_kind

  val check_scheme : 'a scheme_kind -> Names.inductive -> bool
  val find_scheme : ?mode:Declare.internal_flag -> 'a scheme_kind -> Names.inductive -> Names.Constant.t * Safe_typing.private_constants
  val pr_scheme_kind : 'a scheme_kind -> Pp.std_ppcmds
end

module Elimschemes :
sig
  val case_scheme_kind_from_prop : Ind_tables.individual Ind_tables.scheme_kind
  val case_dep_scheme_kind_from_type_in_prop : Ind_tables.individual Ind_tables.scheme_kind
  val case_scheme_kind_from_type : Ind_tables.individual Ind_tables.scheme_kind
  val case_dep_scheme_kind_from_type : Ind_tables.individual Ind_tables.scheme_kind
  val case_dep_scheme_kind_from_prop : Ind_tables.individual Ind_tables.scheme_kind
end

module Tactics :
sig
  open Proofview

  type change_arg = Pattern.patvar_map -> Evd.evar_map -> Evd.evar_map * EConstr.constr
  type tactic_reduction = Environ.env -> Evd.evar_map -> EConstr.constr -> EConstr.constr

  type elim_scheme =
    {
      elimc: EConstr.constr Misctypes.with_bindings option;
      elimt: EConstr.types;
      indref: Globnames.global_reference option;
      params: EConstr.rel_context;
      nparams: int;
      predicates: EConstr.rel_context;
      npredicates: int;
      branches: EConstr.rel_context;
      nbranches: int;
      args: EConstr.rel_context;
      nargs: int;
      indarg: EConstr.rel_declaration option;
      concl: EConstr.types;
      indarg_in_concl: bool;
      farg_in_concl: bool;
    }

  val unify : ?state:Names.transparent_state -> EConstr.constr -> EConstr.constr -> unit Proofview.tactic
  val intro_then : (Names.Id.t -> unit Proofview.tactic) -> unit Proofview.tactic
  val reflexivity : unit tactic
  val change_concl : EConstr.constr -> unit tactic
  val apply : EConstr.constr -> unit tactic
  val normalise_vm_in_concl : unit tactic
  val assert_before : Names.Name.t -> EConstr.types -> unit tactic
  val exact_check : EConstr.constr -> unit tactic
  val simplest_elim : EConstr.constr -> unit tactic
  val introf : unit tactic
  val cut : EConstr.types -> unit tactic
  val convert_concl : ?check:bool -> EConstr.types -> Constr.cast_kind -> unit tactic
  val intro_using : Names.Id.t -> unit tactic
  val intro : unit tactic
  val fresh_id_in_env : Names.Id.t list -> Names.Id.t -> Environ.env -> Names.Id.t
  val is_quantified_hypothesis : Names.Id.t -> 'a Goal.t -> bool
  val tclABSTRACT : ?opaque:bool -> Names.Id.t option -> unit Proofview.tactic -> unit Proofview.tactic
  val intro_patterns : bool -> Tactypes.intro_patterns -> unit Proofview.tactic
  val apply_with_delayed_bindings_gen :
    Misctypes.advanced_flag -> Misctypes.evars_flag -> (Misctypes.clear_flag * Tactypes.delayed_open_constr_with_bindings Loc.located) list -> unit Proofview.tactic
  val apply_delayed_in :
    Misctypes.advanced_flag -> Misctypes.evars_flag -> Names.Id.t ->
    (Misctypes.clear_flag * Tactypes.delayed_open_constr_with_bindings Loc.located) list ->
    Tactypes.intro_pattern option -> unit Proofview.tactic
  val elim :
    Misctypes.evars_flag -> Misctypes.clear_flag -> EConstr.constr Misctypes.with_bindings -> EConstr.constr Misctypes.with_bindings option -> unit Proofview.tactic
  val general_case_analysis : Misctypes.evars_flag -> Misctypes.clear_flag -> EConstr.constr Misctypes.with_bindings ->  unit Proofview.tactic
  val mutual_fix :
    Names.Id.t -> int -> (Names.Id.t * int * EConstr.constr) list -> int -> unit Proofview.tactic
  val mutual_cofix : Names.Id.t -> (Names.Id.t * EConstr.constr) list -> int -> unit Proofview.tactic
  val forward   : bool -> unit Proofview.tactic option option ->
                  Tactypes.intro_pattern option -> EConstr.constr -> unit Proofview.tactic
  val generalize_gen : (EConstr.constr Locus.with_occurrences * Names.Name.t) list -> unit Proofview.tactic
  val letin_tac : (bool * Tactypes.intro_pattern_naming) option ->
                  Names.Name.t -> EConstr.constr -> EConstr.types option -> Locus.clause -> unit Proofview.tactic
  val letin_pat_tac : Misctypes.evars_flag ->
                      (bool * Tactypes.intro_pattern_naming) option ->
                      Names.Name.t ->
                      Evd.evar_map * EConstr.constr ->
                      Locus.clause -> unit Proofview.tactic
  val induction_destruct : Misctypes.rec_flag -> Misctypes.evars_flag ->
                           (Tactypes.delayed_open_constr_with_bindings Misctypes.destruction_arg
                            * (Tactypes.intro_pattern_naming option * Tactypes.or_and_intro_pattern option)
                            * Locus.clause option) list *
                             EConstr.constr Misctypes.with_bindings option -> unit Proofview.tactic
  val reduce : Redexpr.red_expr -> Locus.clause -> unit Proofview.tactic
  val change : Pattern.constr_pattern option -> change_arg -> Locus.clause -> unit Proofview.tactic
  val intros_reflexivity : unit Proofview.tactic
  val exact_no_check : EConstr.constr -> unit Proofview.tactic
  val assumption : unit Proofview.tactic
  val intros_transitivity : EConstr.constr option -> unit Proofview.tactic
  val vm_cast_no_check : EConstr.constr -> unit Proofview.tactic
  val native_cast_no_check : EConstr.constr -> unit Proofview.tactic
  val case_type : EConstr.types -> unit Proofview.tactic
  val elim_type : EConstr.types -> unit Proofview.tactic
  val cut_and_apply : EConstr.constr -> unit Proofview.tactic
  val left_with_bindings  : Misctypes.evars_flag -> EConstr.constr Misctypes.bindings -> unit Proofview.tactic
  val right_with_bindings : Misctypes.evars_flag -> EConstr.constr Misctypes.bindings -> unit Proofview.tactic
  val any_constructor : Misctypes.evars_flag -> unit Proofview.tactic option -> unit Proofview.tactic
  val constructor_tac : Misctypes.evars_flag -> int option -> int ->
                        EConstr.constr Misctypes.bindings -> unit Proofview.tactic
  val specialize : EConstr.constr Misctypes.with_bindings -> Tactypes.intro_pattern option -> unit Proofview.tactic
  val intros_symmetry : Locus.clause -> unit Proofview.tactic
  val split_with_bindings : Misctypes.evars_flag -> EConstr.constr Misctypes.bindings list -> unit Proofview.tactic
  val intros_until : Misctypes.quantified_hypothesis -> unit Proofview.tactic
  val intro_move : Names.Id.t option -> Names.Id.t Misctypes.move_location -> unit Proofview.tactic
  val move_hyp : Names.Id.t -> Names.Id.t Misctypes.move_location -> unit Proofview.tactic
  val rename_hyp : (Names.Id.t * Names.Id.t) list -> unit Proofview.tactic
  val revert : Names.Id.t list -> unit Proofview.tactic
  val simple_induct : Misctypes.quantified_hypothesis -> unit Proofview.tactic
  val simple_destruct : Misctypes.quantified_hypothesis -> unit Proofview.tactic
  val fix : Names.Id.t option -> int -> unit Proofview.tactic
  val cofix : Names.Id.t option -> unit Proofview.tactic
  val keep : Names.Id.t list -> unit Proofview.tactic
  val clear : Names.Id.t list -> unit Proofview.tactic
  val clear_body : Names.Id.t list -> unit Proofview.tactic
  val generalize_dep  : ?with_let:bool (** Don't lose let bindings *) -> EConstr.constr  -> unit Proofview.tactic
  val force_destruction_arg : Misctypes.evars_flag -> Environ.env -> Evd.evar_map ->
    Tactypes.delayed_open_constr_with_bindings Misctypes.destruction_arg ->
    Evd.evar_map * EConstr.constr Misctypes.with_bindings Misctypes.destruction_arg
  val apply_with_bindings   : EConstr.constr Misctypes.with_bindings -> unit Proofview.tactic
  val abstract_generalize : ?generalize_vars:bool -> ?force_dep:bool -> Names.Id.t -> unit Proofview.tactic
  val specialize_eqs : Names.Id.t -> unit Proofview.tactic
  val generalize : EConstr.constr list -> unit Proofview.tactic
  val simplest_case : EConstr.constr -> unit Proofview.tactic
  val introduction : ?check:bool -> Names.Id.t -> unit Proofview.tactic
  val convert_concl_no_check : EConstr.types -> Constr.cast_kind -> unit Proofview.tactic
  val reduct_in_concl : tactic_reduction * Constr.cast_kind -> unit Proofview.tactic
  val reduct_in_hyp : ?check:bool -> tactic_reduction -> Locus.hyp_location -> unit Proofview.tactic
  val convert_hyp_no_check : EConstr.named_declaration -> unit Proofview.tactic
  val reflexivity_red : bool -> unit Proofview.tactic
  val symmetry_red : bool -> unit Proofview.tactic
  val eapply : EConstr.constr -> unit Proofview.tactic
  val transitivity_red : bool -> EConstr.constr option -> unit Proofview.tactic
  val assert_after_replacing : Names.Id.t -> EConstr.types -> unit Proofview.tactic
  val intros : unit Proofview.tactic
  val setoid_reflexivity : unit Proofview.tactic Hook.t
  val setoid_symmetry : unit Proofview.tactic Hook.t
  val setoid_symmetry_in : (Names.Id.t -> unit Proofview.tactic) Hook.t
  val setoid_transitivity : (EConstr.constr option -> unit Proofview.tactic) Hook.t
  val unfold_in_concl :
    (Locus.occurrences * Names.evaluable_global_reference) list -> unit Proofview.tactic
  val intros_using : Names.Id.t list -> unit Proofview.tactic
  val simpl_in_concl : unit Proofview.tactic
  val reduct_option : ?check:bool -> tactic_reduction * Constr.cast_kind -> Locus.goal_location -> unit Proofview.tactic
  val simplest_split : unit Proofview.tactic
  val unfold_in_hyp :
    (Locus.occurrences * Names.evaluable_global_reference) list -> Locus.hyp_location -> unit Proofview.tactic
  val split : EConstr.constr Misctypes.bindings -> unit Proofview.tactic
  val red_in_concl : unit Proofview.tactic
  val change_in_concl   : (Locus.occurrences * Pattern.constr_pattern) option -> change_arg -> unit Proofview.tactic
  val eapply_with_bindings  : EConstr.constr Misctypes.with_bindings -> unit Proofview.tactic
  val assert_by  : Names.Name.t -> EConstr.types -> unit Proofview.tactic ->
                   unit Proofview.tactic
  val intro_avoiding : Names.Id.t list -> unit Proofview.tactic
  val pose_proof : Names.Name.t -> EConstr.constr -> unit Proofview.tactic
  val pattern_option :  (Locus.occurrences * EConstr.constr) list -> Locus.goal_location -> unit Proofview.tactic
  val compute_elim_sig : Evd.evar_map -> ?elimc:EConstr.constr Misctypes.with_bindings -> EConstr.types -> elim_scheme
  val try_intros_until :
    (Names.Id.t -> unit Proofview.tactic) -> Misctypes.quantified_hypothesis -> unit Proofview.tactic
  val cache_term_by_tactic_then :
    opaque:bool -> ?goal_type:(EConstr.constr option) -> Names.Id.t ->
    Decl_kinds.goal_kind -> unit Proofview.tactic -> (EConstr.constr -> EConstr.constr list -> unit Proofview.tactic) -> unit Proofview.tactic
  val apply_type : EConstr.constr -> EConstr.constr list -> unit Proofview.tactic
  val hnf_in_concl : unit Proofview.tactic
  val intro_mustbe_force : Names.Id.t -> unit Proofview.tactic

  module New :
  sig
    val refine : typecheck:bool -> (Evd.evar_map -> Evd.evar_map * EConstr.constr) -> unit Proofview.tactic
    val reduce_after_refine : unit Proofview.tactic
  end
  module Simple :
  sig
    val intro : Names.Id.t -> unit Proofview.tactic
    val apply  : EConstr.constr -> unit Proofview.tactic
    val case : EConstr.constr -> unit Proofview.tactic
  end
end

module Elim :
sig
  val h_decompose : Names.inductive list -> EConstr.constr -> unit Proofview.tactic
  val h_double_induction : Misctypes.quantified_hypothesis -> Misctypes.quantified_hypothesis-> unit Proofview.tactic
  val h_decompose_or : EConstr.constr -> unit Proofview.tactic
  val h_decompose_and : EConstr.constr -> unit Proofview.tactic
end

module Equality :
sig
  type orientation = bool
  type freeze_evars_flag = bool
  type dep_proof_flag = bool
  type conditions =
    | Naive
    | FirstSolved
    | AllMatches

  val build_selector :
    Environ.env -> Evd.evar_map -> int -> EConstr.constr -> EConstr.types ->
    EConstr.constr -> EConstr.constr -> Evd.evar_map * EConstr.constr
  val replace : EConstr.constr -> EConstr.constr -> unit Proofview.tactic
  val general_rewrite :
    orientation -> Locus.occurrences -> freeze_evars_flag -> dep_proof_flag ->
    ?tac:(unit Proofview.tactic * conditions) -> EConstr.constr -> unit Proofview.tactic
  val inj : Tactypes.intro_patterns option -> Misctypes.evars_flag ->
            Misctypes.clear_flag -> EConstr.constr Misctypes.with_bindings -> unit Proofview.tactic
  val general_multi_rewrite :
    Misctypes.evars_flag -> (bool * Misctypes.multi * Misctypes.clear_flag * Tactypes.delayed_open_constr_with_bindings) list ->
    Locus.clause -> (unit Proofview.tactic * conditions) option -> unit Proofview.tactic
  val replace_in_clause_maybe_by : EConstr.constr -> EConstr.constr -> Locus.clause -> unit Proofview.tactic option -> unit Proofview.tactic
  val replace_term : bool option -> EConstr.constr -> Locus.clause -> unit Proofview.tactic
  val dEq : Misctypes.evars_flag -> EConstr.constr Misctypes.with_bindings Misctypes.destruction_arg option -> unit Proofview.tactic
  val discr_tac : Misctypes.evars_flag ->
                  EConstr.constr Misctypes.with_bindings Misctypes.destruction_arg option -> unit Proofview.tactic
  val injClause    : Tactypes.intro_patterns option -> Misctypes.evars_flag ->
                     EConstr.constr Misctypes.with_bindings Misctypes.destruction_arg option -> unit Proofview.tactic

  val simpleInjClause : Misctypes.evars_flag ->
                        EConstr.constr Misctypes.with_bindings Misctypes.destruction_arg option ->
                        unit Proofview.tactic
  val rewriteInConcl : bool -> EConstr.constr -> unit Proofview.tactic
  val rewriteInHyp : bool -> EConstr.constr -> Names.Id.t -> unit Proofview.tactic
  val cutRewriteInConcl : bool -> EConstr.constr -> unit Proofview.tactic
  val cutRewriteInHyp : bool -> EConstr.types -> Names.Id.t -> unit Proofview.tactic
  val general_rewrite_ebindings_clause : Names.Id.t option ->
                                         orientation -> Locus.occurrences -> freeze_evars_flag -> dep_proof_flag ->
                                         ?tac:(unit Proofview.tactic * conditions) -> EConstr.constr Misctypes.with_bindings -> Misctypes.evars_flag -> unit Proofview.tactic
  val subst : Names.Id.t list -> unit Proofview.tactic

  type subst_tactic_flags = {
    only_leibniz : bool;
    rewrite_dependent_proof : bool
  }
  val subst_all : ?flags:subst_tactic_flags -> unit -> unit Proofview.tactic

  val general_rewrite_in :
    orientation -> Locus.occurrences -> freeze_evars_flag -> dep_proof_flag ->
    ?tac:(unit Proofview.tactic * conditions) -> Names.Id.t -> EConstr.constr -> Misctypes.evars_flag -> unit Proofview.tactic

  val general_setoid_rewrite_clause :
  (Names.Id.t option -> orientation -> Locus.occurrences -> EConstr.constr Misctypes.with_bindings ->
   new_goals:EConstr.constr list -> unit Proofview.tactic) Hook.t

  val discrConcl   : unit Proofview.tactic
  val rewriteLR : ?tac:(unit Proofview.tactic * conditions) -> EConstr.constr -> unit Proofview.tactic
  val rewriteRL : ?tac:(unit Proofview.tactic * conditions) -> EConstr.constr  -> unit Proofview.tactic
  val general_rewrite_bindings :
    orientation -> Locus.occurrences -> freeze_evars_flag -> dep_proof_flag ->
    ?tac:(unit Proofview.tactic * conditions) -> EConstr.constr Misctypes.with_bindings -> Misctypes.evars_flag -> unit Proofview.tactic
  val discriminable : Environ.env -> Evd.evar_map -> EConstr.constr -> EConstr.constr -> bool
  val discrHyp : Names.Id.t -> unit Proofview.tactic
  val injectable : Environ.env -> Evd.evar_map -> EConstr.constr -> EConstr.constr -> bool
  val injHyp : Misctypes.clear_flag -> Names.Id.t -> unit Proofview.tactic
  val subst_gen : bool -> Names.Id.t list -> unit Proofview.tactic
end

module Contradiction :
sig
  val contradiction : EConstr.constr Misctypes.with_bindings option -> unit Proofview.tactic
  val absurd : EConstr.constr -> unit Proofview.tactic
end

module Inv :
sig
  val dinv :
    Misctypes.inversion_kind -> EConstr.constr option ->
    Tactypes.or_and_intro_pattern option -> Misctypes.quantified_hypothesis -> unit Proofview.tactic
  val inv_clause :
    Misctypes.inversion_kind -> Tactypes.or_and_intro_pattern option -> Names.Id.t list ->
    Misctypes.quantified_hypothesis -> unit Proofview.tactic
  val inv_clear_tac : Names.Id.t -> unit Proofview.tactic
  val inv_tac : Names.Id.t -> unit Proofview.tactic
  val dinv_tac : Names.Id.t -> unit Proofview.tactic
  val dinv_clear_tac : Names.Id.t -> unit Proofview.tactic
  val inv : Misctypes.inversion_kind -> Tactypes.or_and_intro_pattern option ->
            Misctypes.quantified_hypothesis -> unit Proofview.tactic
end

module Leminv :
sig
  val lemInv_clause :
    Misctypes.quantified_hypothesis -> EConstr.constr -> Names.Id.t list -> unit Proofview.tactic
  val add_inversion_lemma_exn :
    Names.Id.t -> Constrexpr.constr_expr -> Misctypes.glob_sort -> bool -> (Names.Id.t -> unit Proofview.tactic) ->
    unit
end

module Hints :
sig

  type raw_hint = EConstr.t * EConstr.types * Univ.universe_context_set

  type 'a hint_ast =
    | Res_pf     of 'a (* Hint Apply *)
    | ERes_pf    of 'a (* Hint EApply *)
    | Give_exact of 'a
    | Res_pf_THEN_trivial_fail of 'a (* Hint Immediate *)
    | Unfold_nth of Names.evaluable_global_reference       (* Hint Unfold *)
    | Extern     of Genarg.glob_generic_argument (* Hint Extern *)

  type hint

  type debug =
    | Debug | Info | Off

  type 'a hints_path_atom_gen =
    | PathHints of 'a list
    | PathAny

  type hint_term =
    | IsGlobRef of Globnames.global_reference
    | IsConstr of EConstr.constr * Univ.ContextSet.t

  type hint_db_name = string
  type hint_info = (Names.Id.t list * Pattern.constr_pattern) Vernacexpr.hint_info_gen
  type hnf = bool
  type hints_path_atom = Globnames.global_reference hints_path_atom_gen

  type 'a hints_path_gen =
    | PathAtom of 'a hints_path_atom_gen
    | PathStar of 'a hints_path_gen
    | PathSeq of 'a hints_path_gen * 'a hints_path_gen
    | PathOr of 'a hints_path_gen * 'a hints_path_gen
    | PathEmpty
    | PathEpsilon

  type hints_path = Globnames.global_reference hints_path_gen

  type hints_entry =
    | HintsResolveEntry of (hint_info * Decl_kinds.polymorphic * hnf * hints_path_atom * hint_term) list
    | HintsImmediateEntry of (hints_path_atom * Decl_kinds.polymorphic * hint_term) list
    | HintsCutEntry of hints_path
    | HintsUnfoldEntry of Names.evaluable_global_reference list
    | HintsTransparencyEntry of Names.evaluable_global_reference list * bool
    | HintsModeEntry of Globnames.global_reference * Vernacexpr.hint_mode list
    | HintsExternEntry of hint_info * Genarg.glob_generic_argument

  type 'a with_metadata = private {
      pri     : int;
      poly    : Decl_kinds.polymorphic;
      pat     : Pattern.constr_pattern option;
      name    : hints_path_atom;
      db : string option;
      secvars : Names.Id.Pred.t;
      code    : 'a;
    }
  type full_hint = hint with_metadata

  module Hint_db :
  sig
    type t
    val empty : ?name:hint_db_name -> Names.transparent_state -> bool -> t
    val transparent_state : t -> Names.transparent_state
    val iter : (Globnames.global_reference option ->
                Vernacexpr.hint_mode array list -> full_hint list -> unit) -> t -> unit
  end
  type hint_db = Hint_db.t

  val add_hints : bool -> hint_db_name list -> hints_entry -> unit
  val searchtable_map : hint_db_name -> hint_db
  val pp_hints_path_atom : ('a -> Pp.std_ppcmds) -> 'a hints_path_atom_gen -> Pp.std_ppcmds
  val pp_hints_path_gen : ('a -> Pp.std_ppcmds) -> 'a hints_path_gen -> Pp.std_ppcmds
  val glob_hints_path_atom :
    Libnames.reference hints_path_atom_gen -> Globnames.global_reference hints_path_atom_gen
  val pp_hints_path : hints_path -> Pp.std_ppcmds
  val glob_hints_path :
    Libnames.reference hints_path_gen -> Globnames.global_reference hints_path_gen
  val typeclasses_db : hint_db_name
  val add_hints_init : (unit -> unit) -> unit
  val create_hint_db : bool -> hint_db_name -> Names.transparent_state -> bool -> unit
  val empty_hint_info : 'a Vernacexpr.hint_info_gen
  val repr_hint : hint -> (raw_hint * Clenv.clausenv) hint_ast
  val pr_hint_db : Hint_db.t -> Pp.std_ppcmds
end

module Auto :
sig
  val default_auto : unit Proofview.tactic
  val full_trivial : ?debug:Hints.debug ->
                     Tactypes.delayed_open_constr list -> unit Proofview.tactic
  val h_auto   : ?debug:Hints.debug ->
                 int option -> Tactypes.delayed_open_constr list -> Hints.hint_db_name list option -> unit Proofview.tactic
  val h_trivial : ?debug:Hints.debug ->
                  Tactypes.delayed_open_constr list -> Hints.hint_db_name list option -> unit Proofview.tactic
  val new_full_auto : ?debug:Hints.debug ->
                      int -> Tactypes.delayed_open_constr list -> unit Proofview.tactic
  val full_auto : ?debug:Hints.debug ->
                  int -> Tactypes.delayed_open_constr list -> unit Proofview.tactic
  val new_auto : ?debug:Hints.debug ->
                 int -> Tactypes.delayed_open_constr list -> Hints.hint_db_name list -> unit Proofview.tactic
  val default_full_auto : unit Proofview.tactic
end

module Eauto :
sig
  val e_assumption : unit Proofview.tactic
  val e_give_exact : ?flags:Unification.unify_flags -> EConstr.constr -> unit Proofview.tactic
  val prolog_tac : Tactypes.delayed_open_constr list -> int -> unit Proofview.tactic
  val make_dimension : int option -> int option -> bool * int
  val gen_eauto : ?debug:Hints.debug -> bool * int -> Tactypes.delayed_open_constr list ->
                  Hints.hint_db_name list option -> unit Proofview.tactic
  val autounfold_tac : Hints.hint_db_name list option -> Locus.clause -> unit Proofview.tactic
  val autounfold_one : Hints.hint_db_name list -> Locus.hyp_location option -> unit Proofview.tactic
  val eauto_with_bases :
    ?debug:Hints.debug -> bool * int -> Tactypes.delayed_open_constr list -> Hints.hint_db list -> Proof_type.tactic
end

module Class_tactics :
sig

  type search_strategy =
    | Dfs
    | Bfs

  val set_typeclasses_debug : bool -> unit
  val set_typeclasses_strategy : search_strategy -> unit
  val set_typeclasses_depth : int option -> unit
  val typeclasses_eauto : ?only_classes:bool -> ?st:Names.transparent_state -> ?strategy:search_strategy ->
                        depth:(Int.t option) ->
                        Hints.hint_db_name list -> unit Proofview.tactic
  val head_of_constr : Names.Id.t -> EConstr.constr -> unit Proofview.tactic
  val not_evar : EConstr.constr -> unit Proofview.tactic
  val is_ground : EConstr.constr -> unit Proofview.tactic
  val autoapply : EConstr.constr -> Hints.hint_db_name -> unit Proofview.tactic
  val catchable : exn -> bool
end

module Eqdecide :
sig
  val compare : EConstr.constr -> EConstr.constr -> unit Proofview.tactic
  val decideEqualityGoal : unit Proofview.tactic
end

module Autorewrite :
sig
  type rew_rule = { rew_lemma: Constr.t;
                    rew_type: Term.types;
                    rew_pat: Constr.t;
                    rew_ctx: Univ.ContextSet.t;
                    rew_l2r: bool;
                    rew_tac: Genarg.glob_generic_argument option }
  type raw_rew_rule = (Constr.t Univ.in_universe_context_set * bool *
                         Genarg.raw_generic_argument option)
                        Loc.located
  val auto_multi_rewrite : ?conds:Equality.conditions -> string list -> Locus.clause -> unit Proofview.tactic
  val auto_multi_rewrite_with : ?conds:Equality.conditions -> unit Proofview.tactic -> string list -> Locus.clause -> unit Proofview.tactic
  val add_rew_rules : string -> raw_rew_rule list -> unit
  val find_rewrites : string -> rew_rule list
  val find_matches : string -> Constr.t -> rew_rule list
  val print_rewrite_hintdb : string -> Pp.std_ppcmds
end

(************************************************************************)
(* End of modules from tactics/                                         *)
(************************************************************************)
