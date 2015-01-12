(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Names
open Term
open Context
open Environ
open Proof_type
open Evd
open Clenv
open Redexpr
open Globnames
open Tacexpr
open Pattern
open Unification
open Misctypes
open Locus

(** Main tactics. *)

(** {6 General functions. } *)

val is_quantified_hypothesis : Id.t -> goal sigma -> bool

(** {6 Primitive tactics. } *)

val introduction    : ?check:bool -> Id.t -> unit Proofview.tactic
val refine          : constr -> tactic
val convert_concl   : ?check:bool -> types -> cast_kind -> unit Proofview.tactic
val convert_hyp     : ?check:bool -> named_declaration -> unit Proofview.tactic
val convert_concl_no_check : types -> cast_kind -> unit Proofview.tactic
val convert_hyp_no_check : named_declaration -> unit Proofview.tactic
val thin            : Id.t list -> tactic
val mutual_fix      :
  Id.t -> int -> (Id.t * int * constr) list -> int -> tactic
val fix             : Id.t option -> int -> tactic
val mutual_cofix    : Id.t -> (Id.t * constr) list -> int -> tactic
val cofix           : Id.t option -> tactic

val convert         : constr -> constr -> unit Proofview.tactic
val convert_leq     : constr -> constr -> unit Proofview.tactic

(** {6 Introduction tactics. } *)

val fresh_id_in_env : Id.t list -> Id.t -> env -> Id.t
val fresh_id : Id.t list -> Id.t -> goal sigma -> Id.t
val find_intro_names : rel_context -> goal sigma -> Id.t list

val intro                : unit Proofview.tactic
val introf               : unit Proofview.tactic
val intro_move        : Id.t option -> Id.t move_location -> unit Proofview.tactic
val intro_move_avoid  : Id.t option -> Id.t list -> Id.t move_location -> unit Proofview.tactic

  (** [intro_avoiding idl] acts as intro but prevents the new Id.t
     to belong to [idl] *)
val intro_avoiding       : Id.t list -> unit Proofview.tactic

val intro_replacing      : Id.t -> unit Proofview.tactic
val intro_using          : Id.t -> unit Proofview.tactic
val intro_mustbe_force   : Id.t -> unit Proofview.tactic
val intro_then           : (Id.t -> unit Proofview.tactic) -> unit Proofview.tactic
val intros_using         : Id.t list -> unit Proofview.tactic
val intros_replacing     : Id.t list -> unit Proofview.tactic
val intros_possibly_replacing : Id.t list -> unit Proofview.tactic

val intros               : unit Proofview.tactic

(** [depth_of_quantified_hypothesis b h g] returns the index of [h] in
   the conclusion of goal [g], up to head-reduction if [b] is [true] *)
val depth_of_quantified_hypothesis :
  bool -> quantified_hypothesis -> goal sigma -> int

val intros_until         : quantified_hypothesis -> unit Proofview.tactic

val intros_clearing      : bool list -> unit Proofview.tactic

(** Assuming a tactic [tac] depending on an hypothesis Id.t,
   [try_intros_until tac arg] first assumes that arg denotes a
   quantified hypothesis (denoted by name or by index) and try to
   introduce it in context before to apply [tac], otherwise assume the
   hypothesis is already in context and directly apply [tac] *)

val try_intros_until :
  (Id.t -> unit Proofview.tactic) -> quantified_hypothesis -> unit Proofview.tactic

(** Apply a tactic on a quantified hypothesis, an hypothesis in context
   or a term with bindings *)

val onInductionArg :
  (clear_flag -> constr with_bindings -> unit Proofview.tactic) ->
    constr with_bindings induction_arg -> unit Proofview.tactic

(** Tell if a used hypothesis should be cleared by default or not *)

val use_clear_hyp_by_default : unit -> bool

(** {6 Introduction tactics with eliminations. } *)

val intro_patterns : intro_patterns -> unit Proofview.tactic
val intro_patterns_to : Id.t move_location -> intro_patterns ->
  unit Proofview.tactic
val intro_patterns_bound_to : int -> Id.t move_location -> intro_patterns ->
  unit Proofview.tactic
val intro_pattern_to : Id.t move_location -> delayed_open_constr intro_pattern_expr ->
  unit Proofview.tactic

(** Implements user-level "intros", with [] standing for "**" *)
val intros_patterns : intro_patterns -> unit Proofview.tactic

(** {6 Exact tactics. } *)

val assumption       : unit Proofview.tactic
val exact_no_check   : constr -> tactic
val vm_cast_no_check : constr -> tactic
val exact_check      : constr -> unit Proofview.tactic
val exact_proof      : Constrexpr.constr_expr -> tactic

(** {6 Reduction tactics. } *)

type tactic_reduction = env -> evar_map -> constr -> constr

type change_arg = evar_map -> evar_map * constr

val reduct_in_hyp     : ?check:bool -> tactic_reduction -> hyp_location -> tactic
val reduct_option     : ?check:bool -> tactic_reduction * cast_kind -> goal_location -> tactic
val reduct_in_concl   : tactic_reduction * cast_kind -> tactic
val change_in_concl   : (occurrences * constr_pattern) option -> change_arg -> unit Proofview.tactic
val change_concl      : constr -> unit Proofview.tactic
val change_in_hyp     : (occurrences * constr_pattern) option -> change_arg ->
                        hyp_location -> unit Proofview.tactic
val red_in_concl      : tactic
val red_in_hyp        : hyp_location -> tactic
val red_option        : goal_location -> tactic
val hnf_in_concl      : tactic
val hnf_in_hyp        : hyp_location -> tactic
val hnf_option        : goal_location -> tactic
val simpl_in_concl    : tactic
val simpl_in_hyp      : hyp_location -> tactic
val simpl_option      : goal_location -> tactic
val normalise_in_concl : tactic
val normalise_in_hyp  : hyp_location -> tactic
val normalise_option  : goal_location -> tactic
val normalise_vm_in_concl : tactic
val unfold_in_concl   :
  (occurrences * evaluable_global_reference) list -> tactic
val unfold_in_hyp     :
  (occurrences * evaluable_global_reference) list -> hyp_location -> tactic
val unfold_option     :
  (occurrences * evaluable_global_reference) list -> goal_location -> tactic
val change            :
  constr_pattern option -> change_arg -> clause -> tactic
val pattern_option    :
  (occurrences * constr) list -> goal_location -> tactic
val reduce            : red_expr -> clause -> tactic
val unfold_constr     : global_reference -> tactic

(** {6 Modification of the local context. } *)

val clear         : Id.t list -> tactic
val clear_body    : Id.t list -> unit Proofview.tactic
val unfold_body   : Id.t -> tactic
val keep          : Id.t list -> unit Proofview.tactic
val apply_clear_request : clear_flag -> bool -> constr -> unit Proofview.tactic

val specialize    : constr with_bindings -> tactic

val move_hyp      : Id.t -> Id.t move_location -> tactic
val rename_hyp    : (Id.t * Id.t) list -> unit Proofview.tactic

val revert        : Id.t list -> unit Proofview.tactic

(** {6 Resolution tactics. } *)

val apply_type : constr -> constr list -> tactic
val bring_hyps : named_context -> unit Proofview.tactic

val apply                 : constr -> unit Proofview.tactic
val eapply                : constr -> unit Proofview.tactic

val apply_with_bindings_gen :
  advanced_flag -> evars_flag -> (clear_flag * constr with_bindings located) list -> unit Proofview.tactic

val apply_with_delayed_bindings_gen :
  advanced_flag -> evars_flag -> (clear_flag * delayed_open_constr_with_bindings located) list -> unit Proofview.tactic

val apply_with_bindings   : constr with_bindings -> unit Proofview.tactic
val eapply_with_bindings  : constr with_bindings -> unit Proofview.tactic

val cut_and_apply         : constr -> unit Proofview.tactic

val apply_in :
  advanced_flag -> evars_flag -> clear_flag -> Id.t -> 
    (clear_flag * constr with_bindings located) list ->
    intro_pattern option -> unit Proofview.tactic

val apply_delayed_in :
  advanced_flag -> evars_flag -> clear_flag -> Id.t -> 
    (clear_flag * delayed_open_constr_with_bindings located) list ->
    intro_pattern option -> unit Proofview.tactic

(** {6 Elimination tactics. } *)

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

(** [rel_contexts] and [rel_declaration] actually contain triples, and
   lists are actually in reverse order to fit [compose_prod]. *)
type elim_scheme = {
  elimc: constr with_bindings option;
  elimt: types;
  indref: global_reference option;
  params: rel_context;     (** (prm1,tprm1);(prm2,tprm2)...(prmp,tprmp) *)
  nparams: int;            (** number of parameters *)
  predicates: rel_context; (** (Qq, (Tq_1 -> Tq_2 ->...-> Tq_nq)), (Q1,...) *)
  npredicates: int;        (** Number of predicates *)
  branches: rel_context;   (** branchr,...,branch1 *)
  nbranches: int;          (** Number of branches *)
  args: rel_context;       (** (xni, Ti_ni) ... (x1, Ti_1) *)
  nargs: int;              (** number of arguments *)
  indarg: rel_declaration option; (** Some (H,I prm1..prmp x1...xni)
				     if HI is in premisses, None otherwise *)
  concl: types;            (** Qi x1...xni HI (f...), HI and (f...)
			      are optional and mutually exclusive *)
  indarg_in_concl: bool;   (** true if HI appears at the end of conclusion *)
  farg_in_concl: bool;     (** true if (f...) appears at the end of conclusion *)
}

val compute_elim_sig : ?elimc: constr with_bindings -> types -> elim_scheme

(** elim principle with the index of its inductive arg *)
type eliminator = {
  elimindex : int option;  (** None = find it automatically *)
  elimrename : (bool * int array) option; (** None = don't rename Prop hyps with H-names *)
  elimbody : constr with_bindings
}

val general_elim  : evars_flag -> clear_flag ->
  constr with_bindings -> eliminator -> unit Proofview.tactic

val general_elim_clause : evars_flag -> unify_flags -> identifier option ->
  clausenv -> eliminator -> unit Proofview.tactic

val default_elim  : evars_flag -> clear_flag -> constr with_bindings ->
  unit Proofview.tactic
val simplest_elim : constr -> unit Proofview.tactic
val elim :
  evars_flag -> clear_flag -> constr with_bindings -> constr with_bindings option -> unit Proofview.tactic

val simple_induct : quantified_hypothesis -> unit Proofview.tactic

val induction : evars_flag -> clear_flag -> constr -> or_and_intro_pattern option ->
  constr with_bindings option -> unit Proofview.tactic

(** {6 Case analysis tactics. } *)

val general_case_analysis : evars_flag -> clear_flag -> constr with_bindings ->  unit Proofview.tactic
val simplest_case         : constr -> unit Proofview.tactic

val simple_destruct       : quantified_hypothesis -> unit Proofview.tactic
val destruct : evars_flag -> clear_flag -> constr -> or_and_intro_pattern option ->
  constr with_bindings option -> unit Proofview.tactic

(** {6 Generic case analysis / induction tactics. } *)

(** Implements user-level "destruct" and "induction" *)

val induction_destruct : rec_flag -> evars_flag ->
  (delayed_open_constr_with_bindings induction_arg
   * (intro_pattern_naming option * or_and_intro_pattern option)
   * clause option) list *
  constr with_bindings option -> unit Proofview.tactic

(** {6 Eliminations giving the type instead of the proof. } *)

val case_type         : types -> unit Proofview.tactic
val elim_type         : types -> unit Proofview.tactic

(** {6 Constructor tactics. } *)

val constructor_tac      : evars_flag -> int option -> int ->
  constr bindings -> unit Proofview.tactic
val any_constructor      : evars_flag -> unit Proofview.tactic option -> unit Proofview.tactic
val one_constructor      : int -> constr bindings  -> unit Proofview.tactic

val left                 : constr bindings -> unit Proofview.tactic
val right                : constr bindings -> unit Proofview.tactic
val split                : constr bindings -> unit Proofview.tactic

val left_with_bindings  : evars_flag -> constr bindings -> unit Proofview.tactic
val right_with_bindings : evars_flag -> constr bindings -> unit Proofview.tactic
val split_with_bindings : evars_flag -> constr bindings list -> unit Proofview.tactic

val simplest_left        : unit Proofview.tactic
val simplest_right       : unit Proofview.tactic
val simplest_split       : unit Proofview.tactic

(** {6 Equality tactics. } *)

val setoid_reflexivity : unit Proofview.tactic Hook.t
val reflexivity_red             : bool -> unit Proofview.tactic
val reflexivity                 : unit Proofview.tactic
val intros_reflexivity          : unit Proofview.tactic

val setoid_symmetry : unit Proofview.tactic Hook.t
val symmetry_red                : bool -> unit Proofview.tactic
val symmetry                    : unit Proofview.tactic
val setoid_symmetry_in : (Id.t -> unit Proofview.tactic) Hook.t
val intros_symmetry             : clause -> unit Proofview.tactic

val setoid_transitivity : (constr option -> unit Proofview.tactic) Hook.t
val transitivity_red            : bool -> constr option -> unit Proofview.tactic
val transitivity                : constr -> unit Proofview.tactic
val etransitivity               : unit Proofview.tactic
val intros_transitivity         : constr option -> unit Proofview.tactic

(** {6 Cut tactics. } *)

val assert_before_replacing: Id.t -> types -> unit Proofview.tactic
val assert_after_replacing : Id.t -> types -> unit Proofview.tactic
val assert_before : Name.t -> types -> unit Proofview.tactic
val assert_after  : Name.t -> types -> unit Proofview.tactic

val assert_as     : (* true = before *) bool ->
  intro_pattern option -> constr -> unit Proofview.tactic

(** Implements the tactics assert, enough and pose proof; note that "by"
    applies on the first goal for both assert and enough *)

val assert_by  : Name.t -> types -> unit Proofview.tactic ->
  unit Proofview.tactic
val enough_by  : Name.t -> types -> unit Proofview.tactic ->
  unit Proofview.tactic
val pose_proof : Name.t -> constr ->
  unit Proofview.tactic

(** Common entry point for user-level "assert", "enough" and "pose proof" *)

val forward   : bool -> unit Proofview.tactic option ->
  intro_pattern option -> constr -> unit Proofview.tactic

(** Implements the tactic cut, actually a modus ponens rule *)

val cut        : types -> unit Proofview.tactic

(** {6 Tactics for adding local definitions. } *)

val letin_tac : (bool * intro_pattern_naming) option ->
  Name.t -> constr -> types option -> clause -> unit Proofview.tactic

(** Common entry point for user-level "set", "pose" and "remember" *)

val letin_pat_tac : (bool * intro_pattern_naming) option ->
  Name.t -> pending_constr -> clause -> unit Proofview.tactic

(** {6 Generalize tactics. } *)

val generalize      : constr list -> tactic
val generalize_gen  : ((occurrences * constr) * Name.t) list -> tactic
val new_generalize  : constr list -> unit Proofview.tactic
val new_generalize_gen  : ((occurrences * constr) * Name.t) list -> unit Proofview.tactic

val generalize_dep  : ?with_let:bool (** Don't lose let bindings *) -> constr  -> tactic

(** {6 Other tactics. } *)

val unify           : ?state:Names.transparent_state -> constr -> constr -> unit Proofview.tactic

val tclABSTRACT : Id.t option -> unit Proofview.tactic -> unit Proofview.tactic

val admit_as_an_axiom : unit Proofview.tactic

val abstract_generalize : ?generalize_vars:bool -> ?force_dep:bool -> Id.t -> unit Proofview.tactic
val specialize_eqs : Id.t -> tactic

val general_rewrite_clause :
  (bool -> evars_flag -> constr with_bindings -> clause -> unit Proofview.tactic) Hook.t

val subst_one :
  (bool -> Id.t -> Id.t * constr * bool -> unit Proofview.tactic) Hook.t

val declare_intro_decomp_eq :
  ((int -> unit Proofview.tactic) -> Coqlib.coq_eq_data * types *
   (types * constr * constr) ->
   constr * types -> unit Proofview.tactic) -> unit

(** {6 Simple form of basic tactics. } *)

module Simple : sig
  (** Simplified version of some of the above tactics *)

  val intro           : Id.t -> unit Proofview.tactic
  val generalize      : constr list -> tactic
  val generalize_gen  : (constr Locus.with_occurrences * Name.t) list -> tactic

  val apply  : constr -> unit Proofview.tactic
  val eapply : constr -> unit Proofview.tactic
  val elim   : constr -> unit Proofview.tactic
  val case   : constr -> unit Proofview.tactic
  val apply_in : identifier -> constr -> unit Proofview.tactic

end

(** {6 Tacticals defined directly in term of Proofview} *)

module New : sig

  val refine : ?unsafe:bool -> (Evd.evar_map -> Evd.evar_map*constr) -> unit Proofview.tactic
  (** [refine ?unsafe c] is [Proofview.Refine.refine ?unsafe c]
      followed by beta-iota-reduction of the conclusion. *)

  val reduce_after_refine : unit Proofview.tactic
  (** The reducing tactic called after {!refine}. *)

  open Proofview
  val exact_proof : Constrexpr.constr_expr -> unit tactic
end
