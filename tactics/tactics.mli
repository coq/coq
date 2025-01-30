(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open EConstr
open Environ
open Evd
open Redexpr
open Pattern
open Unification
open Tactypes
open Locus
open Ltac_pretype

(** Main tactics defined in ML. This file is huge and should probably be split
    in more reasonable units at some point. Because of its size and age, the
    implementation features various styles and stages of the proof engine.
    This has to be uniformized someday. *)

(** {6 General functions. } *)

val is_quantified_hypothesis : Id.t -> Proofview.Goal.t -> bool

(** {6 Primitive tactics. } *)

exception NotConvertible

val introduction    : Id.t -> unit Proofview.tactic
val convert_concl   : cast:bool -> check:bool -> types -> cast_kind -> unit Proofview.tactic
val convert_hyp     : check:bool -> reorder:bool -> named_declaration -> unit Proofview.tactic
val mutual_fix      :
  Id.t -> int -> (Id.t * int * constr) list -> int -> unit Proofview.tactic
val fix             : Id.t -> int -> unit Proofview.tactic
val mutual_cofix    : Id.t -> (Id.t * constr) list -> int -> unit Proofview.tactic
val cofix           : Id.t -> unit Proofview.tactic

val convert         : constr -> constr -> unit Proofview.tactic
val convert_leq     : constr -> constr -> unit Proofview.tactic

(** {6 Introduction tactics. } *)

val fresh_id_in_env : Id.Set.t -> Id.t -> env -> Id.t
val find_intro_names : env -> Evd.evar_map -> rel_context -> Id.t list

val intro                : unit Proofview.tactic
val introf               : unit Proofview.tactic
val intro_move        : Id.t option -> Id.t Logic.move_location -> unit Proofview.tactic
val intro_move_avoid  : Id.t option -> Id.Set.t -> Id.t Logic.move_location -> unit Proofview.tactic
val intros_move       : (Id.t * Id.t Logic.move_location) list -> unit Proofview.tactic

  (** [intro_avoiding idl] acts as intro but prevents the new Id.t
     to belong to [idl] *)
val intro_avoiding       : Id.Set.t -> unit Proofview.tactic

val intro_replacing      : Id.t -> unit Proofview.tactic
val intro_using          : Id.t -> unit Proofview.tactic
[@@ocaml.deprecated "(8.13) Prefer [intro_using_then] to avoid renaming issues."]
val intro_using_then     : Id.t -> (Id.t -> unit Proofview.tactic) -> unit Proofview.tactic
val intro_mustbe_force   : Id.t -> unit Proofview.tactic
val intros_mustbe_force  : Id.t list -> unit Proofview.tactic
val intro_then           : (Id.t -> unit Proofview.tactic) -> unit Proofview.tactic
val intros_using         : Id.t list -> unit Proofview.tactic
[@@ocaml.deprecated "(8.13) Prefer [intros_using_then] to avoid renaming issues."]
val intros_using_then    : Id.t list -> (Id.t list -> unit Proofview.tactic) -> unit Proofview.tactic
val intros_replacing     : Id.t list -> unit Proofview.tactic
val intros_possibly_replacing : Id.t list -> unit Proofview.tactic

(** [auto_intros_tac names] handles Automatic Introduction of binders *)
val auto_intros_tac : Names.Name.t list -> unit Proofview.tactic

val intros               : unit Proofview.tactic

val intros_until         : quantified_hypothesis -> unit Proofview.tactic

val intros_clearing      : bool list -> unit Proofview.tactic

(** Assuming a tactic [tac] depending on an hypothesis Id.t,
   [try_intros_until tac arg] first assumes that arg denotes a
   quantified hypothesis (denoted by name or by index) and try to
   introduce it in context before to apply [tac], otherwise assume the
   hypothesis is already in context and directly apply [tac] *)

val try_intros_until :
  (Id.t -> unit Proofview.tactic) -> quantified_hypothesis -> unit Proofview.tactic

type evars_flag = bool     (* true = pose evars       false = fail on evars *)
type rec_flag = bool       (* true = recursive        false = not recursive *)
type advanced_flag = bool  (* true = advanced         false = basic *)
type clear_flag = bool option (* true = clear hyp, false = keep hyp, None = use default *)

(** Apply a tactic on a quantified hypothesis, an hypothesis in context
   or a term with bindings *)

type 'a core_destruction_arg =
  | ElimOnConstr of 'a
  | ElimOnIdent of lident
  | ElimOnAnonHyp of int

type 'a destruction_arg =
  clear_flag * 'a core_destruction_arg

val onInductionArg :
  (clear_flag -> constr with_bindings -> unit Proofview.tactic) ->
    constr with_bindings destruction_arg -> unit Proofview.tactic

val force_destruction_arg : evars_flag -> env -> evar_map ->
    delayed_open_constr_with_bindings destruction_arg ->
    evar_map * constr with_bindings destruction_arg

val finish_evar_resolution : ?flags:Pretyping.inference_flags ->
  env -> evar_map -> (evar_map option * constr) -> evar_map * constr

(** Tell if a used hypothesis should be cleared by default or not *)

val use_clear_hyp_by_default : unit -> bool

(** {6 Introduction tactics with eliminations. } *)

val intro_patterns : evars_flag -> intro_patterns -> unit Proofview.tactic
val intro_patterns_to : evars_flag -> Id.t Logic.move_location -> intro_patterns ->
  unit Proofview.tactic
val intro_patterns_bound_to : evars_flag -> int -> Id.t Logic.move_location -> intro_patterns ->
  unit Proofview.tactic
val intro_pattern_to : evars_flag -> Id.t Logic.move_location -> delayed_open_constr intro_pattern_expr ->
  unit Proofview.tactic

(** Implements user-level "intros", with [] standing for "**" *)
val intros_patterns : evars_flag -> intro_patterns -> unit Proofview.tactic

(** {6 Exact tactics. } *)

val assumption       : unit Proofview.tactic
val exact_no_check   : constr -> unit Proofview.tactic
val vm_cast_no_check : constr -> unit Proofview.tactic
val native_cast_no_check : constr -> unit Proofview.tactic
val exact_check      : constr -> unit Proofview.tactic
val exact_proof      : Constrexpr.constr_expr -> unit Proofview.tactic

(** {6 Reduction tactics. } *)

type tactic_reduction = Reductionops.reduction_function
type e_tactic_reduction = Reductionops.e_reduction_function

type change_arg = patvar_map -> env -> evar_map -> (evar_map * constr) Tacred.change

val make_change_arg   : constr -> change_arg
val reduct_in_hyp     : check:bool -> reorder:bool -> tactic_reduction -> hyp_location -> unit Proofview.tactic
val reduct_option     : check:bool -> tactic_reduction * cast_kind -> goal_location -> unit Proofview.tactic
val reduct_in_concl : cast:bool -> check:bool -> tactic_reduction * cast_kind -> unit Proofview.tactic
val e_reduct_in_concl : cast:bool -> check:bool -> e_tactic_reduction * cast_kind -> unit Proofview.tactic
val change_in_concl   : check:bool -> (occurrences * constr_pattern) option -> change_arg -> unit Proofview.tactic
val change_concl      : constr -> unit Proofview.tactic
val change_in_hyp     : check:bool -> (occurrences * constr_pattern) option -> change_arg ->
                        hyp_location -> unit Proofview.tactic
val red_in_concl      : unit Proofview.tactic
val red_in_hyp        : hyp_location -> unit Proofview.tactic
val red_option        : goal_location -> unit Proofview.tactic
val hnf_in_concl      : unit Proofview.tactic
val hnf_in_hyp        : hyp_location -> unit Proofview.tactic
val hnf_option        : goal_location -> unit Proofview.tactic
val simpl_in_concl    : unit Proofview.tactic
val simpl_in_hyp      : hyp_location -> unit Proofview.tactic
val simpl_option      : goal_location -> unit Proofview.tactic
val normalise_in_concl : unit Proofview.tactic
val normalise_in_hyp  : hyp_location -> unit Proofview.tactic
val normalise_option  : goal_location -> unit Proofview.tactic
val normalise_vm_in_concl : unit Proofview.tactic
val unfold_in_concl   :
  (occurrences * Evaluable.t) list -> unit Proofview.tactic
val unfold_in_hyp     :
  (occurrences * Evaluable.t) list -> hyp_location -> unit Proofview.tactic
val unfold_option     :
  (occurrences * Evaluable.t) list -> goal_location -> unit Proofview.tactic
val change            :
  check:bool -> constr_pattern option -> change_arg -> clause -> unit Proofview.tactic
val pattern_option    :
  (occurrences * constr) list -> goal_location -> unit Proofview.tactic
val reduce            : red_expr -> clause -> unit Proofview.tactic
val unfold_constr     : GlobRef.t -> unit Proofview.tactic

(** {6 Modification of the local context. } *)

val clear         : Id.t list -> unit Proofview.tactic
val clear_body    : Id.t list -> unit Proofview.tactic
val unfold_body   : Id.t -> unit Proofview.tactic
val keep          : Id.t list -> unit Proofview.tactic
val apply_clear_request : clear_flag -> bool -> Id.t option -> unit Proofview.tactic

val specialize    : constr with_bindings -> intro_pattern option -> unit Proofview.tactic

val move_hyp      : Id.t -> Id.t Logic.move_location -> unit Proofview.tactic
val rename_hyp    : (Id.t * Id.t) list -> unit Proofview.tactic

(** {6 Resolution tactics. } *)

val apply_type : typecheck:bool -> constr -> constr list -> unit Proofview.tactic

val apply                 : constr -> unit Proofview.tactic
val eapply : ?with_classes:bool -> constr -> unit Proofview.tactic

val apply_with_bindings_gen :
  ?with_classes:bool -> advanced_flag -> evars_flag -> (clear_flag * constr with_bindings CAst.t) list -> unit Proofview.tactic

val apply_with_delayed_bindings_gen :
  advanced_flag -> evars_flag -> (clear_flag * constr with_bindings Proofview.tactic CAst.t) list -> unit Proofview.tactic

val apply_with_bindings   : constr with_bindings -> unit Proofview.tactic
val eapply_with_bindings : ?with_classes:bool -> constr with_bindings -> unit Proofview.tactic

val cut_and_apply         : constr -> unit Proofview.tactic

val apply_in :
  advanced_flag -> evars_flag -> Id.t ->
    (clear_flag * constr with_bindings CAst.t) list ->
    intro_pattern option -> unit Proofview.tactic

val apply_delayed_in :
  advanced_flag -> evars_flag -> Id.t ->
    (clear_flag * constr with_bindings Proofview.tactic CAst.t) list ->
    intro_pattern option -> unit Proofview.tactic -> unit Proofview.tactic

(** {6 Elimination tactics. } *)

val general_elim_clause : evars_flag -> unify_flags -> Id.t option ->
  ((metavariable list * Unification.Meta.t) * EConstr.t * EConstr.types) -> Constant.t -> unit Proofview.tactic

val default_elim  : evars_flag -> clear_flag -> constr with_bindings ->
  unit Proofview.tactic
val simplest_elim : constr -> unit Proofview.tactic
val elim :
  evars_flag -> clear_flag -> constr with_bindings -> constr with_bindings option -> unit Proofview.tactic

(** {6 Case analysis tactics. } *)

val general_case_analysis : evars_flag -> clear_flag -> constr with_bindings ->  unit Proofview.tactic
val simplest_case         : constr -> unit Proofview.tactic

(** {6 Eliminations giving the type instead of the proof. } *)

val exfalso : unit Proofview.tactic

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
val split_with_delayed_bindings : evars_flag -> constr bindings delayed_open list -> unit Proofview.tactic

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

(** Implements the tactics assert, enough and pose proof; note that "by"
    applies on the first goal for both assert and enough *)

val assert_by  : Name.t -> types -> unit Proofview.tactic ->
  unit Proofview.tactic
val enough_by  : Name.t -> types -> unit Proofview.tactic ->
  unit Proofview.tactic
val pose_proof : Name.t -> constr ->
  unit Proofview.tactic

(** Common entry point for user-level "assert", "enough" and "pose proof" *)

val forward   : bool -> unit Proofview.tactic option option ->
  intro_pattern option -> constr -> unit Proofview.tactic

(** Implements the tactic cut, actually a modus ponens rule *)

val cut        : types -> unit Proofview.tactic

(** {6 Tactics for adding local definitions. } *)

val pose_tac : Name.t -> constr -> unit Proofview.tactic

val letin_tac : (bool * intro_pattern_naming) option ->
  Name.t -> constr -> types option -> clause -> unit Proofview.tactic

(** Common entry point for user-level "set", "pose" and "remember" *)

val letin_pat_tac : evars_flag -> (bool * intro_pattern_naming) option ->
  Name.t -> (evar_map option * constr) -> clause -> unit Proofview.tactic

(** {6 Other tactics. } *)

(** Syntactic equality up to universes. With [strict] the universe
   constraints must be already true to succeed, without [strict] they
   are added to the evar map. *)
val constr_eq : strict:bool -> constr -> constr -> unit Proofview.tactic

val unify           : ?state:TransparentState.t -> constr -> constr -> unit Proofview.tactic
val evarconv_unify : ?state:TransparentState.t -> ?with_ho:bool -> constr -> constr -> unit Proofview.tactic

val specialize_eqs : Id.t -> unit Proofview.tactic

val general_rewrite_clause :
  (bool -> evars_flag -> constr with_bindings -> clause -> unit Proofview.tactic) Hook.t

val subst_one :
  (bool -> Id.t -> Id.t * constr * bool -> unit Proofview.tactic) Hook.t

val declare_intro_decomp_eq :
  ((int -> unit Proofview.tactic) -> Rocqlib.rocq_eq_data * types *
   (types * constr * constr) ->
   constr * types -> unit Proofview.tactic) -> unit

(** Tactic analogous to the [Strategy] vernacular, but only applied
   locally to the tactic argument *)
val with_set_strategy :
  (Conv_oracle.level * Names.GlobRef.t list) list ->
  'a Proofview.tactic -> 'a Proofview.tactic

(** {6 Simple form of basic tactics. } *)

module Simple : sig
  (** Simplified version of some of the above tactics *)

  val intro           : Id.t -> unit Proofview.tactic
  val apply  : constr -> unit Proofview.tactic
  val eapply : constr -> unit Proofview.tactic
  val elim   : constr -> unit Proofview.tactic
  val case   : constr -> unit Proofview.tactic
  val apply_in : Id.t -> constr -> unit Proofview.tactic

end

(** {6 Tacticals defined directly in term of Proofview} *)

val refine : typecheck:bool -> (evar_map -> evar_map * constr) -> unit Proofview.tactic
(** [refine ~typecheck c] is [Refine.refine ~typecheck c]
    followed by beta-iota-reduction of the conclusion. *)

val reduce_after_refine : unit Proofview.tactic
(** The reducing tactic called after {!refine}. *)

(** {6 Internals, do not use} *)

module Internal :
sig

val explicit_intro_names : 'a intro_pattern_expr CAst.t list -> Id.Set.t

val check_name_unicity : env -> Id.t list -> Id.t list -> 'a intro_pattern_expr CAst.t list -> unit

val clear_gen : (env -> evar_map -> Id.t -> Evarutil.clear_dependency_error ->
  GlobRef.t option -> evar_map * named_context_val * types) ->
  Id.t list -> unit Proofview.tactic

val clear_wildcards : lident list -> unit Proofview.tactic

val dest_intro_patterns : evars_flag -> Id.Set.t -> lident list ->
  Id.t Logic.move_location -> intro_patterns ->
  (Id.t list -> lident list -> unit Proofview.tactic) -> unit Proofview.tactic

end
