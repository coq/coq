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

(** Main tactics defined in ML. *)

(** {6 General functions. } *)

val is_quantified_hypothesis : Id.t -> Proofview.Goal.t -> bool

(** {6 Conversion tactics. } *)

(** [vm_cast_no_check new_concl] changes the conclusion to [new_concl] by inserting a [VMcast].
    It does not check that the new conclusion is indeed convertible to the old conclusion. *)
val vm_cast_no_check : constr -> unit Proofview.tactic

(** Same as [vm_cast_no_check] but uses a [NATIVEcast]. *)
val native_cast_no_check : constr -> unit Proofview.tactic

(** [convert_concl ~cast ~check new_concl kind] changes the conclusion to [new_concl],
    which should be convertible to the old conclusion.
    - [cast]: if [true] insert a cast in the proof term using [kind] as the cast kind.
    - [check]: if [true] we check for convertibility. *)
val convert_concl : cast:bool -> check:bool -> types -> cast_kind -> unit Proofview.tactic

(** [convert_hyp ~check ~reorder decl] changes the declaration of [x] to [decl],
    where [x] is the variable bound by [decl].
    - [check]: if [true] we check that [x] is in the context, that the new and old declarations of [x]
      are convertible (both the types and bodies need to be convertible), and that the new
      declaration of [x] has a body if and only if the old declaration of [x] has a body. *)
val convert_hyp : check:bool -> reorder:bool -> named_declaration -> unit Proofview.tactic

(** [convert x y] checks that [x] and [y] are convertible (using all conversion rules),
    and fails otherwise. *)
val convert : constr -> constr -> unit Proofview.tactic

(** [convert_leq x y] checks that [x] is smaller than [y] for cumulativity (using all conversion rules),
    and fails otherwise. *)
val convert_leq : constr -> constr -> unit Proofview.tactic

(** {6 Basic introduction tactics. } *)

(** [introduction id] is a low-level tactic which introduces a single variable with name [id].
    - Fails if the goal is not a product or a let-in.
    - Fails if [id] is already declared in the context. *)
val introduction : Id.t -> unit Proofview.tactic

(** [fresh_id_in_env avoid id env] generates a fresh identifier built from [id].
    The returned identifier is guaranteed to be distinct from:
    - The identifiers in [avoid].
    - The global constants in [env].
    - The local variables in [env]. *)
val fresh_id_in_env : Id.Set.t -> Id.t -> env -> Id.t

(** [find_intro_names env sigma ctx] returns the names that would be created by [intros],
    without actually doing [intros].  *)
val find_intro_names : env -> Evd.evar_map -> rel_context -> Id.t list

(** [intro] introduces a single variable with an automatically-generated name.
    Fails if the goal is not a product or a let-in. *)
val intro : unit Proofview.tactic

(** [introf] is a more aggressive version of [intro]:
    - If the goal is an evar it will instantiate it with a product.
    - It will attempt to head normalize the goal until it is a product, a let-in, or an evar. *)
val introf : unit Proofview.tactic

(** [intro_move id_opt loc] introduces a single variable and moves it to location [loc].
    - If [id_opt] is [Some id] the introduced variable is named [id].
    - If [id_opt] is [None] we use an automatically generated name.
    - It will instantiate evars and head-normalize the goal in the same way as [introf]. *)
val intro_move : Id.t option -> Id.t Logic.move_location -> unit Proofview.tactic

(** [intro_move_avoid id_opt avoid loc] is the same as [intro_move] except that
    the automatically generated name is guaranteed to not be in the set [avoid]. *)
val intro_move_avoid : Id.t option -> Id.Set.t -> Id.t Logic.move_location -> unit Proofview.tactic

(** Generalization of [intro_move] to a list of variables and locations (processed from left to right). *)
val intros_move : (Id.t * Id.t Logic.move_location) list -> unit Proofview.tactic

(** [intro_avoiding avoid] introduces a single variable with an automatically-generated name
    which is guaranteed to not be the set [avoid]. *)
val intro_avoiding : Id.Set.t -> unit Proofview.tactic

(** [intro_replacing id] introduces a single variable named [id], replacing the previous declaration of [id].

    Fails if [id] is not already in the context. *)
val intro_replacing : Id.t -> unit Proofview.tactic

(** [intro_using_then id tac] introduces a single variable named [id]. It refreshes the name [id] if needed,
    and applies [tac] to the resulting identifier. *)
val intro_using_then : Id.t -> (Id.t -> unit Proofview.tactic) -> unit Proofview.tactic

(** [intro_mustbe_force id] is the same as [introf] but the name [id] is used instead of
    an automatically-generated name. *)
val intro_mustbe_force : Id.t -> unit Proofview.tactic

(** Generalization of [intro_mustbe_force] to a list of variables (processed from left to right). *)
val intros_mustbe_force : Id.t list -> unit Proofview.tactic

(** [intro_then tac] introduces a single variable with an automatically-generated name,
    and applies [tac] to the resulting identifier. *)
val intro_then : (Id.t -> unit Proofview.tactic) -> unit Proofview.tactic

(** Generalization of [intro_using_then] to a list of variables (processed from left to right). *)
val intros_using_then : Id.t list -> (Id.t list -> unit Proofview.tactic) -> unit Proofview.tactic

(** Generalization of [intro_replacing] to a list of variables (processed from left to right). *)
val intros_replacing : Id.t list -> unit Proofview.tactic

(** Variant of [intros_replacing] which does not assume that the variables are
    already declared in the context. *)
val intros_possibly_replacing : Id.t list -> unit Proofview.tactic

(** [auto_intros_tac names] introduces the variables in [names].
    - The variables are introduced from right to left (contrary to the conventional order).
    - Names are chosen as follow: [Anonymous] indicates to generate a fresh name
      and [Name id] indicates to use the name [id].
    - It will instantiate evars and head-normalize the goal in the same way as [introf]. *)
val auto_intros_tac : Names.Name.t list -> unit Proofview.tactic

(** [intros] keeps introducing variables while the goal is a product or a let-in. *)
val intros : unit Proofview.tactic

(** [intros_until hyp] is a variant of [intros] which stops when hypothesis [hyp] is introduced. *)
val intros_until : quantified_hypothesis -> unit Proofview.tactic

(** [intros_clearing bs] introduces as many variables as booleans in [bs]. Each boolean indicates
    whether to clear the introduced variable (if [true]) or to keep it (if [false]). *)
val intros_clearing : bool list -> unit Proofview.tactic

(** Assuming a tactic [tac] depending on a hypothesis,
    [try_intros_until tac arg] first assumes that [arg] denotes a
    quantified hypothesis (denoted by name or by index) and tries to
    introduce it in context before applying [tac], otherwise assumes the
    hypothesis is already in context and directly applies [tac]. *)
val try_intros_until :
  (Id.t -> unit Proofview.tactic) -> quantified_hypothesis -> unit Proofview.tactic

type evars_flag = bool     (* true = pose evars       false = fail on evars *)
type rec_flag = bool       (* true = recursive        false = not recursive *)
type advanced_flag = bool  (* true = advanced         false = basic *)
type clear_flag = bool option (* true = clear hyp, false = keep hyp, None = use default *)

(** Apply a tactic on a quantified hypothesis, an hypothesis in context
    or a term with bindings. *)

type 'a core_destruction_arg =
  | ElimOnConstr of 'a
  | ElimOnIdent of lident
  | ElimOnAnonHyp of int

type equality_position_on_elim =
  | UnknownPosition
  | AtPosition of int

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

(** {6 Pattern introduction tactics. } *)

(** [intro_patterns with_evars patt] introduces variables and processes them according
    to the introduction patterns [patt]. *)
val intro_patterns : evars_flag -> intro_patterns -> unit Proofview.tactic

(** Variant of [intro_patterns] which moves introduced variables to location [loc]. *)
val intro_patterns_to : evars_flag -> Id.t Logic.move_location -> intro_patterns ->
  unit Proofview.tactic

(** Variant of [intro_patterns_to] which introduces a single variable. *)
val intro_pattern_to : evars_flag -> Id.t Logic.move_location -> delayed_open_constr intro_pattern_expr ->
    unit Proofview.tactic

val intro_patterns_bound_to : evars_flag -> int -> Id.t Logic.move_location -> intro_patterns ->
  unit Proofview.tactic

(** [intros_patterns with_evars patt] implements the user-level "intros" tactic:
    - If [patt] is empty it will introduces as many variables as possible (using [intros]).
    - Otherwise it will behave as [intro_patterns with_evars patt]. *)
val intros_patterns : evars_flag -> intro_patterns -> unit Proofview.tactic

(** {6 Exact tactics. } *)

(** [assumption] solves the goal if it is convertible to the type of a hypothesis.
    Fails if there is no such hypothesis. *)
val assumption : unit Proofview.tactic

(** [exact_no_check x] solves the goal with term [x].
    It does not check that the type of [x] is convertible to the conclusion. *)
val exact_no_check : constr -> unit Proofview.tactic

(** [exact_check x] solves the goal with term [x].
    Fails if the type of [x] does not match the conclusion. *)
val exact_check : constr -> unit Proofview.tactic

(** [exact_proof x] internalizes the constr_expr [x] using the conclusion,
    and solves the goal using the internalized term.
    Fails if [x] could not be internalized. *)
val exact_proof : Constrexpr.constr_expr -> unit Proofview.tactic

(** {6 Reduction tactics. } *)

type tactic_reduction = Reductionops.reduction_function
type e_tactic_reduction = Reductionops.e_reduction_function

type change_arg = patvar_map -> env -> evar_map -> (evar_map * constr) Tacred.change

val make_change_arg : constr -> change_arg

(** [reduct_in_hyp ~check ~reorder red_fun hyp] applies the reduction function [red_fun] in hypothesis [hyp].
    - [check]: if [true] we check that the new hypothesis is convertible to the old hypothesis. *)
val reduct_in_hyp : check:bool -> reorder:bool -> tactic_reduction -> hyp_location -> unit Proofview.tactic

(** [reduct_in_concl ~cast ~check (red_fun, kind)] applies the reduction function [red_fun] to the conclusion.
    - [cast]: if [true] we insert a cast  in the proof term using [kind] as the cast kind.
    - [check]: if [true] we check that the new conclusion is convertible to the old conclusion. *)
val reduct_in_concl : cast:bool -> check:bool -> tactic_reduction * cast_kind -> unit Proofview.tactic

(** [reduct_option] combines the behaviour of [reduct_in_hyp] and [reduct_in_concl].
    If reducing in the conclusion it will insert a cast. *)
val reduct_option : check:bool -> tactic_reduction * cast_kind -> goal_location -> unit Proofview.tactic

(** Same as [reduct_in_concl] but the reduction function can update the evar map. *)
val e_reduct_in_concl : cast:bool -> check:bool -> e_tactic_reduction * cast_kind -> unit Proofview.tactic

(** [change_in_concl ~check where change_fun] changes the conclusion (or subterms of the conclusion) using
    the change function [change_fun].
    - [check]: if [true] we check that the new conclusion is convertible to the old conclusion.
    - [where]: if [None] then the whole conclusion is changed.
      If [Some (occs, patt)] then only the subterms of the conclusion which match occurences [occs]
      and pattern [patt] are changed. *)
val change_in_concl : check:bool -> (occurrences * constr_pattern) option -> change_arg -> unit Proofview.tactic

(** [change_concl new_concl] replaces the conclusion with [new_concl].
    Fails if the new conclusion and old conclusion are not convertible. *)
val change_concl : constr -> unit Proofview.tactic

(** [change_in_hyp ~check where change_fun hyp] is analogous to [change_in_concl] but works
    on the hypothesis [hyp] instead of the conclusion. *)
val change_in_hyp : check:bool -> (occurrences * constr_pattern) option -> change_arg ->
                        hyp_location -> unit Proofview.tactic

(** [change ~check where change_fun clause] applies the change function [change_fun].
    - [check]: if [true] we check that the changed terms are convertible to the old terms.
    - [clause]: specifies where to apply the change function: to the conclusion and/or to a (subset of) hypotheses.
    - [where]: if [None] we change the complete conclusion/hypothesis.
      If [Some patt] we change subterms matching pattern [patt]. *)
val change :
  check:bool -> constr_pattern option -> change_arg -> clause -> unit Proofview.tactic

(** [red_in_concl] reduces the conclusion using the [red] reduction strategy. *)
val red_in_concl : unit Proofview.tactic

(** [red_in_hyp hyp] reduces hypothesis [hyp] using the [red] reduction strategy. *)
val red_in_hyp : hyp_location -> unit Proofview.tactic

(** [red_option loc] reduces the hypothesis or conclusion [loc] using the [red] reduction strategy. *)
val red_option : goal_location -> unit Proofview.tactic

(** [hnf_in_concl] reduces the conclusion to head normal form. *)
val hnf_in_concl : unit Proofview.tactic

(** [hnf_in_hyp hyp] reduces hypothesis [hyp] to head normal form. *)
val hnf_in_hyp : hyp_location -> unit Proofview.tactic

(** [hnf_option loc] reduces the hypothesis or conclusion [loc] to head normal form. *)
val hnf_option : goal_location -> unit Proofview.tactic

(** [simpl_in_concl] reduces the conclusion using the [simpl] reduction strategy. *)
val simpl_in_concl : unit Proofview.tactic

(** [simpl_in_hyp hyp] reduces hypothesis [hyp] using the [red] reduction strategy. *)
val simpl_in_hyp : hyp_location -> unit Proofview.tactic

(** [simpl_option loc] reduces the hypothesis or conclusion [loc] using the [simpl] reduction strategy. *)
val simpl_option : goal_location -> unit Proofview.tactic

(** [normalise_in_concl] reduces the conclusion to normal form. *)
val normalise_in_concl : unit Proofview.tactic

(** [normalise_in_hyp hyp] reduces hypothesis [hyp] to normal form. *)
val normalise_in_hyp : hyp_location -> unit Proofview.tactic

(** [normalise_option loc] reduces the hypothesis or conclusion [loc] to normal form. *)
val normalise_option : goal_location -> unit Proofview.tactic

(** [normalise_in_concl] reduces the conclusion to normal form using VM compute. *)
val normalise_vm_in_concl : unit Proofview.tactic

(** [unfold_in_concl cs] unfolds a list of constants [cs] in the conclusion.
    One can specify which occurences of each constant to unfold. *)
val unfold_in_concl :
  (occurrences * Evaluable.t) list -> unit Proofview.tactic

(** [unfold_in_hyp cs hyp] unfolds a list of constants [cs] in hypothesis [hyp].
    One can specify which occurences of each constant to unfold. *)
val unfold_in_hyp :
  (occurrences * Evaluable.t) list -> hyp_location -> unit Proofview.tactic

(** [unfold_option cs loc] unfolds a list of constants [cs] in the hypothesis or conclusion [loc].
    One can specify which occurences of each constant to unfold. *)
val unfold_option :
  (occurrences * Evaluable.t) list -> goal_location -> unit Proofview.tactic

(** [pattern_option [(occs1, t1); (occs2, t2); ...] loc] implements the [pattern] user tactic.
    It performs beta-expansion for the terms [ti] at occurences [occsi], in the goal location
    [loc] (i.e. either in the goal or in a hypothesis). *)
val pattern_option :
  (occurrences * constr) list -> goal_location -> unit Proofview.tactic

val reduce : red_expr -> clause -> unit Proofview.tactic

(** [unfold_constr x] unfolds all occurences of [x] in the conclusion. *)
val unfold_constr : GlobRef.t -> unit Proofview.tactic

(** {6 Modification of the local context. } *)

(** [clear ids] removes hypotheses [ids] from the context. *)
val clear : Id.t list -> unit Proofview.tactic

(** [clear_body ids] removes the definitions (but not the declarations) of hypotheses [ids]
    from the context. *)
val clear_body : Id.t list -> unit Proofview.tactic

(** [unfold_body id] unfolds the definition of the local variable [id] in the conclusion
    and in all hypotheses. Fails if [id] does not have a body. *)
val unfold_body : Id.t -> unit Proofview.tactic

(** [keep ids] clears every hypothesis except:
    - The hypotheses in [ids].
    - The hypotheses which occur in the conclusion.
    - The hypotheses which occur in the type or body of a kept hypothesis. *)
val keep : Id.t list -> unit Proofview.tactic

val specialize : constr with_bindings -> intro_pattern option -> unit Proofview.tactic

(** [move_hyp id loc] moves hypothesis [id] to location [loc]. *)
val move_hyp : Id.t -> Id.t Logic.move_location -> unit Proofview.tactic

(** [rename_hyp [(x1, y1); (x2; y2); ...]] renames hypotheses [xi] into [yi].
    - The names [x1, x2, ...] are expected to be distinct.
    - The names [y1, y2, ...] are expected to be distinct. *)
val rename_hyp : (Id.t * Id.t) list -> unit Proofview.tactic

(** {6 Apply tactics. } *)

(** [use_clear_hyp_by_default ()] returns the default clear flag used by [apply] and related tactics.
    - [true] means that hypotheses are cleared after being applied.
    - [false] means that hypotheses are kept after being applied. *)
val use_clear_hyp_by_default : unit -> bool

(** [apply_clear_request c1 c2 id] implements the clear behaviour of [apply] and friends.
    - [c1] is the primary clear flag. If [None] we use the secondary clear flag.
    - [c2] is the secondary clear flag, usually [use_clear_hyp_by_default ()].
    - [id] is the identifier of the hypothesis to clear. If [None] we do nothing. *)
val apply_clear_request : clear_flag -> bool -> Id.t option -> unit Proofview.tactic

(** [apply t] applies the lemma [t] to the conclusion. *)
val apply : constr -> unit Proofview.tactic

(** Variant of [apply] which allows creating new evars. *)
val eapply : ?with_classes:bool -> constr -> unit Proofview.tactic

(** Variant of [apply] which takes a term with bindings (e.g. [apply foo with (x := 42)]). *)
val apply_with_bindings : constr with_bindings -> unit Proofview.tactic

(** Variant of [eapply] which takes a term with bindings (e.g. [eapply foo with (x := 42)]).
    - [with_classes] specifies whether to attempt to solve remaining evars using typeclass resolution. *)
val eapply_with_bindings : ?with_classes:bool -> constr with_bindings -> unit Proofview.tactic

(** [apply_with_bindings_gen ?with_classes advanced with_evars [(c1, t1); (c2, t2); ...]] is the most
    general version of [apply]. It applies lemmas [t1], [t2], ... in order.
    - [with_evars]: if [true] allow the creation of (non-goal) evars (i.e. setting [with_evars] to [true]
      gives the behaviour of [eapply]).
    - [with_classes]: if [true] attempt to solve remaining evars using typeclass resolution.
    - [advanced]: if [true] use delta reduction (constant unfolding) in unification,
      and descend under conjunctions in the conclusion.
    - [ci]: if [ti] is a hypothesis, [ci] tells whether to clear [ti] after applying it.
      If [ci] is [None] we use the default clear flag. *)
val apply_with_bindings_gen :
  ?with_classes:bool -> advanced_flag -> evars_flag -> (clear_flag * constr with_bindings CAst.t) list -> unit Proofview.tactic

(** Variant of [apply_with_bindings_gen] in which the terms are produced by tactics.  *)
val apply_with_delayed_bindings_gen :
  advanced_flag -> evars_flag -> (clear_flag * constr with_bindings Proofview.tactic CAst.t) list -> unit Proofview.tactic

(** Variant of [apply_with_bindings_gen] which works on a hypothesis instead of the goal. *)
val apply_in :
  advanced_flag -> evars_flag -> Id.t ->
    (clear_flag * constr with_bindings CAst.t) list ->
    intro_pattern option -> unit Proofview.tactic

(** Variant of [apply_in] in which the terms are produced by tactics.*)
val apply_delayed_in :
  advanced_flag -> evars_flag -> Id.t ->
    (clear_flag * constr with_bindings Proofview.tactic CAst.t) list ->
    intro_pattern option -> unit Proofview.tactic -> unit Proofview.tactic

val apply_type : typecheck:bool -> constr -> constr list -> unit Proofview.tactic

(** [cut_and_apply t] (where [t] has type [A -> B]) transforms a goal [ |- C ] into two goals
    [ |- B -> C ] and [ |- A ]. *)
val cut_and_apply : constr -> unit Proofview.tactic

(** {6 Elimination tactics. } *)

(** [simplest_elim t] eliminates [t] using the default eliminator associated to [t].
    It does not allow unresolved evars, and uses the default clear flag. *)
val simplest_elim : constr -> unit Proofview.tactic

(** [elim with_evars clear t eliminator] eliminates [t].
    - [with_evars]: if [true] we allow unresolved evars (this is the behaviour of [eelim]).
    - [clear]: if [Some _], [clear] tells whether to remove [t] from the context.
      If [None] we use the default clear flag.
    - [eliminator]: if [Some _] we use this as the eliminator for [t].
      If [None] we use the default eliminator associated to [t]. *)
val elim :
  evars_flag -> clear_flag -> constr with_bindings -> constr with_bindings option -> unit Proofview.tactic

(** Variant of [elim] which uses the default eliminator. *)
val default_elim : evars_flag -> clear_flag -> constr with_bindings ->
  unit Proofview.tactic

val general_elim_clause : evars_flag -> unify_flags -> Id.t option ->
    ((metavariable list * Unification.Meta.t) * EConstr.t * EConstr.types) -> EConstr.t -> equality_position_on_elim -> unit Proofview.tactic

(** [general_case_analysis with_evars clear (t, bindings)] performs case analysis on [t].
    If [t] is a variable which is not in the context, we attempt to perform introductions
    until [t] is in the context.
    - [with_evars]: if [true] allow unsolved evars (this is the behaviour of [ecase]).
    - [clear]: if [Some _], [clear] tells whether to remove [t] from the context.
      If [None] we use the default clear flag. *)
val general_case_analysis : evars_flag -> clear_flag -> constr with_bindings -> unit Proofview.tactic

(** [simplest_case t] performs case analysis on [t]. It does not allow unresolved evars,
    and uses the default clear flag. *)
val simplest_case : constr -> unit Proofview.tactic

(** [exfalso] changes the conclusion to [False]. *)
val exfalso : unit Proofview.tactic

(** {6 Constructor tactics. } *)

(** [constructor_tac with_evars expected_num_ctors i bindings] checks that the goal is
    an inductive [ind] and applies the [i]-th constructor of [ind].
    - [with_evars]: if [true] applying the constructor can leave evars (this gives the
      behaviour of [econstructor]).
    - [expected_num_ctors]: if [Some nctors] we check that the number of constructors of [ind]
      is equal to [nctors].
    - [i]: index of the constructor to apply, starting at [1].
    - [bindings]: bindings to use when applying the constructor. *)
val constructor_tac : evars_flag -> int option -> int ->
  constr bindings -> unit Proofview.tactic

(** [one_constructor i bindings] is a specialization of [constructor_tac] with:
    - [with_evars] set to [false].
    - [expected_num_ctors] set to [None]. *)
val one_constructor : int -> constr bindings -> unit Proofview.tactic

(** [any_constructor with_evars tac] checks that the goal is an inductive [ind] and
    tries to apply the constructors of [ind] one by one (from first to last).
    - [with_evars]: if [true] applying the constructor can leave evars (this gives the
      behaviour of [econstructor]).
    - [tac]: we run [tac] after applying each constructor, and backtrack
      to the next constructor if [tac] fails. *)
val any_constructor : evars_flag -> unit Proofview.tactic option -> unit Proofview.tactic

(** [simplest_left] checks the goal is an inductive with two constructors
    and applies the first constructor. *)
val simplest_left : unit Proofview.tactic

(** Variant of [simplest_left] which takes bindings. *)
val left  : constr bindings -> unit Proofview.tactic

(** Variant of [simplest_left] which takes an evar flag and bindings. *)
val left_with_bindings : evars_flag -> constr bindings -> unit Proofview.tactic

(** [simplest_right] checks the goal is an inductive with two constructors
    and applies the second constructor. *)
val simplest_right : unit Proofview.tactic

(** Variant of [simplest_right] which takes bindings. *)
val right : constr bindings -> unit Proofview.tactic

(** Variant of [simplest_right] which takes an evar flag and bindings. *)
val right_with_bindings : evars_flag -> constr bindings -> unit Proofview.tactic

(** [simplest_left] checks the goal is an inductive with one constructor
    and applies the (unique) constructor. *)
val simplest_split : unit Proofview.tactic

(** Variant of [simplest_split] which takes bindings. *)
val split : constr bindings -> unit Proofview.tactic

(** Variant of [simplest_split] which takes an evar flag and bindings. *)
val split_with_bindings : evars_flag -> constr bindings list -> unit Proofview.tactic

(** Variant of [simplest_split] which takes an evar flag and delayed bindings. *)
val split_with_delayed_bindings : evars_flag -> constr bindings delayed_open list -> unit Proofview.tactic

(** {6 Equality tactics. } *)

(** Hook to the [setoid_reflexivity] tactic, set at runtime. *)
val setoid_reflexivity : unit Proofview.tactic Hook.t

(** [reflexivity_red reduce] solves a goal of the form [x = y].
    - [reduce]: if [true] we weak-head normalize the goal before checking it is
      indeed an equality. *)
val reflexivity_red : bool -> unit Proofview.tactic

(** Variant of [reflexivity_red] which does not perform reduction,
    and falls back to [setoid_reflexivity] in case of failure. *)
val reflexivity : unit Proofview.tactic

(** [intros_reflexivity] performs [intros] followed by [reflexivity]. *)
val intros_reflexivity : unit Proofview.tactic

(** Hook to the [setoid_symmetry] tactic, set at runtime. *)
val setoid_symmetry : unit Proofview.tactic Hook.t

(** [symmetry_red reduce] checks the goal is of the form [x = y] and changes it to [y = x].
    - [reduce]: if [true] we weak-head normalize the goal before checking it is
      indeed an equality. *)
val symmetry_red : bool -> unit Proofview.tactic

(** Variant of [symmetry_red] which does not perform reduction,
    and falls back to [setoid_symmetry] in case of failure. *)
val symmetry : unit Proofview.tactic

(** Hook to the [setoid_symmetry_in] tactic, set at runtime. *)
val setoid_symmetry_in : (Id.t -> unit Proofview.tactic) Hook.t

(** [intros_symmetry clause] performs [intros] followed by [symmetry] on all
    the locations indicated by [clause] (i.e. the conclusion and/or a (subset of) hypotheses).
    Actual occurences contained in [clause] are not used: only the hypotheses names are relevant. *)
val intros_symmetry : clause -> unit Proofview.tactic

type transitivity_arg = Closed of constr | Open of constr option

(** Hook to the [setoid_transitivity] tactic, set at runtime. *)
val setoid_transitivity : (transitivity_arg -> unit Proofview.tactic) Hook.t

(** [transitivity_red reduce t] checks the goal is of the form [x = y] and changes it to [x = t] and [t = y].
    - [reduce]: if [true] we weak-head normalize the goal before checking it is
      indeed an equality.
    - [t]: if [Closed] then we use [apply eq_trans with t] to perform transitivity.
      If [Open o] we use [eapply eq_trans with t] (if o is Some t, otherwise without binding) instead. *)
val transitivity_red : bool -> transitivity_arg -> unit Proofview.tactic

(** Variant of [transitivity_red] which does not perform reduction,
    uses [apply eq_trans with t],
    and falls back to [setoid_transitivity] in case of failure. *)
val transitivity : constr -> unit Proofview.tactic

(** Variant of [transitivity_red] which does not perform reduction,
    uses [eapply eq_trans],
    and falls back to [setoid_transitivity] in case of failure. *)
val etransitivity : constr option -> unit Proofview.tactic

(** [intros_transitivity t] performs [intros] followed by [transitivity t] or [etransivity t]
    (depending on whether [t] is [Closed] or [Open]). *)
val intros_transitivity : transitivity_arg -> unit Proofview.tactic

(** {6 Forward reasoning tactics. } *)

(** [assert_before x T] first asks to prove [T], then to prove the original goal augmented
    with a new hypothesis of type [x : T].
    - [x]: if [None] the name of the hypothesis is generated automatically.
      If [Some] then it is the name of the hypothesis (which should not be already defined in the context). *)
val assert_before : Name.t -> types -> unit Proofview.tactic

(** Variant of [assert_before] which allows replacing hypotheses. *)
val assert_before_replacing: Id.t -> types -> unit Proofview.tactic

(** [assert_after x T] first asks the original goal augmented with a new hypothesis of type [x : T],
    then to prove [T].
    - [x]: if [None] the name of the hypothesis is generated automatically.
      If [Some] then it is the name of the hypothesis (which should not be already defined in the context). *)
val assert_after : Name.t -> types -> unit Proofview.tactic

(** Variant of [assert_after] which allows replacing hypotheses. *)
val assert_after_replacing : Id.t -> types -> unit Proofview.tactic

(** [forward before by_tac ipat t] performs a forward reasoning step.
    - If [by_tac] is [None] it adds a new hypothesis with _body_ equal to [t].
    - If [by_tac] is [Some tac] it asks to prove [t] and to prove the original goal
      augmented with a new hypothesis of type [t]. If [tac] is [Some _] then [tac] is used
      to prove [t] (and [tac] is required to succeed).
    - [before]: if [true] then [t] must be proved first.
      If [false] then [t] must be proved [last]. *)
val forward : bool -> unit Proofview.tactic option option ->
    intro_pattern option -> constr -> unit Proofview.tactic

(** [assert_by x T tac] adds a new hypothesis [x : T]. The tactic [tac] is used
    to prove [T]. If [x] is [None] a fresh name is automatically generated. *)
val assert_by : Name.t -> types -> unit Proofview.tactic ->
  unit Proofview.tactic

(** [enough_by x T tac] changes the goal to [T]. The tactic [tac] is used to
    prove the orignal goal augmented with a hypothesis [x : T]. If [x] is [None] a fresh name
    is automatically generated. *)
val enough_by : Name.t -> types -> unit Proofview.tactic ->
  unit Proofview.tactic

(** [pose_proof x t] adds a new hypothesis [x := t]. If [x] is [None] a fresh name
    is automatically generated. *)
val pose_proof : Name.t -> constr -> unit Proofview.tactic

(** Implements the tactic [cut], actually a modus ponens rule. *)
val cut : types -> unit Proofview.tactic

(** [pose_tac x t] adds a new hypothesis [x := t]. If [x] is [None] a fresh name
    is automatically generated. Fails if there is alreay a hypothesis named [x]. *)
val pose_tac : Name.t -> constr -> unit Proofview.tactic

val letin_tac : (bool * intro_pattern_naming) option ->
  Name.t -> constr -> types option -> clause -> unit Proofview.tactic

(** Common entry point for user-level "set", "pose", and "remember". *)
val letin_pat_tac : evars_flag -> (bool * intro_pattern_naming) option ->
  Name.t -> (evar_map option * constr) -> clause -> unit Proofview.tactic

(** {6 Other tactics. } *)

(** [constr_eq ~strict x y] checks that [x] and [y] are syntactically equal (i.e. alpha-equivalent),
    up to universes.
    - [strict]: if [true] the universe constraints must be already true.
      If [false] any necessary universe constraints are added to the evar map. *)
val constr_eq : strict:bool -> constr -> constr -> unit Proofview.tactic

(** Legacy unification. Use [evarconv_unify] instead. *)
val unify : ?state:TransparentState.t -> constr -> constr -> unit Proofview.tactic

(** [evarconv_unify ?state ?with_ho x y] unifies [x] and [y], instantiating evars and adding universe constraints
    as needed. Fails if [x] and [y] are not unifiable.
    - [state]: transparency state to use (defaults to [TransparentState.full]).
    - [with_ho]: whether to use higher order unification (defaults to [true]). *)
val evarconv_unify : ?state:TransparentState.t -> ?with_ho:bool -> constr -> constr -> unit Proofview.tactic

val specialize_eqs : Id.t -> unit Proofview.tactic

val general_rewrite_clause :
  (bool -> evars_flag -> constr with_bindings -> clause -> unit Proofview.tactic) Hook.t

val subst_one :
  (bool -> Id.t -> Id.t * constr * bool -> unit Proofview.tactic) Hook.t

val declare_intro_decomp_eq :
  ((int -> unit Proofview.tactic) -> EConstr.constr * GlobRef.t * types *
   (types * constr * constr) ->
   constr * types -> unit Proofview.tactic) -> unit

(** Tactic analogous to the [Strategy] vernacular, but only applied
    locally to the tactic argument. *)
val with_set_strategy :
  (Conv_oracle.level * Names.GlobRef.t list) list -> 'a Proofview.tactic -> 'a Proofview.tactic

(** {6 Simple form of common tactics. } *)

module Simple : sig
  (** Simplified version of some of the above tactics *)

  val intro : Id.t -> unit Proofview.tactic
  val apply : constr -> unit Proofview.tactic
  val eapply : constr -> unit Proofview.tactic
  val elim : constr -> unit Proofview.tactic
  val case : constr -> unit Proofview.tactic
  val apply_in : Id.t -> constr -> unit Proofview.tactic

end

(** {6 Tacticals defined directly in term of Proofview} *)

(** [refine ~typecheck c] is [Refine.refine ~typecheck c]
    followed by beta-iota-reduction of the conclusion. *)
val refine : typecheck:bool -> (evar_map -> evar_map * constr) -> unit Proofview.tactic

(** The reducing tactic called after [refine]. *)
val reduce_after_refine : unit Proofview.tactic

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

(** {6 Moved functions} *)

(** The functions below have been moved to other files but are kept here
    for backwards compatibility. Don't use in new code. *)

(** Deprecated since 9.2, use [TacticErrors.not_convertible ()] instead. *)
exception NotConvertible of (Environ.env * Evd.evar_map * EConstr.constr * EConstr.constr) option

val fix : Id.t -> int -> unit Proofview.tactic
[@@ocaml.deprecated "(since 9.2) Use [FixTactics.fix]"]

val mutual_fix :
  Id.t -> int -> (Id.t * int * constr) list -> unit Proofview.tactic
[@@ocaml.deprecated "(since 9.2) Use [FixTactics.mutual_fix]"]

val cofix : Id.t -> unit Proofview.tactic
[@@ocaml.deprecated "(since 9.2) Use [FixTactics.cofix]"]

val mutual_cofix : Id.t -> (Id.t * constr) list -> unit Proofview.tactic
[@@ocaml.deprecated "(since 9.2) Use [FixTactics.mutual_cofix]"]
