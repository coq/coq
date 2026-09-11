(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.

(** ML-facing types *)

Ltac2 Type hypothesis := [ AnonHyp (int) | NamedHyp (ident) ].

Ltac2 Type bindings := [
| NoBindings
| ImplicitBindings (constr list)
| ExplicitBindings ((hypothesis * constr) list)
].

Ltac2 Type constr_with_bindings := constr * bindings.

Ltac2 Type occurrences := [
| AllOccurrences
| AllOccurrencesBut (int list)
| NoOccurrences
| OnlyOccurrences (int list)
].

Ltac2 Type hyp_location_flag := [ InHyp | InHypTypeOnly | InHypValueOnly ].

Ltac2 Type clause := {
  on_hyps : (ident * occurrences * hyp_location_flag) list option;
  on_concl : occurrences;
}.

Ltac2 Type reference := [
| VarRef (ident)
| ConstRef (constant)
| IndRef (inductive)
| ConstructRef (constructor)
].

Ltac2 Type strength := [ Norm | Head ].

Ltac2 Type red_flags := {
  rStrength : strength;
  rBeta : bool;
  rMatch : bool;
  rFix : bool;
  rCofix : bool;
  rZeta : bool;
  rDelta : bool; (** true = delta all but rConst; false = delta only on rConst*)
  rConst : reference list
}.

Ltac2 Type 'a not_implemented.

Ltac2 Type rec intro_pattern := [
| IntroForthcoming (bool)
| IntroNaming (intro_pattern_naming)
| IntroAction (intro_pattern_action)
]
with intro_pattern_naming := [
| IntroIdentifier (ident)
| IntroFresh (ident)
| IntroAnonymous
]
with intro_pattern_action := [
| IntroWildcard
| IntroOrAndPattern (or_and_intro_pattern)
| IntroInjection (intro_pattern list)
| IntroApplyOn ((unit -> constr), intro_pattern)
| IntroRewrite (bool)
]
with or_and_intro_pattern := [
| IntroOrPattern (intro_pattern list list)
| IntroAndPattern (intro_pattern list)
].

Ltac2 Type destruction_arg := [
| ElimOnConstr (unit -> constr_with_bindings)
| ElimOnIdent (ident)
| ElimOnAnonHyp (int)
].

Ltac2 Type induction_clause := {
  indcl_arg : destruction_arg;
  indcl_eqn : intro_pattern_naming option;
  indcl_as : or_and_intro_pattern option;
  indcl_in : clause option;
}.

Ltac2 Type assertion := [
| AssertType (intro_pattern option, constr, (unit -> unit) option)
| AssertValue (ident, constr)
].

Ltac2 Type repeat := [
| Precisely (int)
| UpTo (int)
| RepeatStar
| RepeatPlus
].

Ltac2 Type orientation := [ LTR | RTL ].

Ltac2 Type rewriting := {
  rew_orient : orientation option;
  rew_repeat : repeat;
  rew_equatn : (unit -> constr_with_bindings);
}.

Ltac2 Type evar_flag := bool.
Ltac2 Type advanced_flag := bool.

Ltac2 Type move_location := [
| MoveAfter (ident)
| MoveBefore (ident)
| MoveFirst
| MoveLast
].

Ltac2 Type inversion_kind := [
| SimpleInversion
| FullInversion
| FullInversionClear
].

(** Standard, built-in tactics. See Ltac1 for documentation. *)

Ltac2 @ external intros : evar_flag -> intro_pattern list -> unit := "rocq-runtime.plugins.ltac2" "tac_intros".

Ltac2 @ external apply : advanced_flag -> evar_flag ->
  (unit -> constr_with_bindings) list -> (ident * (intro_pattern option)) option -> unit := "rocq-runtime.plugins.ltac2" "tac_apply".

Ltac2 @ external elim : evar_flag -> constr_with_bindings -> constr_with_bindings option -> unit := "rocq-runtime.plugins.ltac2" "tac_elim".
Ltac2 @ external case : evar_flag -> constr_with_bindings -> unit := "rocq-runtime.plugins.ltac2" "tac_case".

Ltac2 @ external generalize : (constr * occurrences * ident option) list -> unit := "rocq-runtime.plugins.ltac2" "tac_generalize".

Ltac2 @ external assert : assertion -> unit := "rocq-runtime.plugins.ltac2" "tac_assert".
Ltac2 @ external enough : constr -> (unit -> unit) option option -> intro_pattern option -> unit := "rocq-runtime.plugins.ltac2" "tac_enough".

Ltac2 @ external pose : ident option -> constr -> unit := "rocq-runtime.plugins.ltac2" "tac_pose".
Ltac2 @ external set : evar_flag -> (unit -> ident option * constr) -> clause -> unit := "rocq-runtime.plugins.ltac2" "tac_set".

Ltac2 @ external remember : evar_flag -> ident option -> (unit -> constr) -> intro_pattern option -> clause -> unit := "rocq-runtime.plugins.ltac2" "tac_remember".

Ltac2 @ external destruct : evar_flag -> induction_clause list ->
  constr_with_bindings option -> unit := "rocq-runtime.plugins.ltac2" "tac_destruct".

Ltac2 @ external induction : evar_flag -> induction_clause list ->
  constr_with_bindings option -> unit := "rocq-runtime.plugins.ltac2" "tac_induction".

Ltac2 @external exfalso : unit -> unit := "rocq-runtime.plugins.ltac2" "tac_exfalso".


(** Constructors for reduction/expansion strategies *)

Module Red.
  Ltac2 Type t.

  (** βιζ-reduction of the _head constant_ of a term. Fails if there is no
  reducible head constant. *)
  Ltac2 @external red : t := "rocq-runtime.plugins.ltac2" "red".

  (** Full βδιζ-reduction the head of a term. Does not recurse into subterms. *)
  Ltac2 @external hnf : t := "rocq-runtime.plugins.ltac2" "hnf".

  (** Strong normalization except two key differences:

  - It unfolds constants only if they lead to an ι-reduction, i.e. reducing a
    match or unfolding a fixpoint.

  - When reducing a constant unfolding to (co)fixpoints, uses the name of the
    constant the (co)fixpoint comes from instead of the (co)fixpoint definition
    in recursive calls.

  Can unfold transparent constants as well as those designated by [Arguments]
  commands. The second parameter can limit the application of [simpl] to
  specific subterms matching. If the pattern resolves into a global reference,
  it will be treated as such.

  Only the following [red_flags] are relevant: [head], [delta]. *)
  Ltac2 @external simpl : red_flags -> (pattern * occurrences) option -> t := "rocq-runtime.plugins.ltac2" "simpl".

  (** Full normalization using provided reduction flags by first evaluating the
  head of the expression into weak-head normal form in _call-by-value_ order.
  Once a weak-head normal form is obtained, subterms are recursively reduced
  using the same strategy. *)
  Ltac2 @external cbv : red_flags -> t := "rocq-runtime.plugins.ltac2" "cbv".

  (** [cbn] was intended to be a more principled, faster and more predictable
  replacement for [simpl]. The main difference is that cbn may unfold constants
  even when they cannot be reused in recursive calls. Certain modifiers are also
  not treated the same. See the respective Ltac1 tactic documentation for more
  details. Setting [Debug "RAKAM"] makes [cbn] print various debugging
  information.. *)
  Ltac2 @external cbn : red_flags -> t := "rocq-runtime.plugins.ltac2" "cbn".

  (** Full normalization using provided reduction flags by first evaluating the
  head of the expression into weak-head normal form in _call-by-need_ order.
  Once a weak-head normal form is obtained, subterms are recursively reduced
  using the same strategy. *)
  Ltac2 @external lazy : red_flags -> t := "rocq-runtime.plugins.ltac2" "lazy".

  (** Applies delta-reduction to the constants specified by each [reference *
  occurrences] and then reduces to βιζ-normal form. Use the general reductions
  if you want to only apply the δ rule, for example [cbv] with [delta]. *)
  Ltac2 @external unfold : (reference * occurrences) list -> t := "rocq-runtime.plugins.ltac2" "unfold".

  (** First, reduces each [constr] using [red]. Then, every occurrence of the
  resulting terms will be replaced by its associated [constr]. *)
  Ltac2 @external fold : constr list -> t := "rocq-runtime.plugins.ltac2" "fold".

  (** Performs beta-expansion (the inverse of beta-reduction). The [constr]s
  must be free subterms in the subject of reduction. The expansion is done by:

  1. Replacing all selected occurrences of the [constr]s in the term with fresh
  variables

  2. Abstracting these variables

  3. Applying the abstracted term to the [constr]s *)
  Ltac2 @external pattern : (constr * occurrences) list -> t := "rocq-runtime.plugins.ltac2" "pattern".

  (** Optimized _call-by-value_ evaluation on a bytecode-based virtual machine.
  This algorithm is dramatically more efficient than the algorithm used for
  [cbv], but it cannot be fine-tuned. It is especially useful for full
  evaluation of algebraic objects. This includes the case of reflection-based
  tactics. *)
  Ltac2 @external vm : (pattern * occurrences) option -> t := "rocq-runtime.plugins.ltac2" "vm".

  (** Evaluates the goal by compilation to OCaml. Depending on the
  configuration, it can either default to [vm], recompile dependencies or fail
  due to some missing precompiled dependencies. See the [native-compiler] option
  for details. *)
  Ltac2 @external native : (pattern * occurrences) option -> t := "rocq-runtime.plugins.ltac2" "native".
End Red.

(** Reduction/expansion tactics *)

Ltac2 @external eval_in : Red.t -> clause -> unit := "rocq-runtime.plugins.ltac2" "reduce_in".

Ltac2 red (c : clause) : unit := eval_in Red.red c.

Ltac2 hnf (c : clause) : unit := eval_in Red.hnf c.

Ltac2 simpl (flags : red_flags) (occs : (pattern * occurrences) option) (c : clause) := eval_in (Red.simpl flags occs) c.

Ltac2 cbv (flags : red_flags) (c : clause) : unit := eval_in (Red.cbv flags) c.

Ltac2 cbn (flags : red_flags) (c : clause) : unit := eval_in (Red.cbn flags) c.

Ltac2 lazy (flags : red_flags) (c : clause) : unit := eval_in (Red.lazy flags) c.

Ltac2 unfold (occs : (reference * occurrences) list) (c : clause) : unit := eval_in (Red.unfold occs) c.

Ltac2 fold (cs : constr list) (c : clause) : unit := eval_in (Red.fold cs) c.

Ltac2 pattern (occs : (constr * occurrences) list) (c : clause) : unit := eval_in (Red.pattern occs) c.

Ltac2 vm (ctx : (pattern * occurrences) option) (c : clause) : unit := eval_in (Red.vm ctx) c.

Ltac2 native (ctx : (pattern * occurrences) option) (c : clause) : unit := eval_in (Red.native ctx) c.

(** Constr reduction/expansion functions *)

Ltac2 @external eval : Red.t -> constr -> constr := "rocq-runtime.plugins.ltac2" "reduce_constr".

Ltac2 eval_red (c : constr) : constr := eval Red.red c.

Ltac2 eval_hnf (c : constr) : constr := eval Red.hnf c.

Ltac2 eval_simpl (flags : red_flags) (occs : (pattern * occurrences) option) (c : constr) := eval (Red.simpl flags occs) c.

Ltac2 eval_cbv (flags : red_flags) (c : constr) : constr := eval (Red.cbv flags) c.

Ltac2 eval_cbn (flags : red_flags) (c : constr) : constr := eval (Red.cbn flags) c.

Ltac2 eval_lazy (flags : red_flags) (c : constr) : constr := eval (Red.lazy flags) c.

Ltac2 eval_unfold (occs : (reference * occurrences) list) (c : constr) : constr := eval (Red.unfold occs) c.

Ltac2 eval_fold (cs : constr list) (c : constr) : constr := eval (Red.fold cs) c.

Ltac2 eval_pattern (occs : (constr * occurrences) list) (c : constr) : constr := eval (Red.pattern occs) c.

Ltac2 eval_vm (ctx : (pattern * occurrences) option) (c : constr) : constr := eval (Red.vm ctx) c.

Ltac2 eval_native (ctx : (pattern * occurrences) option) (c : constr) : constr := eval (Red.native ctx) c.


Ltac2 @ external change : pattern option -> (constr array -> constr) -> clause -> unit := "rocq-runtime.plugins.ltac2" "tac_change".

Ltac2 @ external rewrite : evar_flag -> rewriting list -> clause -> (unit -> unit) option -> unit := "rocq-runtime.plugins.ltac2" "tac_rewrite".

Ltac2 @ external setoid_rewrite : orientation -> (unit -> constr_with_bindings) -> occurrences -> ident option -> unit := "rocq-runtime.plugins.ltac2" "tac_setoid_rewrite".

Ltac2 @ external reflexivity : unit -> unit := "rocq-runtime.plugins.ltac2" "tac_reflexivity".

Ltac2 @ external assumption : unit -> unit := "rocq-runtime.plugins.ltac2" "tac_assumption".
Ltac2 @ external eassumption : unit -> unit := "rocq-runtime.plugins.ltac2" "tac_eassumption".

Ltac2 @ external transitivity : constr -> unit := "rocq-runtime.plugins.ltac2" "tac_transitivity".

Ltac2 @ external etransitivity : constr option -> unit := "rocq-runtime.plugins.ltac2" "tac_etransitivity".

Ltac2 @ external cut : constr -> unit := "rocq-runtime.plugins.ltac2" "tac_cut".

Ltac2 @ external left : evar_flag -> bindings -> unit := "rocq-runtime.plugins.ltac2" "tac_left".
Ltac2 @ external right : evar_flag -> bindings -> unit := "rocq-runtime.plugins.ltac2" "tac_right".

Ltac2 @ external constructor : evar_flag -> unit := "rocq-runtime.plugins.ltac2" "tac_constructor".
Ltac2 @ external split : evar_flag -> bindings -> unit := "rocq-runtime.plugins.ltac2" "tac_split".

Ltac2 @ external constructor_n : evar_flag -> int -> bindings -> unit := "rocq-runtime.plugins.ltac2" "tac_constructorn".

Ltac2 @ external intros_until : hypothesis -> unit := "rocq-runtime.plugins.ltac2" "tac_introsuntil".

Ltac2 @ external symmetry : clause -> unit := "rocq-runtime.plugins.ltac2" "tac_symmetry".

Ltac2 @ external rename : (ident * ident) list -> unit := "rocq-runtime.plugins.ltac2" "tac_rename".

Ltac2 @ external revert : ident list -> unit := "rocq-runtime.plugins.ltac2" "tac_revert".

Ltac2 @ external admit : unit -> unit := "rocq-runtime.plugins.ltac2" "tac_admit".

Ltac2 @ external fix_ : ident -> int -> unit := "rocq-runtime.plugins.ltac2" "tac_fix".
Ltac2 @ external cofix_ : ident -> unit := "rocq-runtime.plugins.ltac2" "tac_cofix".

Ltac2 @ external clear : ident list -> unit := "rocq-runtime.plugins.ltac2" "tac_clear".
Ltac2 @ external keep : ident list -> unit := "rocq-runtime.plugins.ltac2" "tac_keep".

Ltac2 @ external clearbody : ident list -> unit := "rocq-runtime.plugins.ltac2" "tac_clearbody".

Ltac2 @ external exact_no_check : constr -> unit := "rocq-runtime.plugins.ltac2" "tac_exactnocheck".
Ltac2 @ external vm_cast_no_check : constr -> unit := "rocq-runtime.plugins.ltac2" "tac_vmcastnocheck".
Ltac2 @ external native_cast_no_check : constr -> unit := "rocq-runtime.plugins.ltac2" "tac_nativecastnocheck".

Ltac2 @ external inversion : inversion_kind -> destruction_arg -> intro_pattern option -> ident list option -> unit := "rocq-runtime.plugins.ltac2" "tac_inversion".

(** coretactics *)

Ltac2 @ external move : ident -> move_location -> unit := "rocq-runtime.plugins.ltac2" "tac_move".

Ltac2 @ external intro : ident option -> move_location option -> unit := "rocq-runtime.plugins.ltac2" "tac_intro".

Ltac2 @ external specialize : constr_with_bindings -> intro_pattern option -> unit := "rocq-runtime.plugins.ltac2" "tac_specialize".

(** extratactics *)

Ltac2 @ external discriminate : evar_flag -> destruction_arg option -> unit := "rocq-runtime.plugins.ltac2" "tac_discriminate".
Ltac2 @ external injection : evar_flag -> intro_pattern list option -> destruction_arg option -> unit := "rocq-runtime.plugins.ltac2" "tac_injection".

Ltac2 @ external absurd : constr -> unit := "rocq-runtime.plugins.ltac2" "tac_absurd".
Ltac2 @ external contradiction : constr_with_bindings option -> unit := "rocq-runtime.plugins.ltac2" "tac_contradiction".

Ltac2 @ external autorewrite : bool -> (unit -> unit) option -> ident list -> clause -> unit := "rocq-runtime.plugins.ltac2" "tac_autorewrite".

Ltac2 @ external autorewrite_backward : bool -> (unit -> unit) option -> ident list -> clause -> unit := "rocq-runtime.plugins.ltac2" "tac_autorewrite_backward".

Ltac2 @ external subst : ident list -> unit := "rocq-runtime.plugins.ltac2" "tac_subst".
Ltac2 @ external subst_all : unit -> unit := "rocq-runtime.plugins.ltac2" "tac_substall".

(** auto *)

Ltac2 Type debug := [ Off | Info | Debug ].

Ltac2 Type strategy := [ BFS | DFS ].

Ltac2 @ external trivial : debug -> reference list -> ident list option -> unit := "rocq-runtime.plugins.ltac2" "tac_trivial".

Ltac2 @ external auto : debug -> int option -> reference list -> ident list option -> unit := "rocq-runtime.plugins.ltac2" "tac_auto".

Ltac2 @ external eauto : debug -> int option -> reference list -> ident list option -> unit := "rocq-runtime.plugins.ltac2" "tac_eauto".

Ltac2 @ external typeclasses_eauto : strategy option -> int option -> ident list option -> unit := "rocq-runtime.plugins.ltac2" "tac_typeclasses_eauto".

Ltac2 @ external resolve_tc : constr -> unit := "rocq-runtime.plugins.ltac2" "tac_resolve_tc".
(** Resolve the existential variables appearing in the constr
    whose types are typeclasses.
    Fail if any of them cannot be resolved.
    Does not focus. *)

Ltac2 @ external unify : constr -> constr -> unit := "rocq-runtime.plugins.ltac2" "tac_unify".

Ltac2 @ external congruence : int option -> constr list option -> unit :=
  "rocq-runtime.plugins.ltac2" "congruence".

Ltac2 @ external simple_congruence : int option -> constr list option -> unit :=
  "rocq-runtime.plugins.ltac2" "simple_congruence".

Ltac2 @external f_equal : unit -> unit :=
  "rocq-runtime.plugins.ltac2" "f_equal".
