(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

Ltac2 Type red_flags := {
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

Ltac2 @ external intros : evar_flag -> intro_pattern list -> unit := "ltac2" "tac_intros".

Ltac2 @ external apply : advanced_flag -> evar_flag ->
  (unit -> constr_with_bindings) list -> (ident * (intro_pattern option)) option -> unit := "ltac2" "tac_apply".

Ltac2 @ external elim : evar_flag -> constr_with_bindings -> constr_with_bindings option -> unit := "ltac2" "tac_elim".
Ltac2 @ external case : evar_flag -> constr_with_bindings -> unit := "ltac2" "tac_case".

Ltac2 @ external generalize : (constr * occurrences * ident option) list -> unit := "ltac2" "tac_generalize".

Ltac2 @ external assert : assertion -> unit := "ltac2" "tac_assert".
Ltac2 @ external enough : constr -> (unit -> unit) option option -> intro_pattern option -> unit := "ltac2" "tac_enough".

Ltac2 @ external pose : ident option -> constr -> unit := "ltac2" "tac_pose".
Ltac2 @ external set : evar_flag -> (unit -> ident option * constr) -> clause -> unit := "ltac2" "tac_set".

Ltac2 @ external remember : evar_flag -> ident option -> (unit -> constr) -> intro_pattern option -> clause -> unit := "ltac2" "tac_remember".

Ltac2 @ external destruct : evar_flag -> induction_clause list ->
  constr_with_bindings option -> unit := "ltac2" "tac_destruct".

Ltac2 @ external induction : evar_flag -> induction_clause list ->
  constr_with_bindings option -> unit := "ltac2" "tac_induction".

Ltac2 @ external red : clause -> unit := "ltac2" "tac_red".
Ltac2 @ external hnf : clause -> unit := "ltac2" "tac_hnf".
Ltac2 @ external simpl : red_flags -> (pattern * occurrences) option -> clause -> unit := "ltac2" "tac_simpl".
Ltac2 @ external cbv : red_flags -> clause -> unit := "ltac2" "tac_cbv".
Ltac2 @ external cbn : red_flags -> clause -> unit := "ltac2" "tac_cbn".
Ltac2 @ external lazy : red_flags -> clause -> unit := "ltac2" "tac_lazy".
Ltac2 @ external unfold : (reference * occurrences) list -> clause -> unit := "ltac2" "tac_unfold".
Ltac2 @ external fold : constr list -> clause -> unit := "ltac2" "tac_fold".
Ltac2 @ external pattern : (constr * occurrences) list -> clause -> unit := "ltac2" "tac_pattern".
Ltac2 @ external vm : (pattern * occurrences) option -> clause -> unit := "ltac2" "tac_vm".
Ltac2 @ external native : (pattern * occurrences) option -> clause -> unit := "ltac2" "tac_native".

Ltac2 @ external eval_red : constr -> constr := "ltac2" "eval_red".
Ltac2 @ external eval_hnf : constr -> constr := "ltac2" "eval_hnf".
Ltac2 @ external eval_red : constr -> constr := "ltac2" "eval_red".
Ltac2 @ external eval_simpl : red_flags -> (pattern * occurrences) option -> constr -> constr := "ltac2" "eval_simpl".
Ltac2 @ external eval_cbv : red_flags -> constr -> constr := "ltac2" "eval_cbv".
Ltac2 @ external eval_cbn : red_flags -> constr -> constr := "ltac2" "eval_cbn".
Ltac2 @ external eval_lazy : red_flags -> constr -> constr := "ltac2" "eval_lazy".
Ltac2 @ external eval_unfold : (reference * occurrences) list -> constr -> constr := "ltac2" "eval_unfold".
Ltac2 @ external eval_fold : constr list -> constr -> constr := "ltac2" "eval_fold".
Ltac2 @ external eval_pattern : (constr * occurrences) list -> constr -> constr := "ltac2" "eval_pattern".
Ltac2 @ external eval_vm : (pattern * occurrences) option -> constr -> constr := "ltac2" "eval_vm".
Ltac2 @ external eval_native : (pattern * occurrences) option -> constr -> constr := "ltac2" "eval_native".

Ltac2 @ external change : pattern option -> (constr array -> constr) -> clause -> unit := "ltac2" "tac_change".

Ltac2 @ external rewrite : evar_flag -> rewriting list -> clause -> (unit -> unit) option -> unit := "ltac2" "tac_rewrite".

Ltac2 @ external reflexivity : unit -> unit := "ltac2" "tac_reflexivity".

Ltac2 @ external assumption : unit -> unit := "ltac2" "tac_assumption".

Ltac2 @ external transitivity : constr -> unit := "ltac2" "tac_transitivity".

Ltac2 @ external etransitivity : unit -> unit := "ltac2" "tac_etransitivity".

Ltac2 @ external cut : constr -> unit := "ltac2" "tac_cut".

Ltac2 @ external left : evar_flag -> bindings -> unit := "ltac2" "tac_left".
Ltac2 @ external right : evar_flag -> bindings -> unit := "ltac2" "tac_right".

Ltac2 @ external constructor : evar_flag -> unit := "ltac2" "tac_constructor".
Ltac2 @ external split : evar_flag -> bindings -> unit := "ltac2" "tac_split".

Ltac2 @ external constructor_n : evar_flag -> int -> bindings -> unit := "ltac2" "tac_constructorn".

Ltac2 @ external intros_until : hypothesis -> unit := "ltac2" "tac_introsuntil".

Ltac2 @ external symmetry : clause -> unit := "ltac2" "tac_symmetry".

Ltac2 @ external rename : (ident * ident) list -> unit := "ltac2" "tac_rename".

Ltac2 @ external revert : ident list -> unit := "ltac2" "tac_revert".

Ltac2 @ external admit : unit -> unit := "ltac2" "tac_admit".

Ltac2 @ external fix_ : ident option -> int -> unit := "ltac2" "tac_fix".
Ltac2 @ external cofix_ : ident option -> unit := "ltac2" "tac_cofix".

Ltac2 @ external clear : ident list -> unit := "ltac2" "tac_clear".
Ltac2 @ external keep : ident list -> unit := "ltac2" "tac_keep".

Ltac2 @ external clearbody : ident list -> unit := "ltac2" "tac_clearbody".

Ltac2 @ external exact_no_check : constr -> unit := "ltac2" "tac_exactnocheck".
Ltac2 @ external vm_cast_no_check : constr -> unit := "ltac2" "tac_vmcastnocheck".
Ltac2 @ external native_cast_no_check : constr -> unit := "ltac2" "tac_nativecastnocheck".

Ltac2 @ external inversion : inversion_kind -> destruction_arg -> intro_pattern option -> ident list option -> unit := "ltac2" "tac_inversion".

(** coretactics *)

Ltac2 @ external move : ident -> move_location -> unit := "ltac2" "tac_move".

Ltac2 @ external intro : ident option -> move_location option -> unit := "ltac2" "tac_intro".

Ltac2 @ external specialize : constr_with_bindings -> intro_pattern option -> unit := "ltac2" "tac_specialize".

(** extratactics *)

Ltac2 @ external discriminate : evar_flag -> destruction_arg option -> unit := "ltac2" "tac_discriminate".
Ltac2 @ external injection : evar_flag -> intro_pattern list option -> destruction_arg option -> unit := "ltac2" "tac_injection".

Ltac2 @ external absurd : constr -> unit := "ltac2" "tac_absurd".
Ltac2 @ external contradiction : constr_with_bindings option -> unit := "ltac2" "tac_contradiction".

Ltac2 @ external autorewrite : bool -> (unit -> unit) option -> ident list -> clause -> unit := "ltac2" "tac_autorewrite".

Ltac2 @ external subst : ident list -> unit := "ltac2" "tac_subst".
Ltac2 @ external subst_all : unit -> unit := "ltac2" "tac_substall".

(** auto *)

Ltac2 Type debug := [ Off | Info | Debug ].

Ltac2 Type strategy := [ BFS | DFS ].

Ltac2 @ external trivial : debug -> (unit -> constr) list -> ident list option -> unit := "ltac2" "tac_trivial".

Ltac2 @ external auto : debug -> int option -> (unit -> constr) list -> ident list option -> unit := "ltac2" "tac_auto".

Ltac2 @ external new_auto : debug -> int option -> (unit -> constr) list -> ident list option -> unit := "ltac2" "tac_newauto".

Ltac2 @ external eauto : debug -> int option -> int option -> (unit -> constr) list -> ident list option -> unit := "ltac2" "tac_eauto".

Ltac2 @ external typeclasses_eauto : strategy option -> int option -> ident list option -> unit := "ltac2" "tac_typeclasses_eauto".
