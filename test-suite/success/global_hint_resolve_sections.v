Create HintDb ghrs_basic.
Create HintDb ghrs_constructors.
Create HintDb ghrs_extra.
Create HintDb ghrs_nested.
Create HintDb ghrs_local_def.
Create HintDb ghrs_local_head.
Create HintDb ghrs_local_inductive.
Create HintDb ghrs_direction_l2r.
Create HintDb ghrs_direction_r2l.
Create HintDb ghrs_priority_default.
Create HintDb ghrs_priority_explicit.
Create HintDb ghrs_eapply_after_discharge.

Inductive SecPred (A : Type) : Prop :=
| sec_pred_intro : A -> SecPred A.

Section Basic.
  Context (A : Type) (a : A).

  Lemma basic_hint : SecPred A.
  Proof. exact (sec_pred_intro A a). Qed.

  #[global] Hint Resolve basic_hint : ghrs_basic.

  Goal SecPred A.
  Proof. intros. auto with ghrs_basic. Qed.
End Basic.

Goal forall (A : Type) (a : A), SecPred A.
Proof. intros. auto with ghrs_basic. Qed.

Section Constructors.
  Context (A : Type) (a : A).

  #[global] Hint Constructors SecPred : ghrs_constructors.

  Goal SecPred A.
  Proof. intros. auto with ghrs_constructors. Qed.
End Constructors.

Goal forall (A : Type) (a : A), SecPred A.
Proof. intros. auto with ghrs_constructors. Qed.

Section MultipleDatabases.
  Context (n : nat).

  Definition multi_db_hint : SecPred nat := sec_pred_intro nat n.

  #[global] Hint Resolve multi_db_hint : ghrs_basic ghrs_extra.

  Goal SecPred nat.
  Proof. auto with ghrs_extra. Qed.
End MultipleDatabases.

Goal forall n : nat, SecPred nat.
Proof.
  intros.
  Succeed auto with ghrs_basic.
  auto with ghrs_extra.
Qed.

Inductive NestedPred (A : Type) (x : A) : Prop :=
| nested_pred_intro : NestedPred A x.

Section Outer.
  Context (A : Type).

  Section Inner.
    Context (x : A).

    Lemma nested_hint : NestedPred A x.
    Proof. exact (nested_pred_intro A x). Qed.

    #[global] Hint Resolve nested_hint : ghrs_nested.

    Goal NestedPred A x.
    Proof. auto with ghrs_nested. Qed.
  End Inner.
End Outer.

Goal forall (A : Type) (x : A), NestedPred A x.
Proof.
  intros; auto with ghrs_nested.
Qed.

Inductive LocalDefPred : nat -> Prop :=
| local_def_intro : LocalDefPred 2.

Section LocalDefinition.
  Let two := 2.

  Lemma local_def_hint : LocalDefPred two.
  Proof. exact local_def_intro. Qed.

  #[global] Hint Resolve local_def_hint : ghrs_local_def.

  Goal LocalDefPred two.
  Proof. auto with ghrs_local_def. Qed.
End LocalDefinition.

Goal LocalDefPred 2.
Proof.
  auto with ghrs_local_def.
Qed.

Section LocalHeadAfterDischarge.
  Let Alias := True.

  Lemma local_head_hint : Alias.
  Proof. exact I. Qed.

  #[global] Hint Resolve local_head_hint : ghrs_local_head.
End LocalHeadAfterDischarge.

Goal True.
Proof. auto with ghrs_local_head nocore. Qed.

Section LocalInductiveConstructors.
  Context (A : Type) (a : A).

  Inductive LocalBox : Type :=
  | local_box : A -> LocalBox.

  #[global] Hint Constructors LocalBox : ghrs_local_inductive.
End LocalInductiveConstructors.

Goal forall (A : Type) (a : A), LocalBox A.
Proof. intros; auto with ghrs_local_inductive nocore. Qed.

Inductive LeftPred (A : Type) : Prop :=
| left_pred_intro : A -> LeftPred A.

Inductive RightPred (A : Type) : Prop :=
| right_pred_intro : A -> RightPred A.

Section DirectionalResolve.
  Context (A : Type) (a : A).

  Lemma directional_hint : LeftPred A <-> RightPred A.
  Proof.
    split; intros; [exact (right_pred_intro A a) | exact (left_pred_intro A a)].
  Qed.

  #[global] Hint Resolve -> directional_hint : ghrs_direction_l2r.
  #[global] Hint Resolve <- directional_hint : ghrs_direction_r2l.
End DirectionalResolve.

Goal forall (A : Type) (a : A), LeftPred A -> RightPred A.
Proof. intros; auto with ghrs_direction_l2r nocore. Qed.

Goal forall (A : Type) (a : A), RightPred A -> LeftPred A.
Proof. intros; auto with ghrs_direction_r2l nocore. Qed.

Inductive PriorityChoice (A : Type) : Type :=
| priority_good : PriorityChoice A
| priority_bad : A -> PriorityChoice A.

Definition priority_good_hint {A : Type} : PriorityChoice A := priority_good A.
#[global] Hint Resolve priority_good_hint : ghrs_priority_default.

Section DefaultPriorityAfterDischarge.
  Context (A : Type) (a : A).

  Definition priority_bad_hint : PriorityChoice A := priority_bad A a.

  #[global] Hint Resolve priority_bad_hint : ghrs_priority_default.
End DefaultPriorityAfterDischarge.

Definition priority_default_selected (n : nat) : PriorityChoice nat :=
  ltac:(auto with ghrs_priority_default).

Goal priority_default_selected 0 = priority_good nat.
Proof. reflexivity. Qed.

Definition priority_explicit_good_hint {A : Type} : PriorityChoice A := priority_good A.
#[global] Hint Resolve priority_explicit_good_hint : ghrs_priority_explicit.

Section ExplicitPriorityAfterDischarge.
  Context (A : Type) (a : A).

  Definition priority_explicit_bad_hint : PriorityChoice A := priority_bad A a.

  #[global] Hint Resolve priority_explicit_bad_hint | 0 : ghrs_priority_explicit.
End ExplicitPriorityAfterDischarge.

Definition priority_explicit_selected (n : nat) : PriorityChoice nat :=
  ltac:(auto with ghrs_priority_explicit).

Goal priority_explicit_selected 0 = priority_bad nat 0.
Proof. reflexivity. Qed.

Inductive EApplyRel : nat -> nat -> Prop :=
| eapply_rel_01 : EApplyRel 0 1
| eapply_rel_10 : EApplyRel 1 0
| eapply_rel_trans : forall mid : nat,
    EApplyRel 0 mid -> EApplyRel mid 0 -> EApplyRel 0 0.

#[global] Hint Resolve eapply_rel_01 eapply_rel_10 : ghrs_eapply_after_discharge.

Section EApplyAfterDischarge.
  Context (mid : nat).

  Definition eapply_after_discharge_hint :
    EApplyRel 0 mid -> EApplyRel mid 0 -> EApplyRel 0 0 := eapply_rel_trans mid.

  #[global] Hint Resolve eapply_after_discharge_hint : ghrs_eapply_after_discharge.
End EApplyAfterDischarge.

Goal EApplyRel 0 0.
Proof.
  (* The section parameter [mid] is not inferable by [auto]; [eauto]
     must use the discharged hint as an eapply hint. The informational
     "only be used by eauto" message is not checked in this success test. *)
  Fail solve [auto with ghrs_eapply_after_discharge nocore].
  eauto with ghrs_eapply_after_discharge nocore.
Qed.

Module Type GhrsFunctorSig.
  Parameter T : Type.
  Parameter t : T.
End GhrsFunctorSig.

Module GhrsFunctor (X : GhrsFunctorSig).
  Create HintDb ghrs_functor.

  Inductive FunctorPred : X.T -> Prop :=
  | functor_pred_intro : forall x : X.T, FunctorPred x.

  Section FunctorSection.
    Context (x : X.T).

    Lemma functor_hint : FunctorPred x.
    Proof. exact (functor_pred_intro x). Qed.

    #[global] Hint Resolve functor_hint : ghrs_functor.
  End FunctorSection.

  Goal forall x : X.T, FunctorPred x.
  Proof. intros; auto with ghrs_functor. Qed.
End GhrsFunctor.

Module GhrsNatSig <: GhrsFunctorSig.
  Definition T := nat.
  Definition t := 0.
End GhrsNatSig.

Module GhrsNatFunctor := GhrsFunctor GhrsNatSig.
Import GhrsNatFunctor.

Goal forall x : GhrsNatSig.T, FunctorPred x.
Proof.
  intros; auto with ghrs_functor.
Qed.

Module Universes.
  Create HintDb ghrs_universe_polymorphic.
  Create HintDb ghrs_universe_constrained.
  Create HintDb ghrs_universe_constrained_section.
  Set Universe Polymorphism.
  Monomorphic Universe ghrs_mono.

  Polymorphic Inductive UPolyPred (A : Type) : Type :=
  | u_poly_intro : A -> UPolyPred A.

  Section UniversePolymorphicHint.
    Context (A : Type) (a : A).
    Polymorphic Lemma u_poly_hint : UPolyPred A.
    Proof. exact (u_poly_intro A a). Qed.

    #[global] Hint Resolve u_poly_hint : ghrs_universe_polymorphic.
  End UniversePolymorphicHint.

  Goal forall (A : Type) (a : A), UPolyPred A.
  Proof. intros; auto with ghrs_universe_polymorphic. Qed.

  Polymorphic Definition constrained_hint@{u | u < ghrs_mono}
    (A : Type@{u}) : True := I.

  Section ConstrainedPreexistingHint.
    #[global] Hint Resolve constrained_hint : ghrs_universe_constrained.
  End ConstrainedPreexistingHint.

  Check constrained_hint.

  Section ConstrainedSectionHint.
    Context (n : nat).

    Polymorphic Definition constrained_section_hint@{u | u < ghrs_mono}
      (A : Type@{u}) : True := match n with _ => I end.

    #[global] Hint Resolve constrained_section_hint : ghrs_universe_constrained_section.
  End ConstrainedSectionHint.

  Check constrained_section_hint.
End Universes.
