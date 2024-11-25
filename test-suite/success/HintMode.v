Module Postponing.

Class In A T := { IsIn : A -> T -> Prop }.
Class Empty T := { empty : T }.
Class EmptyIn (A T : Type) `{In A T} `{Empty T} :=
 { isempty : forall x, IsIn x empty -> False }.

#[export] Hint Mode EmptyIn ! ! - - : typeclass_instances.
#[export] Hint Mode Empty ! : typeclass_instances.
#[export] Hint Mode In ! - : typeclass_instances.
Existing Class IsIn.
Goal forall A T `{In A T} `{Empty T} `{EmptyIn A T}, forall x : A, IsIn x empty -> False.
 Proof.
   intros.
   eapply @isempty. (* Second goal needs to be solved first, to un-stuck the first one
   (hence the Existing Class IsIn to allow finding the assumption of IsIn here)  *)
   all:typeclasses eauto.
Qed.

End Postponing.

Module Heads.
  Set Primitive Projections.
  Class A (X : Type) := { somex : X }.
  Local Hint Mode A ! : typeclass_instances.

  Record foo := { car : Type; obj : car }.
  Local Instance foo_A (f : foo) : A (car f) := { somex := obj f }.

  Definition onef := {| car := nat; obj := 0 |}.
  Goal  {f : foo & A (car f)}.
  Proof.
    unshelve eexists; cycle 1.
    solve [typeclasses eauto].
    exact onef.
  Defined.
End Heads.

Module BestEffort.

  Class A (T : Type).
  Global Hint Mode A + : typeclass_instances.
  Class B (T : Type).
  Global Hint Mode B + : typeclass_instances.

  #[export] Instance a_imp_b T : A T -> B T := {}.
  #[export] Instance anat : B nat := {}.
  Lemma b : B nat * A nat.
  Proof.
    Fail split; typeclasses eauto.
    Set Typeclasses Debug Verbosity 2.
    Fail split; solve [typeclasses eauto best_effort].
    (* Here typeclasses eauto best_effort, when run on the 2 goals at once,
       can solve the B goal which has a nat instance nd whose mode is +
       (this morally assumes that there is only one instance matching B nat)
    *)
    split; typeclasses eauto best_effort.
    admit.
  Admitted.

End BestEffort.

Module Plus.
  Parameter plus : nat -> nat -> nat -> Prop.

  Axiom plus0l : forall m : nat, plus 0 m m.
  Axiom plus0r : forall n : nat, plus n 0 n.
  Axiom plusSl : forall n m r : nat, plus n m r -> plus (S n) m (S r).
  Axiom plusSr : forall n m r : nat, plus n m r -> plus m (S m) (S r).

  Hint Resolve plus0l plus0r plusSl plusSr : plus.
  Hint Mode plus ! - - : plus.
  Hint Mode plus - ! - : plus.

  Require Corelib.derive.Derive.
  Derive r SuchThat (plus 1 4 r) As r_proof.
  Proof.
    subst r. typeclasses eauto with plus.
  Qed.

  Goal exists x y, plus x y 12.
  Proof.
    eexists ?[x], ?[y].
    Set Typeclasses Debug.
    Fail typeclasses eauto with plus.
    instantiate (y := 1).
    typeclasses eauto with plus.
  Defined.
End Plus.

Module ModeAttr.
  Fail #[mode="+"] Inductive foo (A : Type) : Set :=.

  Fail #[mode=""] Class Foo (A : Type) := {}.
  #[mode="+"] Class Foo (A : Type) := {}.
  Fail #[mode="+ +"] Class Foo' (A : Type) := {}.
End ModeAttr.
