Require Import FunctionalExtensionality.
Require Import Init.Wf.

Lemma fix_sub_eq_ext :
  forall (A : Type) (R : A -> A -> Prop) (Rwf : well_founded R)
    (P : A -> Type)
    (F_sub : forall x : A, (forall y:{y : A | R y x}, P (proj1_sig y)) -> P x),
    forall x : A,
      Fix_sub A R Rwf P F_sub x =
        F_sub x (fun y:{y : A | R y x} => Fix_sub A R Rwf P F_sub (proj1_sig y)).
Proof.
  intros A R Rwf P F_sub x; apply Fix_sub_eq ; auto.
  intros ? f g H.
  assert(f = g) as H0.
  - extensionality y ; apply H.
  - rewrite H0 ; auto.
Qed.

Ltac unfold_sub f fargs :=
  set (call:=fargs) ; unfold f in call ; unfold call ; clear call ;
    rewrite fix_sub_eq_ext ; repeat fold_sub f ; simpl proj1_sig.
