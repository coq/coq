
Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Classes.Equivalence.

Section Equiv.
  Context [ Equivalence A eqA ].

  Variables x y z w : A.

  Goal eqA x y -> eqA y x.
    intros H ; clrewrite H.
    refl.
  Qed.

  Tactic Notation "simpl" "*" := auto || relation_tac.

  Goal eqA x y -> eqA y x /\ True.
    intros H ; clrewrite H.
    split ; simpl*.
  Qed.

  Goal eqA x y -> eqA y x /\ eqA x x.
    intros H ; clrewrite H.
    split ; simpl*.
  Qed.

  Goal eqA x y -> eqA y z -> eqA x y.
    intros H.
    clrewrite H.
    intro. refl.
  Qed.

  Goal eqA x y -> eqA z y -> eqA x y.
    intros H.
    clrewrite <- H at 2.
    clrewrite <- H at 1.
    intro. refl.
  Qed.

  Opaque complement.

  Print iff_inverse_impl_binary_morphism.

  Goal eqA x y -> eqA x y -> eqA x y.
    intros H.
    clrewrite H.
    intro. refl.
  Qed.

  Goal eqA x y -> eqA x y -> eqA x y.
    intros H.
    clrewrite <- H.
    refl.
  Qed.

  Goal eqA x y -> True /\ True /\ False /\ eqA x x -> True /\ True /\ False /\ eqA x y.
  Proof.
    intros.
    clrewrite <- H.
    apply H0.
  Qed.

End Equiv.

Section Trans.
  Context [ Transitive A R ].

  Variables x y z w : A.

  Tactic Notation "simpl" "*" := auto || relation_tac.

(*   Typeclasses eauto := debug. *)

  Goal R x y -> R y x -> R y y -> R x x.
  Proof with auto.
    intros H H' H''.

    clrewrite <- H' at 2.
    clrewrite H at 1...
  Qed.

  Goal R x y -> R y z -> R x z.
    intros H.
    clrewrite H.
    refl.
  Qed.

  Goal R x y -> R z y -> R x y.
    intros H.
    clrewrite <- H at 2.
    intro.
    clrewrite H at 1.
  Abort.

  Goal R x y -> True /\ R y z -> True /\ R x z.
  Proof.
    intros.
    clrewrite H.
    apply H0.
  Qed.

  Goal R x y -> True /\ True /\ False /\ R y z -> True /\ True /\ False /\ R x z.
  Proof.
    intros.
    clrewrite H.
    apply H0.
  Qed.

End Trans.
