Require Import Ltac2.Ltac2.

Ltac2 congruence_dev () := congruence.
Ltac2 simpl_congruence_dev () := simple congruence.

Lemma congruence_test_1 : (forall x:bool, x = true) -> False.
Proof.
    intros.
    Fail congruence.
    Fail congruence 0 with false.
    Fail congruence 1 with true.
    congruence 1 with false.
Qed.

Lemma congruence_test_2 : (forall x:bool, x = true) -> False.
Proof.
    intros.
    Fail congruence.
    congruence with false.
Qed.

Lemma congruence_test_3 {A B} (f: A->B->A) (a:A) (b:B): f a b = a -> f (f a b) b = a.
Proof.
congruence.
Qed.

Lemma congruence_test_4 {A} (f: A->A) (a:A): f (f (f a)) = a -> f (f (f (f (f a)))) = a -> f a = a.
Proof.
congruence.
Qed.

Lemma simple_congruence_test_1 : (forall x:bool, x = true) -> False.
Proof.
    intros.
    Fail simple congruence.
    Fail simple congruence 0 with false.
    Fail simple congruence 1 with true.
    simple congruence 1 with false.
Qed.

Lemma simple_congruence_test_2 : (forall x:bool, x = true) -> False.
Proof.
    intros.
    Fail simple congruence.
    simple congruence with false.
Qed.

Lemma simple_congruence_test_3 {A B} (f: A->B->A) (a:A) (b:B): f a b = a -> f (f a b) b = a.
Proof.
simple congruence.
Qed.

Lemma simple_congruence_test_4 {A} (f: A->A) (a:A): f (f (f a)) = a -> f (f (f (f (f a)))) = a -> f a = a.
Proof.
simple congruence.
Qed.
