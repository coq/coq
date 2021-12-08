Require Import TestSuite.admit.
Require Setoid.

Variables P Q : forall {T : Set}, T -> Prop.

Lemma rule{T : Set}{x : T} : Q x <-> P x. admit. Qed.

Goal forall (T : Set)(x : T), Q x <-> P x.
Proof.
intros T x.
setoid_rewrite rule.
reflexivity.
Qed.
