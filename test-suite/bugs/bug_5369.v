Require Import Corelib.Classes.Morphisms Corelib.Setoids.Setoid.
Axiom f g : nat -> nat -> nat.
Axiom Hfg : forall n m, n = n -> f n m = g n m.
Axiom LetIn : forall {A B} (x : A) (f : A -> B), B.
Axiom LetIn_Proper : forall A B, Proper (eq ==> pointwise_relation _ eq ==> eq)
(@ LetIn A B).
#[export] Existing Instance LetIn_Proper.

Goal forall n, LetIn n (fun n' => f 1 n') = LetIn n (fun n' => g 1 n').
Proof.
  intros.
  setoid_rewrite Hfg.
  - reflexivity.
  - exact (eq_refl 1).
Qed.
