Require Import Bool.

Goal forall axiom, transparent_true true axiom = I.
Proof. intros. exact eq_refl. Qed.

Goal forall axiom1 axiom2,
  Is_true_hprop true (transparent_true true axiom1) (transparent_true true axiom2) = eq_refl.
Proof. intros. exact eq_refl. Qed.
