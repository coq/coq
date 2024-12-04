Require Import Bool.

Goal forall axiom, @transparent_Is_true true axiom = I.
Proof. intros. exact eq_refl. Qed.

Goal forall axiom1 axiom2,
  Is_true_hprop true (transparent_Is_true _ axiom1) (transparent_Is_true _ axiom2) = eq_refl.
Proof. intros. exact eq_refl. Qed.


Goal forall axiom, @transparent_eq_true true axiom = is_eq_true.
Proof. intros. exact eq_refl. Qed.

Goal forall axiom1 axiom2,
  eq_true_hprop true (transparent_eq_true _ axiom1) (transparent_eq_true _ axiom2) = eq_refl.
Proof. intros. exact eq_refl. Qed.

(* These notations are not keywords *)
Goal True.
  assert_succeeds pose (fun transparent_Is_true : nat => transparent_Is_true).
  assert_succeeds pose (fun transparent_eq_true : nat => transparent_eq_true).
Abort.
