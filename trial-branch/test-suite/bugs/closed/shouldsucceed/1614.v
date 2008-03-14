Require Import Ring.
Require Import ArithRing.

Fixpoint eq_nat_bool (x y : nat) {struct x} : bool :=
match x, y with
| 0, 0 => true
| S x', S y' => eq_nat_bool x' y'
| _, _ => false
end.

Theorem eq_nat_bool_implies_eq : forall x y, eq_nat_bool x y = true -> x = y.
Proof.
induction x; destruct y; simpl; intro H; try (reflexivity || inversion H).
apply IHx in H; rewrite H; reflexivity.
Qed.

Add Ring MyNatSRing : natSRth (decidable eq_nat_bool_implies_eq).

Goal 0 = 0.
  ring.
Qed.
