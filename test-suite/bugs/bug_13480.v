Axiom dummy : forall x : nat, x = 0.

Goal forall x : nat, x = 0.
Proof.
intros x.
replace -> x with 0.
+ apply (eq_refl 0).
+ apply (dummy x).
Qed.

Goal forall x : nat, x = 0.
Proof.
intros x.
replace <- x with 0.
+ apply (eq_refl 0).
+ symmetry; apply (dummy x).
Qed.

Goal forall x : nat, x = 0.
Proof.
intros x.
replace x with 0.
+ apply (eq_refl 0).
+ symmetry; apply (dummy x).
Qed.
