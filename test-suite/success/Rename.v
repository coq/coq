Goal forall n : nat, n = 0 -> n = 0.
intros.
rename n into p.
induction p; auto.
Qed.
