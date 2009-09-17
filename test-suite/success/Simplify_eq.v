(* Check the behaviour of Simplify_eq *)

(* Check that Simplify_eq tries Intro until *)

Lemma l1 : 0 = 1 -> False.
 simplify_eq 1.
Qed.

Lemma l2 : forall (x : nat) (H : S x = S (S x)), H = H -> False.
 simplify_eq H.
intros.
apply (n_Sn x H0).
Qed.
