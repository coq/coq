(* Check the behaviour of Injection *)

(* Check that Injection tries Intro until *)

Lemma l1 : (x:nat)(S x)=(S (S x))->False.
Injection 1.
Apply n_Sn.
Qed.

Lemma l2 : (x:nat)(H:(S x)=(S (S x)))H==H->False.
Injection H.
Intros.
Apply (n_Sn x H0).
Qed.
