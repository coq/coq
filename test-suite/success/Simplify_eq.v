(* Check the behaviour of Simplify_eq *)

(* Check that Simplify_eq tries Intro until *)

Lemma l1 : O=(S O)->False.   
Simplify_eq 1.
Qed.

Lemma l2 : (x:nat)(H:(S x)=(S (S x)))H==H->False.   
Simplify_eq H.
Intros.
Apply (n_Sn x H0).
Qed.
