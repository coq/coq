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

(* Check that no tuple needs to be built *)
Lemma l3 : (x,y:nat)
     (existS ? [n:nat]({n=n}+{n=n}) x (left ? ? (refl_equal nat x)))=
     (existS ? [n:nat]({n=n}+{n=n}) y (left ? ? (refl_equal nat y)))
  -> x=y.
Intros x y H.
Injection H.
Exact [H]H.
Qed.

(* Check that a tuple is built (actually the same as the initial one) *)
Lemma l4 : (p1,p2:{O=O}+{O=O})
    (existS ? [n:nat]({n=n}+{n=n}) O p1)=(existS ? [n:nat]({n=n}+{n=n}) O p2)
  ->(existS ? [n:nat]({n=n}+{n=n}) O p1)=(existS ? [n:nat]({n=n}+{n=n}) O p2).
Intros.
Injection H.
Exact [H]H.
Qed.

