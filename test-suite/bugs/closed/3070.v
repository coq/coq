(* Testing subst wrt chains of dependencies *)

Lemma foo (a1 a2 : Set) (b1 : a1 -> Prop)
      (Ha : a1 = a2) (c : a1) (d : b1 c) : True.
Proof.
  subst.
