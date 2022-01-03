Inductive Prod (s1 s2 : Set) : Set :=
  | Pair : s1 -> s2 -> Prod s1 s2.

Arguments Pair {_ _} _ _.

Axiom A1 : forall (s1 s2 : Set) (e1 : s1) (e2 : s2) (p1 : Prod s1 s2),
  True -> p1 = Pair e1 e2.

Lemma L1 : forall (s1 s2 : Set) (e1 e3 : s1) (e2 e4 : s2)
  (p1 : Prod s1 s2) (p2 : Prod s1 s2), True -> p1 = Pair e1 e2 ->
  p2 = Pair e3 e4 -> True.
Proof.
intros s1 s2 e1 e3 e2 e4 p1 p2 H1 H2 H3.
repeat rewrite (A1 s1 s2 e1 e2 _ H1) in *.
Check (H2 : Pair e1 e2 = Pair e1 e2).
Check (H3 : Pair e1 e2 = Pair e3 e4).
exact I.
Qed.
