(* Test robustness of Groebner tactic in presence of disequalities *)

Require Export Reals.
Require Export Nsatz.

Open Scope R_scope.

Lemma essai :
 forall yb xb m1 m2 xa ya,
  xa <> xb ->
 yb - 2 * m2 * xb = ya - m2 * xa -> 
 yb - m1 * xb = ya - m1 * xa ->
 yb - ya = (2 * xb - xa) * m2 -> 
 yb - ya = (xb - xa) * m1.
Proof.
intros.
(* clear H. groebner used not to work when H was not cleared *)
nsatz.
Qed.

