Require Import TestSuite.admit.
Goal forall m n, n+n = m+m -> m+m = m+m.
Proof.
intros.
set (k := n+n) in *.
cut (n=m).
intro.
subst n.
admit.
admit.
Qed.

Goal forall m n, n+n = m+m -> n+n = m+m.
Proof.
intros.
set (k := n+n).
cut (n=m).
intro.
subst n.
admit.
admit.
Qed.
