Axiom f : forall a b c, a + b = 0 -> c = 0.
Goal 0 = 0.
Fail apply f with (d := 0).
Fail apply f with (a := 0).
Fail rewrite <- f with (d := 0).
Fail rewrite <- f with (a := 0).
apply f with (a:=0) (b:=0).
auto.
Qed.

Axiom g : forall a b, S a = S b.
Goal forall n, n = 0.
intros n.
Fail injection g with (c := 0).
Fail injection g.
injection g with (a := n) (b := 0).
auto.
Qed.
