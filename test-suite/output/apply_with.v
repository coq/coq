Axiom f : forall a b c, a + b = 0 -> c = 0.
Goal 0 = 0.
Fail apply f with (d := 0).
apply f with (a:=0) (b:=0).
auto.
Qed.
