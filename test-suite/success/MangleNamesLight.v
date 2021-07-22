Axiom X : Type.

Goal forall (x y z : X), X.
intro. Check x.
Set Mangle Names.
intro. Fail Check y. Check _0.
Set Mangle Names Light.
intro. Fail Check z. Fail Check _1. Check _z.
Abort.

Fixpoint Lots (n : nat) : Type :=
  match n with
  | 0 => X
  | S k => forall (x : X), Lots k
  end.

Goal Lots 10.
assert (_x8 : X) by admit.
cbv; intros.
Check _x9.
Abort.

Fixpoint Lots' (x : X) (n : nat) : Type :=
  match n with
  | 0 => X
  | S k => forall _x, Lots' _x k
  end.

Goal forall _x0, Lots' _x0 10.
assert (_x8 : X) by admit.
cbv; intros.
Check __x9.
simpl.
Abort.
