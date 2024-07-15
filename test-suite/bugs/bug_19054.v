
Module PretypingWasRejectingFormerConvPbs.

Notation "x .+1" := (S x) (at level 1, left associativity, format "x .+1").

(** A Yoneda-style encoding of le *)
Parameter leR : nat -> nat -> SProp.
Class leY n m := le_intro : forall p, leR p n -> leR p m.
Infix "<=" := leY: nat_scope.

Definition leY_trans {n m p} (Hnm: n <= m) (Hmp: m <= p): n <= p :=
  fun q (Hqn: leR q n) => Hmp _ (Hnm _ Hqn).
Axiom  leY_down : forall {n m} (Hnm: n.+1 <= m), n <= m.

Infix "↕" := leY_trans (at level 45).
Notation "↓ p" := (leY_down p) (at level 40).

Ltac find _ := assumption || (apply leY_down; eapply leY_trans; eassumption).

(* Below, the presence of open constraints in the goal makes that the typing of 0 fails *)
Hint Extern 10 (_ <= _) => (find 0) : typeclass_instances.

Parameter p n q r : nat.
Parameter F : forall (Hp: p <= n), Type.
Parameter R : forall (Hpq: p <= q) (Hq: q <= n), F (Hpq ↕ Hq).

Section S.
Context {Hpr: p.+1 <= r} {Hrq: r <= q} {Hq: q <= n}.
Context (P : F (↓ (Hpr ↕ (Hrq ↕ Hq))) -> Prop).
Context (C : P (R _ _)).
End S.

End PretypingWasRejectingFormerConvPbs.

Module PretypingShouldCheckConvPbsAboutExpectedType.

Goal forall x y, x + y = 0 -> exists P, P x y.
eexists.
try exact H.
Abort.

End PretypingShouldCheckConvPbsAboutExpectedType.
