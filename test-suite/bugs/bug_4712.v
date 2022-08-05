Module Example1.

Notation "x =_s y" := (x = y) (at level 50).
Fail Check id=_sid.

End Example1.

Module Example2.
(* see https://coq.zulipchat.com/#narrow/stream/237664-math-comp-users/topic/Surprising.20parsing.20of.20the.20.E2.80.9C*l.E2.80.9D.20notation *)

Notation "*l" := Nat.add.
Check forall (T lT: Type) (x: T*lT), x = x. (* Expected to be "(x : T * lT)" *)

End Example2.
