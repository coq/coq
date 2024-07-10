From Stdlib Require Import Vector Program.

Module T.

Inductive T A B : forall n, t A n -> Type := cons n m p c d e : A -> B -> T A B n c -> T A B m d -> T A B p e.

Program Definition h {A B : Type} {n1 n2 : nat} (v1 : t A n1) (v2 : t A n2) (p1 : T A B n1 v1) (p2 : T A B n2 v2) : nat :=
  match p1, p2 with
    | cons _ _ i1 j1 k1 c1 d1 e1 a1 b1 q1 r1, cons _ _ i2 j2 k2 c2 d2 e2 a2 b2 q2 r2 => 0
  end.

Program Definition h2 {A B : Type} b {n1 n2 : nat} (v1 : t A n1) (v2 : t A n2) (p1 : T A B n1 v1) (p2 : T A B n2 v2) : nat :=
  match b, p1, p2 with
    | true, cons _ _ i1 j1 k1 c1 d1 e1 a1 b1 q1 r1, _ => 0
    | false, _, cons _ _ i2 j2 k2 c2 d2 e2 a2 b2 q2 r2 => 0
  end.

End T.

Module U.

Inductive U A B : forall n, t A n -> Type :=
  | cons n m p c d e : A -> B -> U A B n c -> U A B m d -> U A B p e
  | nil n c : U A B n c.

Program Definition h {A B : Type} {n1 n2 : nat} (v1 : t A n1) (v2 : t A n2) (p1 : U A B n1 v1) (p2 : U A B n2 v2) : nat :=
  match p1, p2 with
    | cons _ _ i1 j1 k1 c1 d1 e1 a1 b1 q1 r1, _ => 0
    | _, cons _ _ i2 j2 k2 c2 d2 e2 a2 b2 q2 r2 => 0
    | _, _ => 0
  end.

End U.
