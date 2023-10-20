(* Bug #5481 *)

Set Universe Polymorphism.

Parameter P : Type -> Type -> Prop.
Parameter A : Type.
Lemma foo (B : Type) (H : P A B) : P A B.
Proof.
  congruence.
Qed.

(* An example with types hidden behind "match" *)

Parameter b : unit.
Lemma foo2 (B : Type) (H : (let () := b in P) A B) : (let () := b in P) A B.
Proof.
  congruence.
Qed.

(* Bug #9979, with f_equal *)

Record Map(K V: Type) := {
  rep: Type;
  put: rep -> K -> V -> rep;
}.

Section Test.
  Universes u1 u2 u3 u4 u5 u6.

  Goal forall K V (M: Map K V) (k: K) (v: V) (m: rep K V M),
      put@{u1 u2 u3} K V M m k v = put@{u4 u5 u6} K V M m k v.
  Proof.
    intros.
    f_equal.
  Qed.

End Test.

(* An example with unification of monomorphic universe levels *)

Unset Universe Polymorphism.

Lemma foo3 (B : Type) : Type.
Proof.
  congruence.
Qed.
