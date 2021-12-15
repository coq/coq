Require Import FSets.

Module SomeSetoids (Import M:FSetInterface.S).

Lemma Equal_refl : forall s, s[=]s.
Proof. red; split; auto. Qed.

Add Relation t Equal
 reflexivity proved by Equal_refl
 symmetry proved by eq_sym
 transitivity proved by eq_trans
 as EqualSetoid.

Add Morphism Empty with signature Equal ==> iff as Empty_m.
Proof.
unfold Equal, Empty; firstorder.
Qed.

End SomeSetoids.

Module Test (Import M:FSetInterface.S).
 Module A:=SomeSetoids M.
 Module B:=SomeSetoids M. (* lots of warning *)

 Lemma Test : forall s s', s[=]s' -> Empty s -> Empty s'.
 intros.
 rewrite H in H0.
 assumption.
Qed.
End Test.
