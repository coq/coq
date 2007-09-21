Require Export NumPrelude.

Module Type NZRingSig.

Parameter Inline NZ : Set.
Parameter Inline NZE : NZ -> NZ -> Prop.
Parameter Inline NZ0 : NZ.
Parameter Inline NZsucc : NZ -> NZ.
Parameter Inline NZplus : NZ -> NZ -> NZ.
Parameter Inline NZtimes : NZ -> NZ -> NZ.

Axiom NZE_equiv : equiv NZ NZE.
Add Relation NZ NZE
 reflexivity proved by (proj1 NZE_equiv)
 symmetry proved by (proj2 (proj2 NZE_equiv))
 transitivity proved by (proj1 (proj2 NZE_equiv))
as NZE_rel.

Add Morphism NZsucc with signature NZE ==> NZE as NZsucc_wd.
Add Morphism NZplus with signature NZE ==> NZE ==> NZE as NZplus_wd.
Add Morphism NZtimes with signature NZE ==> NZE ==> NZE as NZtimes_wd.

Delimit Scope NatIntScope with NatInt.
Open Local Scope NatIntScope.
Notation "x == y"  := (NZE x y) (at level 70) : NatIntScope.
Notation "x ~= y" := (~ NZE x y) (at level 70) : NatIntScope.
Notation "0" := NZ0 : NatIntScope.
Notation "'S'" := NZsucc.
Notation "1" := (S 0) : NatIntScope.
Notation "x + y" := (NZplus x y) : NatIntScope.
Notation "x * y" := (NZtimes x y) : NatIntScope.

Axiom NZsucc_inj : forall n1 n2 : NZ, S n1 == S n2 -> n1 == n2.

Axiom NZinduction :
  forall A : NZ -> Prop, predicate_wd NZE A ->
    A 0 -> (forall n : NZ, A n <-> A (S n)) -> forall n : NZ, A n.

Axiom NZplus_0_l : forall n : NZ, 0 + n == n.
Axiom NZplus_succ_l : forall n m : NZ, (S n) + m == S (n + m).

Axiom NZtimes_0_r : forall n : NZ, n * 0 == 0.
Axiom NZtimes_succ_r : forall n m : NZ, n * (S m) == n * m + n.

End NZRingSig.
