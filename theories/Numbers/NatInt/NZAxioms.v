Require Export NumPrelude.

Module Type NZAxiomsSig.

Parameter Inline NZ : Set.
Parameter Inline NZE : NZ -> NZ -> Prop.
Parameter Inline NZ0 : NZ.
Parameter Inline NZsucc : NZ -> NZ.
Parameter Inline NZpred : NZ -> NZ.
Parameter Inline NZplus : NZ -> NZ -> NZ.
Parameter Inline NZtimes : NZ -> NZ -> NZ.

Axiom NZE_equiv : equiv NZ NZE.
Add Relation NZ NZE
 reflexivity proved by (proj1 NZE_equiv)
 symmetry proved by (proj2 (proj2 NZE_equiv))
 transitivity proved by (proj1 (proj2 NZE_equiv))
as NZE_rel.

Add Morphism NZsucc with signature NZE ==> NZE as NZsucc_wd.
Add Morphism NZpred with signature NZE ==> NZE as NZpred_wd.
Add Morphism NZplus with signature NZE ==> NZE ==> NZE as NZplus_wd.
Add Morphism NZtimes with signature NZE ==> NZE ==> NZE as NZtimes_wd.

Delimit Scope NatIntScope with NatInt.
Open Local Scope NatIntScope.
Notation "x == y"  := (NZE x y) (at level 70) : NatIntScope.
Notation "x ~= y" := (~ NZE x y) (at level 70) : NatIntScope.
Notation "0" := NZ0 : NatIntScope.
Notation "'S'" := NZsucc : NatIntScope.
Notation "'P'" := NZpred : NatIntScope.
Notation "1" := (S 0) : NatIntScope.
Notation "x + y" := (NZplus x y) : NatIntScope.
Notation "x * y" := (NZtimes x y) : NatIntScope.

Axiom NZpred_succ : forall n : NZ, P (S n) == n.

Axiom NZinduction :
  forall A : NZ -> Prop, predicate_wd NZE A ->
    A 0 -> (forall n : NZ, A n <-> A (S n)) -> forall n : NZ, A n.

Axiom NZplus_0_l : forall n : NZ, 0 + n == n.
Axiom NZplus_succ_l : forall n m : NZ, (S n) + m == S (n + m).

Axiom NZtimes_0_r : forall n : NZ, n * 0 == 0.
Axiom NZtimes_succ_r : forall n m : NZ, n * (S m) == n * m + n.

End NZAxiomsSig.

Module Type NZOrdAxiomsSig.
Declare Module Export NZAxiomsMod : NZAxiomsSig.
Open Local Scope NatIntScope.

Parameter Inline NZlt : NZ -> NZ -> Prop.
Parameter Inline NZle : NZ -> NZ -> Prop.

Add Morphism NZlt with signature NZE ==> NZE ==> iff as NZlt_wd.
Add Morphism NZle with signature NZE ==> NZE ==> iff as NZle_wd.

Notation "x < y" := (NZlt x y) : NatIntScope.
Notation "x <= y" := (NZle x y) : NatIntScope.

Axiom NZle_lt_or_eq : forall n m : NZ, n <= m <-> n < m \/ n == m.
Axiom NZlt_irrefl : forall n : NZ, ~ (n < n).
Axiom NZlt_succ_le : forall n m : NZ, n < S m <-> n <= m.
End NZOrdAxiomsSig.

(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)
