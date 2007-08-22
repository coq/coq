Require Export Relation_Definitions.
Require Export Setoid.

Variable A : Type.
Variable S : A -> Type.
Variable Seq : forall (a:A), relation (S a).

Hypothesis Seq_refl : forall (a:A) (x : S a), Seq a x x.
Hypothesis Seq_sym : forall (a:A) (x y : S a), Seq a x y -> Seq a y x.
Hypothesis Seq_trans : forall (a:A) (x y z : S a), Seq a x y -> Seq a y z ->
Seq
a x z.

Add Relation S Seq
 reflexivity proved by Seq_refl
 symmetry proved by Seq_sym
 transitivity proved by Seq_trans
 as S_Setoid.

Goal forall (a : A) (x y : S a), Seq a x y -> Seq a x y.
  intros a x y H.
  setoid_replace x with y using relation Seq.
  apply Seq_refl. trivial.
Qed.
