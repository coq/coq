Require Export Relation_Definitions.
Require Export Setoid.

Parameter A : Type.
Parameter S : A -> Type.
Parameter Seq : forall {a:A}, relation (S a).

Axiom Seq_refl : forall {a:A} (x : S a), Seq x x.
Axiom Seq_sym : forall {a:A} (x y : S a), Seq x y -> Seq y x.
Axiom Seq_trans : forall {a:A} (x y z : S a), Seq x y -> Seq y z ->
Seq x z.

Add Parametric Relation a : (S a) Seq
 reflexivity proved by Seq_refl
 symmetry proved by Seq_sym
 transitivity proved by Seq_trans
 as S_Setoid.

Goal forall (a : A) (x y : S a), Seq x y -> Seq x y.
  intros a x y H.
  setoid_replace x with y.
  reflexivity.
  trivial.
Qed.
