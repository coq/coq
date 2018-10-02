Require Import Setoid.

Section Setoid_Bug.

Variable X:Type -> Type.
Variable Xeq : forall A, (X A) -> (X A) -> Prop.
Hypothesis Xst : forall A, Equivalence (Xeq A).

Variable map : forall A B, (A -> B) -> X A -> X B.

Arguments map [A B].

Goal forall A B (a b:X (B -> A)) (c:X A) (f:A -> B -> A), Xeq _ a b -> Xeq _ b (map f c) -> Xeq _ a (map f c).
intros A B a b c f Hab Hbc.
rewrite Hab.
assumption.
Qed.
