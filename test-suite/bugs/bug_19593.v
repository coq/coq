From Coq Require Import FinFun.
From Coq Require Import Classes.Equivalence.
Definition f_id {X: Type} (x0: X) := x0.
Lemma simpl_prop:
True /\ f_id (f_id (f_id True)).
Proof.
Fixpoint f_apply {X: Type} (x0: X) (f: X -> X) (n: nat) :=
match n with
| 0 => x0
| S n' => f_apply (f x0) f n' end.
assert (forall n (X: Prop), X -> f_apply X f_id n).
{ induction n.
  + simpl. intros. exact H.
  + intros. simpl. specialize (IHn (f_id X)).
    apply IHn. unfold f_id. exact H.  }
split.
+ exact I.
+ specialize (H 3 True). simpl in H.
  apply H. exact I.
Qed.
