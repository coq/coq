Require Import Ring.
Require Import ArithRing.

Ltac ring_simplify_neq :=
  match goal with
  | [ H: ?X <> ?Y |- _ ] => progress ring_simplify X Y in H
  end.

Lemma toto : forall x y, x*1 <> y*1 -> y*1 <> x*1 -> x<>y.
Proof.
  intros.
  ring_simplify_neq.
  ring_simplify_neq.
  (* make sure ring_simplify has simplified both hypotheses *)
  match goal with
  | [ H: context[_*1] |- _ ] => fail 1
  | _ => idtac
  end.
  auto.
Qed.
