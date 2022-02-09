(* cbn is able to refold mutual recursive calls *)

Fixpoint foo (n : nat) :=
  match n with
  | 0 => true
  | S n => g n
  end
with g (n : nat) : bool :=
  match n with
  | 0 => true
  | S n => foo n
  end.
Goal forall n, foo (S n) = g n.
  intros. cbn.
  match goal with
    |- g _ = g _ => reflexivity
  end.
Qed.

(* simpl nomatch *)

Definition thing n := match n with  0 => True | S n => False end.

Arguments thing _ / : simpl nomatch.

Goal forall x, thing x.
  intros. cbn.
  match goal with |- thing x => idtac end.
Abort.

Definition thing' n := n + n.

Arguments thing' !_ / : simpl nomatch.
Lemma bar n : thing' n = 0.
Proof.
  cbn.
  match goal with |- thing' _ = _ => idtac end.
  Arguments thing' _ / : simpl nomatch.
  cbn.
  match goal with |- _ + _ = _ => idtac end.
Abort.
