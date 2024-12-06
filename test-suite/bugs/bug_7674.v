Definition foo (n : option nat) : nat := 0.
Arguments foo !_ /.

Goal forall n, foo (Some n) = 1.
  intros.
  progress cbn.
Abort.

Goal forall n, foo n = 1.
  intros.
  Fail progress cbn.
Abort.

Require Import TestSuite.bool.

Definition do_something (p q : bool) (a b : nat) : option nat :=
  if Bool.eqb p q then Some a else Some b.
Arguments do_something !_ !_ _ _ /.

Lemma test a b :
  exists x, do_something false true a b = x.
Proof.
  intros. eexists.

  progress cbn [do_something].
  match goal with |- (if Bool.eqb false true then Some a else Some b) = _ => idtac end.

  progress cbn [Bool.eqb].
  reflexivity.
Qed.
