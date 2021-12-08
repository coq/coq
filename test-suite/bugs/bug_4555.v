Definition prod_map {A A' B B'} (f : A -> A') (g : B -> B')
           (p : A * B) : A' * B'
  := (f (fst p), g (snd p)).
Arguments prod_map {_ _ _ _} _ _ !_ /.

Lemma test1 {A A' B B'} (f : A -> A') (g : B -> B') x y :
  prod_map f g (x,y) = (f x, g y).
Proof.
  Succeed progress simpl; match goal with |- ?x = ?x => idtac end. (* LHS becomes (f x, g y) *)

  Succeed progress cbn; match goal with |- ?x = ?x => idtac end. (* LHS is not simplified *)
Admitted.


Axiom n : nat.
Arguments Nat.add _ !_.

Goal n + S n = 0.
  Fail progress cbn.
Abort.

Goal S n + S n = 0.
  progress cbn.
  match goal with |- S (n + S n) = 0 => idtac end.
Abort.

Goal S n + n = 0.
  Fail progress cbn.
Abort.
