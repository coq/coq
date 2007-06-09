Require Export JMeq.

Notation " [ x : X ] = [ y : Y ] " := (@JMeq X x Y y) (at level 0, X at next level, Y at next level).

Ltac on_JMeq tac := 
  match goal with
    | [ H : @JMeq ?x ?X ?y ?Y |- _ ] => tac H
  end.

Ltac simpl_one_JMeq :=
  on_JMeq 
  ltac:(fun H => let H' := fresh "H" in 
    assert (H' := JMeq_eq H) ; clear H ; rename H' into H).

Ltac simpl_one_dep_JMeq :=
  on_JMeq
  ltac:(fun H => let H' := fresh "H" in 
    assert (H' := JMeq_eq H)).

Ltac simpl_JMeq := repeat simpl_one_JMeq.




