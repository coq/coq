Tactic Notation "myunfold" reference(x) := unfold x.
Notation idnat := (@id nat).
Goal let n := 0 in idnat n = 0.
Proof.
  intro n.
  myunfold idnat.
  myunfold n.
Abort.
