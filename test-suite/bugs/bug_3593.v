Set Universe Polymorphism.
Set Printing All.
Set Implicit Arguments.

Module NoCumul.

#[universes(cumulative=no)] Record prod A B := pair { fst : A ; snd : B }.
Goal forall x : prod Set Set, let f := @fst _ in f _ x = @fst _ _ x.
simpl; intros.
  constr_eq (@fst Set Set x) (fst (A := Set) (B := Set) x).
  Fail progress change (@fst Set Set x) with (fst (A := Set) (B := Set) x).
  reflexivity.
Qed.

End NoCumul.

Set Universe Polymorphism.
Set Printing All.
Set Implicit Arguments.

Module Cumul.

Record prod A B := pair { fst : A ; snd : B }.
Goal forall x : prod Set Set, let f := @fst _ in f _ x = @fst _ _ x.
simpl; intros.
  constr_eq (@fst Set Set x) (fst (A := Set) (B := Set) x).
  Fail progress change (@fst Set Set x) with (fst (A := Set) (B := Set) x).
  reflexivity.
Qed.

End Cumul.
