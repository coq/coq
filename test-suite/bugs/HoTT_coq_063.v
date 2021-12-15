Set Universe Polymorphism.
Module A.
  Inductive paths A (x : A) : A -> Type := idpath : paths A x x.

  Notation "x = y" := (paths _ x y).

  Inductive IsTrunc : nat -> Type -> Type :=
  | BuildContr : forall A (center : A) (contr : forall y, center = y), IsTrunc 0 A
  | trunc_S : forall A n, (forall x y : A, IsTrunc n (x = y)) -> IsTrunc (S n) A.

  Existing Class IsTrunc.


  Instance is_trunc_unit : IsTrunc 0 unit.
  Proof. apply BuildContr with (center:=tt). now intros []. Defined.

  Check (_ : IsTrunc 0 unit).
End A.

Module B.
  Fixpoint IsTrunc (n : nat) (A : Type) : Type :=
    match n with
      | O => True
      | S _ => False
    end.

  Existing Class IsTrunc.

  Instance is_trunc_unit : IsTrunc 0 unit.
  Proof. exact I. Defined.

  Check (_ : IsTrunc 0 unit).
  Fail Definition foo := (_ : IsTrunc 1 unit).
End B.
