Set Universe Polymorphism.
Module A.
  Inductive paths A (x : A) : A -> Type := idpath : paths A x x.

  Notation "x = y" := (paths _ x y).

  Inductive IsTrunc : nat -> Type -> Type :=
  | BuildContr : forall A (center : A) (contr : forall y, center = y), IsTrunc 0 A
  | trunc_S : forall A n, (forall x y : A, IsTrunc n (x = y)) -> IsTrunc (S n) A.

  Fail Existing Class IsTrunc.
  (* Anomaly: Mismatched instance and context when building universe substitution.
Please report. *)
End A.

Module B.
  Fixpoint IsTrunc (n : nat) (A : Type) : Type :=
    match n with
      | O => True
      | S _ => False
    end.

  Fail Existing Class IsTrunc.
  (* Anomaly: Mismatched instance and context when building universe substitution.
Please report. *)
End B.
