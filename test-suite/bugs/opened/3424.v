Set Universe Polymorphism.
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "x = y" := (@paths _ x y) : type_scope.
Class Contr_internal (A : Type) := BuildContr { center : A ; contr : (forall y : A, center = y) }.
Inductive trunc_index : Type := minus_two | trunc_S (x : trunc_index).
Bind Scope trunc_scope with trunc_index.
Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
  match n with
    | minus_two => Contr_internal A
    | trunc_S n' => forall (x y : A), IsTrunc_internal n' (x = y)
  end.
Notation minus_one:=(trunc_S minus_two).
Notation "0" := (trunc_S minus_one) : trunc_scope.
Class IsTrunc (n : trunc_index) (A : Type) : Type := Trunc_is_trunc : IsTrunc_internal n A.
Notation IsHProp := (IsTrunc minus_one).
Notation IsHSet := (IsTrunc 0).
Goal forall (A : Type) (a b : A) (H' : IsHSet A), { x : Type & IsHProp x }.
Proof.
intros.
eexists.
(* exact (H' a b). *)
(* Undo. *)
Fail apply (H' a b).
exact (H' a b).
Qed.
