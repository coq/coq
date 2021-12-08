Generalizable All Variables.

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

Module success.
  Axiom bar : nat -> Type -> Type.

  Definition foo (n : nat) (A : Type) : Type :=
    match n with
      | O => A
      | S n' => forall x y : A, bar n' (x = y)
    end.

  Definition foo_succ n A : foo (S n) A.
  Admitted.

  Goal forall n (X Y : Type) (y : X) (x : X), bar n (x = y).
  intros.
  apply (foo_succ _ _).
  Defined.
End success.

Module failure.
  Fixpoint bar (n : nat) (A : Type) : Type :=
    match n with
      | O => A
      | S n' => forall x y : A, bar n' (x = y)
    end.

  Definition foo_succ n A : bar (S n) A.
  Admitted.

  Goal forall n (X Y : Type) (y : X) (x : X), bar n (x = y).
  intros.
  apply foo_succ.
  (* Toplevel input, characters 22-34:
Error: In environment
n : nat
X : Type
Y : Type
y : X
x : X
Unable to unify
 "forall x0 y0 : ?16,
  (fix bar (n : nat) (A : Type) {struct n} : Type :=
     match n with
     | 0 => A
     | S n' => forall x y : A, bar n' (x = y)
     end) ?15 (x0 = y0)" with
 "(fix bar (n : nat) (A : Type) {struct n} : Type :=
     match n with
     | 0 => A
     | S n' => forall x y : A, bar n' (x = y)
     end) n (x = y)".
*)
  Defined.
End failure.
