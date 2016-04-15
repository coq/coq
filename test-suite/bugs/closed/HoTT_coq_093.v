Unset Strict Universe Declaration.
(** It would be nice if we had more lax constraint checking of inductive types, and had variance annotations on their universes *)
Set Printing All.
Set Printing Implicit.
Set Printing Universes.
Set Universe Polymorphism.

Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a.
Arguments idpath {A a} , [A] a.

Notation "x = y" := (@paths _ x y) : type_scope.

Section lift.
  Let lift_type : Type.
  Proof.
    let U0 := constr:(Type) in
    let U1 := constr:(Type) in
    let unif := constr:(U0 : U1) in
    exact (U0 -> U1).
  Defined.

  Definition Lift (A : Type@{i}) : Type@{j} := A.
End lift.

Goal forall (A : Type@{i}) (x y : A), @paths@{i j} A x y -> @paths@{j k} A x y.
intros A x y p.
compute in *. destruct p. exact idpath.
Defined.
