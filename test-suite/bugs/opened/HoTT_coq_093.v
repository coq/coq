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

  Definition Lift : lift_type := fun A => A.
End lift.

Goal forall (A : Type) (x y : A), @paths A x y -> @paths (Lift A) x y.
intros A x y p.
compute in *.
Fail exact p. (* Toplevel input, characters 21-22:
Error:
In environment
A : Type (* Top.15 *)
x : A
y : A
p : @paths (* Top.15 *) A x y
The term "p" has type "@paths (* Top.15 *) A x y"
while it is expected to have type "@paths (* Top.18 *) A x y"
(Universe inconsistency: Cannot enforce Top.18 = Top.15 because Top.15
< Top.18)). *)
