
Class Zero (A : Type) := zero : A.
Notation "0" := zero.
Class One (A : Type) := one : A.
Notation "1" := one.
Class Addition (A : Type) := addition : A -> A -> A.
Notation "_+_" := addition.
Notation "x + y" := (addition x y).
Class Multiplication {A B : Type} := multiplication : A -> B -> B.
Notation "_*_" := multiplication.
Notation "x * y" := (multiplication x y).
Class Subtraction (A : Type) := subtraction : A -> A -> A.
Notation "_-_" := subtraction.
Notation "x - y" := (subtraction x y).
Class Opposite (A : Type) := opposite : A -> A.
Notation "-_" := opposite.
Notation "- x" := (opposite(x)).
Class Equality {A : Type}:= equality : A -> A -> Prop.
Notation "_==_" := equality.
Notation "x == y" := (equality x y) (at level 70, no associativity).
Class Bracket (A B: Type):= bracket : A -> B.
Notation "[ x ]" := (bracket(x)).
Class Power {A B: Type} := power : A -> B -> A.
Notation "x ^ y" := (power x y).


Notation "\/ x y z ,  P" := (forall x y z, P)
   (at level 200, x ident, y ident, z ident).
Notation "\/ x y ,  P" := (forall x y, P)
   (at level 200, x ident, y ident).
Notation "\/ x , P" := (forall x, P)(at level 200, x ident).

Notation "\/ x y z : T ,  P" := (forall x y z : T, P)
   (at level 200, x ident, y ident, z ident).
Notation "\/ x y  : T ,  P" := (forall x y : T, P)
   (at level 200, x ident, y ident).
Notation "\/ x  : T , P" := (forall x : T, P)(at level 200, x ident).

Notation "\ x y z , P" := (fun x y z => P)
   (at level 200, x ident, y ident, z ident).
Notation "\ x y ,  P" := (fun x y => P)
   (at level 200, x ident, y ident).
Notation "\ x , P" := (fun x => P)(at level 200, x ident).

Notation "\ x y z : T , P" := (fun x y z : T => P)
   (at level 200, x ident, y ident, z ident).
Notation "\ x y : T ,  P" := (fun x y : T => P)
   (at level 200, x ident, y ident).
Notation "\ x : T , P" := (fun x : T => P)(at level 200, x ident).
