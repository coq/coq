Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Record sigT {A : Type} (P : A -> Type) := existT { projT1 : A; projT2 : P projT1 }.
Arguments existT {A} _ _ _.
Definition unpack_sigma' {A} {P : A -> Type} (Q : sigT P -> Type) (u : sigT P) :
  Q (existT _ (projT1 u) (projT2 u)) -> Q u
  :=
  fun H =>
    (let (x,p) as u return (Q (existT _ (projT1 u) (projT2 u)) -> Q u) := u in fun x : Q (existT _ _ p) => x) H. (* success *)
Definition unpack_sigma {A} {P : A -> Type} (Q : sigT P -> Type) (u : sigT P) :
  Q (existT _ (projT1 u) (projT2 u)) -> Q u
  :=
  fun H =>
    (let (x,p) as u return (Q (existT _ (projT1 u) (projT2 u)) -> Q u) := u in fun x => x) H.
(* Toplevel input, characters 219-229:
Error:
In environment
A : Type
P : A -> Type
Q : sigT P -> Type
u : sigT P
H : Q {| projT1 := projT1 u; projT2 := projT2 u |}
x : A
p : P x
The term
 "fun
    x : Q
          {|
          projT1 := projT1 {| projT1 := x; projT2 := p |};
          projT2 := projT2 {| projT1 := x; projT2 := p |} |} => x" has type
 "Q
    {|
    projT1 := projT1 {| projT1 := x; projT2 := p |};
    projT2 := projT2 {| projT1 := x; projT2 := p |} |} ->
... "
*)
