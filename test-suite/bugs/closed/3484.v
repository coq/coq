Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 14259 lines to 305 lines, then from 237 lines to 120 lines, then from 100 lines to 30 lines *)
Set Primitive Projections.
Set Implicit Arguments.
Record sigT (A : Type) (P : A -> Type) := existT { projT1 : A ; projT2 : P projT1 }.
Notation "{ x : A & P }" := (@sigT A (fun x : A => P)) : type_scope.
Notation pr1 := (@projT1 _ _).
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "x = y" := (@paths _ x y) : type_scope.
Arguments idpath {A a} , [A] a.
Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y := match p with idpath => idpath end.
Goal forall (T : Type) (H :  { g : T & g = g }) (x : T), projT1 H = projT1 (existT (fun g : T => g = g) x idpath).
Proof.
  intros.
  let y := match goal with |- projT1 ?x = projT1 ?y => constr:(y) end in
  apply (@ap _ _ pr1 _ y).
  Undo.
  Unset Printing Notations.
  apply (ap pr1). 
  Undo.
  refine (ap pr1 _).
admit. 
Defined.

(* Toplevel input, characters 22-28:
Error:
In environment
T : Type
H : sigT T (fun g : T => paths g g)
x : T
Unable to unify "paths (@projT1 ?24 ?23 ?25) (@projT1 ?24 ?23 ?26)" with
 "paths (projT1 H) (projT1 {| projT1 := x; projT2 := idpath |})". *)
