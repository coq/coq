Global Set Primitive Projections.
Set Implicit Arguments.
Record sigT {A} (P : A -> Type) := existT { projT1 : A ; projT2 : P projT1 }.
Record PreCategory := { object :> Type ; morphism : object -> object -> Type }.
Variable A : PreCategory.
Variable Pobj : A -> Type.
Local Notation obj := (sigT Pobj).
Variable Pmor : forall s d : obj, morphism A (projT1 s) (projT1 d) -> Type.
Class Foo (x : Type) := { _ : forall y, y }.
Local Instance ishset_pmor {s d m} : Foo (Pmor s d m).
Proof.
SearchAbout ((forall _ _, _) -> Foo _).
Abort.
