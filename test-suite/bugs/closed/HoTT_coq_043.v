Require Import Classes.RelationClasses List Setoid.

Definition RowType := list Type.

Inductive RowTypeDecidable (P : forall T, relation T) `(forall T, Equivalence (P T))
: RowType -> Type :=
| RTDecNil : RowTypeDecidable P _ nil
| RTDecCons : forall T Ts, (forall t0 t1 : T,
                              {P T t0 t1} + {~P T t0 t1})
                           -> RowTypeDecidable P _ Ts
                           -> RowTypeDecidable P _ (T :: Ts).
(* Toplevel input, characters 15-378:
Error:
Last occurrence of "RowTypeDecidable" must have "H" as 2nd argument in
 "RowTypeDecidable P (fun T : Type => H T) nil". *)
