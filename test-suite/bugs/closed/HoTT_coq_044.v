Require Import Classes.RelationClasses List Setoid.

Definition eqT (T : Type) := @eq T.

Set Universe Polymorphism.

Definition RowType := list Type.


Inductive Row : RowType -> Type :=
| RNil : Row nil
| RCons : forall T Ts, T -> Row Ts -> Row (T :: Ts).

Inductive RowTypeDecidable (P : forall T, relation T) `(H : forall T, Equivalence (P T))
: RowType -> Type :=
| RTDecNil : RowTypeDecidable P H nil
| RTDecCons : forall T Ts, (forall t0 t1 : T,
                              {P T t0 t1} + {~P T t0 t1})
                           -> RowTypeDecidable P H Ts
                           -> RowTypeDecidable P H (T :: Ts).


Set Printing Universes.

Fixpoint Row_eq (Ts : RowType)
: RowTypeDecidable (@eqT) _ Ts -> forall r1 r2 : Row Ts, {@eq (Row Ts) r1 r2} + {r1 <> r2}.
(* Toplevel input, characters 81-87:
Error:
In environment
Ts : RowType (* Top.53 Coq.Init.Logic.8 *)
r1 : Row (* Top.54 Top.55 *) Ts
r2 : Row (* Top.56 Top.57 *) Ts
The term "Row (* Coq.Init.Logic.8 Top.59 *) Ts" has type
 "Type (* max(Top.58+1, Top.59) *)" while it is expected to have type
 "Type (* Coq.Init.Logic.8 *)" (Universe inconsistency). *)
