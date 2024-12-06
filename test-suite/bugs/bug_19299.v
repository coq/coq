Require Import ListDef.

Class MBind (M : Type -> Type) :=
  mbind : forall {A B}, (A -> M B) -> M A -> M B.
#[global] Instance list_bind : MBind list.
exact (fun A B f =>
  fix go (l : list A) :=
    match l with nil => nil | cons x l => f x ++ go l end%list).
Defined.

Polymorphic Record dyn := Dyn { type : Type; elem : type }.

Definition fails : list dyn := (Dyn _ (@Datatypes.app)) :: nil.
