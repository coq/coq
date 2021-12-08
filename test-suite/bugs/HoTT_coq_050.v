Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.
Set Printing Universes.

Set Printing All.

Record PreCategory :=
  {
    Object :> Type;
    Morphism : Object -> Object -> Type
  }.

Inductive paths A (x : A) : A -> Type := idpath : @paths A x x.
Inductive Unit : Prop := tt. (* Changing this to [Set] fixes things *)
Inductive Bool : Set := true | false.

Definition DiscreteCategory X : PreCategory
  := @Build_PreCategory X
                        (@paths X).

Definition IndiscreteCategory X : PreCategory
  := @Build_PreCategory X
                        (fun _ _ => Unit).

Check (IndiscreteCategory Unit).
Check (DiscreteCategory Bool).
Definition NatCategory (n : nat) :=
  match n with
    | 0 => IndiscreteCategory Unit
    | _ => DiscreteCategory Bool
  end. (* Error: Universe inconsistency (cannot enforce Set <= Prop). *)
