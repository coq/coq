Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Record Category (obj : Type) := { Morphism : obj -> obj -> Type }.

Record Functor `(C : Category objC) `(D : Category objD) :=
  { ObjectOf :> objC -> objD;
    MorphismOf : forall s d, C.(Morphism) s d -> D.(Morphism) (ObjectOf s) (ObjectOf d) }.

Definition TypeCat : @Category Type := @Build_Category Type (fun s d => s -> d).
Definition SetCat : @Category Set := @Build_Category Set (fun s d => s -> d).

Definition FunctorToSet `(C : @Category objC) := Functor C SetCat.
Definition FunctorToType `(C : @Category objC) := Functor C TypeCat.

(* Removing the following line, as well as the [Definition] and [Identity Coercion] immediately following it, makes the file go through *)
Identity Coercion FunctorToType_Id : FunctorToType >-> Functor.

Set Printing Universes.
Definition FunctorTo_Set2Type `(C : @Category objC) (F : FunctorToSet C)
: FunctorToType C.
  refine (@Build_Functor _ C _ TypeCat
                         (fun x => F.(ObjectOf) x)
                         (fun s d m => F.(MorphismOf) _ _ m)).
(* ??? Toplevel input, characters 8-148:
Error:
In environment
objC : Type{Top.100}
C : Category@{Top.100 Top.101} objC
F : FunctorToSet@{Top.100 Top.101 Top.99} C
The term
 "{|
  ObjectOf := fun x : objC => F x;
  MorphismOf := fun (s d : objC) (m : Morphism@{Top.100 Top.101} C s d) =>
                MorphismOf@{Top.100 Top.101 Top.99 Set} F s d m |}" has type
 "Functor@{Top.104 Top.105 Top.106 Top.107} C TypeCat@{Top.108 Top.109
    Top.110}" while it is expected to have type
 "FunctorToType@{Top.100 Top.101 Top.102 Top.103} C"
(Universe inconsistency: Cannot enforce Set = Top.103)).
 *)
Defined. (* Toplevel input, characters 0-8:
Error:
The term
 "fun (objC : Type) (C : Category objC) (F : FunctorToSet C) =>
  {|
  ObjectOf := fun x : objC => F x;
  MorphismOf := fun (s d : objC) (m : Morphism C s d) => MorphismOf F s d m |}"
has type
 "forall (objC : Type) (C : Category objC),
  FunctorToSet C -> Functor C TypeCat" while it is expected to have type
 "forall (objC : Type) (C : Category objC), FunctorToSet C -> FunctorToType C".
 *)

Coercion FunctorTo_Set2Type : FunctorToSet >-> FunctorToType.

Record GrothendieckPair `(C : @Category objC) (F : Functor C TypeCat) :=
  { GrothendieckC : objC;
    GrothendieckX : F GrothendieckC }.

Record SetGrothendieckPair `(C : @Category objC) (F' : Functor C SetCat) :=
  { SetGrothendieckC : objC;
    SetGrothendieckX : F' SetGrothendieckC }.

Section SetGrothendieckCoercion.
  Context `(C : @Category objC).
  Variable F : Functor C SetCat.
  Let F' := (F : FunctorToSet _) : FunctorToType _. (* The command has indeed failed with message:
=> Anomaly: apply_coercion_args: mismatch between arguments and coercion.
Please report. *)

  Set Printing Universes.
  Definition SetGrothendieck2Grothendieck (G : SetGrothendieckPair F) : GrothendieckPair F'
    := {| GrothendieckC := G.(SetGrothendieckC); GrothendieckX := G.(SetGrothendieckX) : F' _ |}.
  (* Toplevel input, characters 0-187:
Error: Illegal application:
The term "ObjectOf (* Top.8375 Top.8376 Top.8379 Set *)" of type
 "forall (objC : Type (* Top.8375 *))
    (C : Category (* Top.8375 Top.8376 *) objC) (objD : Type (* Top.8379 *))
    (D : Category (* Top.8379 Set *) objD),
  Functor (* Top.8375 Top.8376 Top.8379 Set *) C D -> objC -> objD"
cannot be applied to the terms
 "objC" : "Type (* Top.8375 *)"
 "C" : "Category (* Top.8375 Top.8376 *) objC"
 "Type (* Set *)" : "Type (* Set+1 *)"
 "TypeCat (* Top.8379 Set *)" : "Category (* Top.8379 Set *) Set"
 "F'" : "FunctorToType (* Top.8375 Top.8376 Top.8379 Set *) C"
 "SetGrothendieckC (* Top.8375 Top.8376 Top.8379 *) G" : "objC"
The 5th term has type "FunctorToType (* Top.8375 Top.8376 Top.8379 Set *) C"
which should be coercible to
 "Functor (* Top.8375 Top.8376 Top.8379 Set *) C TypeCat (* Top.8379 Set *)".
 *)
End SetGrothendieckCoercion.
