Require Import TestSuite.admit.
Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Polymorphic Record Category (obj : Type) :=
  Build_Category {
      Object :> _ := obj;
      Morphism : obj -> obj -> Type;

      Compose : forall s d d', Morphism d d' -> Morphism s d -> Morphism s d'
    }.

Polymorphic Record Functor objC (C : Category objC) objD (D : Category objD) :=
  { ObjectOf :> objC -> objD }.

Polymorphic Record NaturalTransformation objC C objD D (F G : Functor (objC := objC) C (objD := objD) D) :=
  { ComponentsOf' :> forall c, D.(Morphism) (F.(ObjectOf) c) (G.(ObjectOf) c);
    Commutes' : forall s d (m : C.(Morphism) s d), ComponentsOf' s = ComponentsOf' s }.

Ltac present_obj from to :=
  match goal with
           | [ _ : context[from ?obj ?C] |- _ ] => progress change (from obj C) with (to obj C) in *
           | [ |- context[from ?obj ?C] ] => progress change (from obj C) with (to obj C) in *
         end.

Section NaturalTransformationComposition.
  Set Universe Polymorphism.
  Context `(C : @Category objC).
  Context `(D : @Category objD).
  Context `(E : @Category objE).
  Variables F F' F'' : Functor C D.
  Unset Universe Polymorphism.

  Polymorphic Definition NTComposeT (T' : NaturalTransformation F' F'') (T : NaturalTransformation F F') :
    NaturalTransformation F F''.
    exists (fun c => Compose _ _ _ _ (T' c) (T c)).
    repeat progress present_obj @Morphism @Morphism. (* removing this line makes the error go away *)
    intros. (* removing this line makes the error go away *)
    admit.
  Defined.
End NaturalTransformationComposition.


Polymorphic Definition FunctorCategory objC (C : Category objC) objD (D : Category objD) :
  @Category (Functor C D)
  := @Build_Category (Functor C D)
                     (NaturalTransformation (C := C) (D := D))
                     (NTComposeT (C := C) (D := D)).

Polymorphic Definition Cat0 : Category Empty_set
  := @Build_Category Empty_set
                     (@eq _)
                     (fun x => match x return _ with end).

Polymorphic Definition FunctorFrom0 objC (C : Category objC) : Functor Cat0 C
  := Build_Functor Cat0 C (fun x => match x with end).

Section Law0.
  Polymorphic Variable objC : Type.
  Polymorphic Variable C : Category objC.

  Set Printing All.
  Set Printing Universes.
  Set Printing Existential Instances.

  Polymorphic Definition ExponentialLaw0Functor_Inverse_ObjectOf' : Object (@FunctorCategory Empty_set Cat0 objC C).
  (* In environment
objC : Type (* Top.154 *)
C : Category (* Top.155 Top.154 *) objC
The term "objC" has type "Type (* Top.154 *)"
while it is expected to have type "Type (* Top.184 *)"
(Universe inconsistency: Cannot enforce Top.154 <= Set)). *)
  Admitted.

  Polymorphic Definition ExponentialLaw0Functor_Inverse_ObjectOf : Object (FunctorCategory Cat0 C).
    hnf.
    refine (@FunctorFrom0 _ _).

    (* Toplevel input, characters 23-40:
Error:
In environment
objC : Type (* Top.61069 *)
C : Category (* Top.61069 Top.61071 *) objC
The term
 "@FunctorFrom0 (* Top.61077 Top.61078 *) ?69 (* [objC, C] *)
    ?70 (* [objC, C] *)" has type
 "@Functor (* Set Prop Top.61077 Top.61078 *) Empty_set Cat0
    ?69 (* [objC, C] *) ?70 (* [objC, C] *)"
 while it is expected to have type
 "@Functor (* Set Prop Set Prop *) Empty_set Cat0 objC C".
*)
  Defined.
End Law0.
