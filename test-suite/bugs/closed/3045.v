
Set Asymmetric Patterns.
Generalizable All Variables.
Set Implicit Arguments.
Set Universe Polymorphism.

Record SpecializedCategory (obj : Type) :=
  {
    Object :> _ := obj;
    Morphism : obj -> obj -> Type;

    Compose : forall s d d', Morphism d d' -> Morphism s d -> Morphism s d'
  }.

Arguments Compose {obj} [C s d d'] _ _ : rename.

Inductive ReifiedMorphism : forall objC (C : SpecializedCategory objC), C -> C -> Type :=
| ReifiedComposedMorphism : forall objC C s d d', ReifiedMorphism C d d' -> ReifiedMorphism C s d -> @ReifiedMorphism objC C s d'.

Fixpoint ReifiedMorphismDenote objC C s d (m : @ReifiedMorphism objC C s d) : Morphism C s d :=
  match m in @ReifiedMorphism objC C s d return Morphism C s d with
    | ReifiedComposedMorphism _ _ _ _ _ m1 m2 => Compose (@ReifiedMorphismDenote _ _ _ _ m1)
                                                         (@ReifiedMorphismDenote _ _ _ _ m2)
  end.

Fixpoint ReifiedMorphismSimplifyWithProof objC C s d (m : @ReifiedMorphism objC C s d)
: { m' : ReifiedMorphism C s d | ReifiedMorphismDenote m = ReifiedMorphismDenote m' }.
refine match m with
         | ReifiedComposedMorphism _ _ s0 d0 d0' m1 m2 => _
       end; clear m.
(* This fails with an error rather than an anomaly, but morally 
   it should work, if destruct were able to do the good generalization
   in advance, before doing the "intros []". *)
Fail destruct (@ReifiedMorphismSimplifyWithProof T s1 d0 d0' m1) as [ [] ? ].
