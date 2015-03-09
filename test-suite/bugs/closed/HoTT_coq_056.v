Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from 10455 lines to 8350 lines, then from 7790 lines to 710 lines, then from 7790 lines to 710 lines, then from 566 lines to 340 lines, then from 191 lines to 171 lines, then from 191 lines to 171 lines. *)

Set Implicit Arguments.
Set Universe Polymorphism.
Definition admit {T} : T.
Admitted.
Reserved Notation "x ≅ y" (at level 70, no associativity).
Reserved Notation "i ^op" (at level 3).
Reserved Infix "∘" (at level 40, left associativity).
Reserved Notation "F ⟨ x ⟩" (at level 10, no associativity, x at level 10).
Reserved Notation "F ⟨ x , y ⟩" (at level 10, no associativity, x at level 10, y at level 10).
Reserved Notation "F ⟨ ─ ⟩" (at level 10, no associativity).
Reserved Notation "F ⟨ x , ─ ⟩" (at level 10, no associativity, x at level 10).
Reserved Notation "F ⟨ ─ , y ⟩" (at level 10, no associativity, y at level 10).
Delimit Scope object_scope with object.
Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope functor_scope with functor.
Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.
Arguments idpath {A a} , [A] a.
Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.
Delimit Scope path_scope with path.
Local Open Scope path_scope.

Record PreCategory :=
  Build_PreCategory' {
      Object :> Type;
      Morphism : Object -> Object -> Type
    }.

Bind Scope category_scope with PreCategory.

Definition Build_PreCategory
           Object Morphism
  := @Build_PreCategory' Object
                         Morphism.

Record Functor (C D : PreCategory) :=
  {
    ObjectOf :> C -> D;
    MorphismOf : forall s d, C.(Morphism) s d -> D.(Morphism) (ObjectOf s) (ObjectOf d)
  }.
Arguments MorphismOf [C%category] [D%category] F%functor [s%object d%object] m%morphism : rename, simpl nomatch.
Class Isomorphic {C : PreCategory} (s d : C) := {}.
Definition ComposeFunctors C D E (G : Functor D E) (F : Functor C D) : Functor C E
  := Build_Functor C E
                   (fun c => G (F c))
                   (fun _ _ m => G.(MorphismOf) (F.(MorphismOf) m)).

Infix "∘" := ComposeFunctors : functor_scope.

Definition IdentityFunctor C : Functor C C
  := Build_Functor C C
                   (fun x => x)
                   (fun _ _ x => x).

Notation "─" := (IdentityFunctor _) : functor_scope.
Record NaturalTransformation C D (F G : Functor C D) :=
  Build_NaturalTransformation' { }.

Definition OppositeCategory (C : PreCategory) : PreCategory
  := @Build_PreCategory' C
                         (fun s d => Morphism C d s).

Notation "C ^op" := (OppositeCategory C) : category_scope.

Definition ProductCategory (C D : PreCategory) : PreCategory
  := @Build_PreCategory (C * D)%type
                        (fun s d => (C.(Morphism) (fst s) (fst d) * D.(Morphism) (snd s) (snd d))%type).

Infix "*" := ProductCategory : category_scope.

Definition OppositeFunctor C D (F : Functor C D) : Functor (C ^op) (D ^op)
  := Build_Functor (C ^op) (D ^op)
                   (ObjectOf F)
                   (fun s d => MorphismOf F (s := d) (d := s)).
Notation "F ^op" := (OppositeFunctor F) : functor_scope.

Definition FunctorProduct' C D C' D' (F : Functor C D) (F' : Functor C' D') : Functor (C * C') (D * D')
  := admit.

Global Class FunctorApplicationInterpretable
       {C D} (F : Functor C D)
       {argsT : Type} (args : argsT)
       {T : Type} (rtn : T)
  := {}.
Definition FunctorApplicationOf {C D} F {argsT} args {T} {rtn}
           `{@FunctorApplicationInterpretable C D F argsT args T rtn}
  := rtn.

Global Arguments FunctorApplicationOf / {C} {D} F {argsT} args {T} {rtn} {_}.

Global Instance FunctorApplicationDash C D (F : Functor C D)
: FunctorApplicationInterpretable F (IdentityFunctor C) F | 0.
Global Instance FunctorApplicationFunctorFunctor' A B C C' D (F : Functor (A * B) D) (G : Functor C A) (H : Functor C' B)
: FunctorApplicationInterpretable F (G, H) (F ∘ (FunctorProduct' G H))%functor | 100.

Notation "F ⟨ x ⟩" := (FunctorApplicationOf F%functor x%functor) : functor_scope.

Notation "F ⟨ x , y ⟩" := (FunctorApplicationOf F%functor (x%functor , y%functor)) : functor_scope.

Notation "F ⟨ ─ ⟩" := (F ⟨ ( ─ ) ⟩)%functor : functor_scope.

Notation "F ⟨ x , ─ ⟩" := (F ⟨ x , ( ─ ) ⟩)%functor : functor_scope.

Notation "F ⟨ ─ , y ⟩" := (F ⟨ ( ─ ) , y ⟩)%functor : functor_scope.

Definition FunctorCategory (C D : PreCategory) : PreCategory
  := @Build_PreCategory (Functor C D)
                        (NaturalTransformation (C := C) (D := D)).

Notation "[ C , D ]" := (FunctorCategory C D) : category_scope.

Definition SetCat : PreCategory := @Build_PreCategory Type (fun x y => x -> y).

Definition HomFunctor C : Functor (C^op * C) SetCat.
admit.
Defined.
Definition NaturalIsomorphism (C D : PreCategory) F G := @Isomorphic [C, D] F G.
Infix "≅" := NaturalIsomorphism : natural_transformation_scope.

Local Open Scope functor_scope.
Local Open Scope natural_transformation_scope.

Section Adjunction.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Variable F : Functor C D.
  Variable G : Functor D C.
  Let Adjunction_Type := Eval simpl in HomFunctor D ⟨ F^op ⟨ ─ ⟩ , ─ ⟩ ≅ HomFunctor C ⟨ ─ , G ⟨ ─ ⟩ ⟩.
  Record Adjunction := { AMateOf : Adjunction_Type }.
End Adjunction.

Section AdjunctionEquivalences.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Variable F : Functor C D.
  Variable G : Functor D C.
  Variable A : Adjunction F G.
  Set Printing All.
  Definition foo := @AMateOf C D F G A.
(* File "./HoTT_coq_56.v", line 145, characters 37-38:
Error:
In environment
C : PreCategory
D : PreCategory
F : Functor C D
G : Functor D C
A : @Adjunction C D F G
The term "A" has type "@Adjunction C D F G" while it is expected to have type
 "@Adjunction C D F G". *)
End AdjunctionEquivalences.
