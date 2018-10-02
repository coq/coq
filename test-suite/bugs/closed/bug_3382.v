Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from 9039 lines to 7786 lines, then from 7245 lines to 476 lines, then from 417 lines to 249 lines, then from 171 lines to 127 lines, then from 139 lines to 114 lines, then from 93 lines to 77 lines *)

Set Implicit Arguments.
Definition admit {T} : T.
Admitted.
Delimit Scope object_scope with object.
Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope functor_scope with functor.
Reserved Infix "o" (at level 40, left associativity).
Record PreCategory :=
  { Object :> Type;
    Morphism : Object -> Object -> Type;
    Compose : forall s d d', Morphism d d' -> Morphism s d -> Morphism s d' where "f 'o' g" := (Compose f g) }.
Bind Scope category_scope with PreCategory.
Infix "o" := (@Compose _ _ _ _) : morphism_scope.
Local Open Scope morphism_scope.
Record Functor (C D : PreCategory) :=
  { ObjectOf :> C -> D;
    MorphismOf : forall s d, C.(Morphism) s d -> D.(Morphism) (ObjectOf s) (ObjectOf d);
    FCompositionOf : forall s d d' (m1 : C.(Morphism) s d) (m2: C.(Morphism) d d'),
                       MorphismOf _ _ (m2 o m1) = (MorphismOf _ _ m2) o (MorphismOf _ _ m1) }.
Bind Scope functor_scope with Functor.
Arguments MorphismOf [C%category] [D%category] F%functor [s%object d%object] m%morphism : rename, simpl nomatch.
Definition ComposeFunctors C D E
           (G : Functor D E) (F : Functor C D) : Functor C E
  := Build_Functor C E (fun c => G (F c)) admit admit.
Infix "o" := ComposeFunctors : functor_scope.
Record NaturalTransformation C D (F G : Functor C D) :=
  { ComponentsOf :> forall c, D.(Morphism) (F c) (G c);
    Commutes : forall s d (m : C.(Morphism) s d),
                 ComponentsOf d o F.(MorphismOf) m = G.(MorphismOf) m o ComponentsOf s }.
Definition NTComposeT C D (F F' F'' : Functor C D)
           (T' : NaturalTransformation F' F'')
           (T : NaturalTransformation F F')
           (CO := fun c => T' c o T c)
: NaturalTransformation F F''.
  exact (Build_NaturalTransformation F F''
                                     (fun c => T' c o T c)
                                     (admit : forall s d (m : Morphism C s d), CO d o MorphismOf F m = MorphismOf F'' m o CO s)).
Defined.
Definition NTWhiskerR C D E (F F' : Functor D E) (T : NaturalTransformation F F')
           (G : Functor C D)
  := Build_NaturalTransformation (F o G) (F' o G) (fun c => T (G c)) admit.
Axiom NTWhiskerR_CompositionOf
: forall C D
         (F G H : Functor C D)
         (T : NaturalTransformation G H)
         (T' : NaturalTransformation F G) B (I : Functor B C),
    NTComposeT (NTWhiskerR T I) (NTWhiskerR T' I) = NTWhiskerR (NTComposeT T T') I.
Definition FunctorCategory C D : PreCategory
  := @Build_PreCategory (Functor C D)
                        (NaturalTransformation (C := C) (D := D))
                        admit.
Notation "[ C , D ]" := (FunctorCategory C D) : category_scope.
Class silly {T} := term : T.
Timeout 1 Fail Definition NTWhiskerR_Functorial (C D E : PreCategory) (G : [C, D]%category)
: [[D, E], [C, E]]%category
  := Build_Functor
       [C, D] [C, E]
       (fun F => _ : silly)
       (fun _ _ T => _ : silly)
       (fun _ _ _ _ _ => NTWhiskerR_CompositionOf _ _ _).
