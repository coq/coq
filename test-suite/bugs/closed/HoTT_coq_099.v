Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from 138 lines to 78 lines. *)
Set Implicit Arguments.
Generalizable All Variables.
Set Universe Polymorphism.
Delimit Scope object_scope with object.
Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Record Category (obj : Type) :=
  {
    Object :> _ := obj;
    Morphism : obj -> obj -> Type;

    Identity : forall x, Morphism x x;
    Compose : forall s d d', Morphism d d' -> Morphism s d -> Morphism s d'
  }.

Arguments Identity {obj%type} [!C%category] x%object : rename.
Arguments Compose {obj%type} [!C%category s%object d%object d'%object] m1%morphism m2%morphism : rename.
Bind Scope category_scope with Category.

Record Functor `(C : @Category objC) `(D : @Category objD)
  := { ObjectOf :> objC -> objD;
       MorphismOf : forall s d, C.(Morphism) s d -> D.(Morphism) (ObjectOf s) (ObjectOf d) }.

Record NaturalTransformation `(C : @Category objC) `(D : @Category objD) (F G : Functor C D)
  := { ComponentsOf :> forall c, D.(Morphism) (F c) (G c) }.

Definition ProductCategory `(C : @Category objC) `(D : @Category objD)
: @Category (objC * objD)%type
  := @Build_Category _
                     (fun s d => (C.(Morphism) (fst s) (fst d) * D.(Morphism) (snd s) (snd d))%type)
                     (fun o => (Identity (fst o), Identity (snd o)))
                     (fun s d d' m2 m1 => (Compose (fst m2) (fst m1), Compose (snd m2) (snd m1))).

Infix "*" := ProductCategory : category_scope.

Record IsomorphismOf `{C : @Category objC} {s d} (m : C.(Morphism) s d) :=
  { IsomorphismOf_Morphism :> C.(Morphism) s d := m;
    Inverse : C.(Morphism) d s }.

Record NaturalIsomorphism `(C : @Category objC) `(D : @Category objD) (F G : Functor C D)
  := { NaturalIsomorphism_Transformation :> NaturalTransformation F G;
       NaturalIsomorphism_Isomorphism : forall x : objC, IsomorphismOf (NaturalIsomorphism_Transformation x) }.

Section PreMonoidalCategory.
  Context `(C : @Category objC).
  Definition TriMonoidalProductL : Functor (C * C * C) C.
    admit.
  Defined.
  Definition TriMonoidalProductR : Functor (C * C * C) C.
    admit.
  Defined. (** Replacing [admit. Defined.] with [Admitted.] satisfies the constraints *)
  Variable Associator : NaturalIsomorphism TriMonoidalProductL TriMonoidalProductR.
  (* Toplevel input, characters 15-96:
Error: Unsatisfied constraints:
Coq.Init.Datatypes.28 <= Coq.Init.Datatypes.29
Top.168 <= Coq.Init.Datatypes.29
Top.168 <= Coq.Init.Datatypes.28
Top.169 <= Coq.Init.Datatypes.29
Top.169 <= Coq.Init.Datatypes.28
 (maybe a bugged tactic). *)
