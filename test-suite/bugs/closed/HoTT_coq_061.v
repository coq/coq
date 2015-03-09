Require Import TestSuite.admit.
(* There are some problems in materialize_evar with local definitions,
   as CO below; this is not completely sorted out yet, but at least
   it fails in a smooth way at the time of today [HH] *)

(* File reduced by coq-bug-finder from 9039 lines to 7786 lines, then
   from 7245 lines to 476 lines, then from 417 lines to 249 lines,
   then from 171 lines to 127 lines. *)

Set Implicit Arguments.
Set Universe Polymorphism.
Definition admit {T} : T.
Admitted.
Delimit Scope object_scope with object.
Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope functor_scope with functor.
Delimit Scope natural_transformation_scope with natural_transformation.
Reserved Infix "o" (at level 40, left associativity).
Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.
Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.
Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
  := match p with idpath => idpath end.

Record PreCategory :=
  {
    Object :> Type;
    Morphism : Object -> Object -> Type;

    Compose : forall s d d', Morphism d d' -> Morphism s d -> Morphism s d' where "f 'o' g" := (Compose f g)
  }.
Bind Scope category_scope with PreCategory.

Arguments Compose [!C%category s%object d%object d'%object] m1%morphism m2%morphism : rename.

Infix "o" := Compose : morphism_scope.
Local Open Scope morphism_scope.

Record Functor (C D : PreCategory) :=
  {
    ObjectOf :> C -> D;
    MorphismOf : forall s d, C.(Morphism) s d -> D.(Morphism) (ObjectOf s) (ObjectOf d);
    FCompositionOf : forall s d d' (m1 : C.(Morphism) s d) (m2: C.(Morphism) d d'),
                       MorphismOf _ _ (m2 o m1) = (MorphismOf _ _ m2) o (MorphismOf _ _ m1)
  }.

Bind Scope functor_scope with Functor.

Arguments MorphismOf [C%category] [D%category] F%functor [s%object d%object] m%morphism : rename, simpl nomatch.

Definition ComposeFunctors C D E
           (G : Functor D E) (F : Functor C D) : Functor C E
  := Build_Functor C E
                   (fun c => G (F c))
                   admit
                   admit.

Infix "o" := ComposeFunctors : functor_scope.

Record NaturalTransformation C D (F G : Functor C D) :=
  {
    ComponentsOf :> forall c, D.(Morphism) (F c) (G c);
    Commutes : forall s d (m : C.(Morphism) s d),
                 ComponentsOf d o F.(MorphismOf) m = G.(MorphismOf) m o ComponentsOf s
  }.

Generalizable All Variables.

Section NTComposeT.

  Variable C : PreCategory.
  Variable D : PreCategory.

  Variables F F' F'' : Functor C D.

  Variable T' : NaturalTransformation F' F''.
  Variable T : NaturalTransformation F F'.
  Let CO := fun c => T' c o T c.
  Definition NTComposeT_Commutes s d (m : Morphism C s d)
  : CO d o MorphismOf F m = MorphismOf F'' m o CO s.

    admit.
  Defined.
  Definition NTComposeT
  : NaturalTransformation F F''
    := Build_NaturalTransformation F F''
                                   (fun c => T' c o T c)
                                   NTComposeT_Commutes.
End NTComposeT.
Definition NTWhiskerR C D E (F F' : Functor D E) (T : NaturalTransformation F F')
           (G : Functor C D)
  := Build_NaturalTransformation (F o G) (F' o G)
                                 (fun c => T (G c))
                                 admit.
Global Class NTC_Composable A B (a : A) (b : B) (T : Type) (term : T) := {}.

Definition NTC_Composable_term `{@NTC_Composable A B a b T term} := term.
Notation "T 'o' U"
  := (@NTC_Composable_term _ _ T%natural_transformation U%natural_transformation _ _ _)
     : natural_transformation_scope.

Local Open Scope natural_transformation_scope.

Lemma NTWhiskerR_CompositionOf C D
      (F G H : Functor C D)
      (T : NaturalTransformation G H)
      (T' : NaturalTransformation F G) B (I : Functor B C)
: NTWhiskerR (NTComposeT T T') I = NTComposeT (NTWhiskerR T I) (NTWhiskerR T' I).

  admit.
Defined.
Definition FunctorCategory C D : PreCategory
  := @Build_PreCategory (Functor C D)
                        (NaturalTransformation (C := C) (D := D))
                        admit.

Notation "[ C , D ]" := (FunctorCategory C D) : category_scope.

Variable C : PreCategory.
Variable D : PreCategory.
Variable E : PreCategory.
Fail Definition NTWhiskerR_Functorial (G : [C, D]%category)
: [[D, E], [C, E]]%category
  := Build_Functor
       [C, D] [C, E]
       (fun F => F o G)
       (fun _ _ T => T o G)
       (fun _ _ _ _ _ => inverse (NTWhiskerR_CompositionOf _ _ _)).
(* Anomaly: Uncaught exception Not_found(_). Please report. *)
