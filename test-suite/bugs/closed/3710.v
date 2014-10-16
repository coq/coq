(* File reduced by coq-bug-finder from original input, then from 13477 lines to 1457 lines, then from 1553 lines to 1586 lines, then \
from 1574 lines to 823 lines, then from 837 lines to 802 lines, then from 793 lines to 657 lines, then from 661 lines to 233 lines, t\
hen from 142 lines to 65 lines *)
(* coqc version trunk (October 2014) compiled on Oct 8 2014 13:38:17 with OCaml 4.01.0
   coqtop version cagnode16:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk (335cf2860bfd9e714d14228d75a52fd2c88db386) *)
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Record sigT {A} (P : A -> Type) := existT { projT1 : A ; projT2 : P projT1 }.
Notation "{ x : A & P }" := (sigT (fun x:A => P)) : type_scope.
Definition relation (A : Type) := A -> A -> Type.
Class Reflexive {A} (R : relation A) := reflexivity : forall x : A, R x x.
Notation "( x ; y )" := (existT _ x y).
Notation "x .1" := (projT1 x) (at level 3, format "x '.1'").
Reserved Infix "o" (at level 40, left associativity).
Delimit Scope category_scope with category.
Record PreCategory :=
  { object :> Type;
    morphism : object -> object -> Type;
    compose : forall s d d', morphism d d' -> morphism s d -> morphism s d' }.
Delimit Scope functor_scope with functor.
Record Functor (C D : PreCategory) := { object_of :> C -> D }.
Local Open Scope category_scope.
Class Isomorphic {C : PreCategory} (s d : C) := {}.
Axiom composeF : forall C D E (G : Functor D E) (F : Functor C D), Functor C E.
Infix "o" := composeF : functor_scope.
Local Open Scope functor_scope.
Definition sub_pre_cat {P : PreCategory -> Type} : PreCategory.
  exact (@Build_PreCategory
           { C : PreCategory & P C }
           (fun C D => Functor C.1 D.1)
           (fun _ _ _ F G => F o G)).
Defined.
Record NaturalTransformation C D (F G : Functor C D) := { components_of :> forall c, morphism D (F c) (G c) }.
Axiom composeT : forall C D (F F' F'' : Functor C D) (T' : NaturalTransformation F' F'') (T : NaturalTransformation F F'),
                   NaturalTransformation F F''.
Definition functor_category (C D : PreCategory) : PreCategory.
  exact (@Build_PreCategory (Functor C D)
                            (@NaturalTransformation C D)
                            (@composeT C D)).
Defined.
Local Notation "C -> D" := (functor_category C D) : category_scope.
Definition NaturalIsomorphism (C D : PreCategory) F G : Type := @Isomorphic (C -> D) F G.
Context `{P : PreCategory -> Type}.
Local Notation cat := (@sub_pre_cat P).
Goal forall (s d d' : cat) (m1 : morphism cat d d') (m2 : morphism cat s d),
       NaturalIsomorphism (m1 o m2) (m1 o m2)%functor.
Fail exact (fun _ _ _ _ _ => reflexivity _).
