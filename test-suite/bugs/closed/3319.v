Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 5353 lines to 4545 lines, then from 4513 lines to 4504 lines, then from 4515 lines to 4508 lines, then from 4519 lines to 132 lines, then from 111 lines to 66 lines, then from 68 lines to 35 lines *)
Set Implicit Arguments.
Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a
                 where "x = y" := (@paths _ x y) : type_scope.

Record PreCategory := { obj :> Type; morphism : obj -> obj -> Type }.
Record NotionOfStructure (X : PreCategory) :=
  { structure :> X -> Type;
    is_structure_homomorphism
    : forall x y (f : morphism X x y) (a : structure x) (b : structure y), Type }.

Section precategory.
  Variable X : PreCategory.
  Variable P : NotionOfStructure X.
  Local Notation object := { x : X & P x }.
  Record morphism' (xa yb : object) := {}.

  Lemma issig_morphism xa yb
  : { f : morphism X (projT1 xa) (projT1 yb)
    & is_structure_homomorphism _ _ _ f (projT2 xa) (projT2 yb) }
    = morphism' xa yb. 
  Proof.
    admit.
  Defined.
