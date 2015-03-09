Require Import TestSuite.admit.
Require Import Coq.Classes.Morphisms Coq.Classes.RelationClasses Coq.Program.Program Coq.Setoids.Setoid.

Global Set Implicit Arguments.

Hint Extern 0 => apply reflexivity : typeclass_instances.

Inductive Comp : Type -> Type :=
| Pick : forall A, (A -> Prop) -> Comp A.

Axiom computes_to : forall A, Comp A -> A -> Prop.

Axiom refine : forall {A} (old : Comp A) (new : Comp A), Prop.

Global Instance refine_PreOrder A : PreOrder (@refine A).
Admitted.
Add Parametric Morphism A
: (@Pick A)
    with signature
    (pointwise_relation _ (flip impl))
      ==> (@refine A)
      as refine_flip_impl_Pick.
  admit.
Defined.
Definition remove_forall_eq' A x B (P : A -> B -> Prop) : pointwise_relation _ impl (P x) (fun z => forall y : A, y = x -> P y z).
  admit.
Defined.
Goal forall A B (x : A) (P : _ -> _ -> Prop),
       refine (Pick (fun n : B => forall y, y = x -> P y n))
              (Pick (fun n : B => P x n)).
Proof.
  intros.
  setoid_rewrite (@remove_forall_eq' _ _ _ _).
  Undo.
  (* This failed with NotConvertible at some time *)
  setoid_rewrite (@remove_forall_eq' _ _ _).
