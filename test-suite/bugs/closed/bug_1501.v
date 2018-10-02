Set Implicit Arguments.


Require Export Relation_Definitions.
Require Export Setoid.
Require Import Morphisms.


Section Essais.

(* Parametrized Setoid *)
Parameter K : Type -> Type.
Parameter equiv : forall A : Type, K A -> K A -> Prop.
Parameter equiv_refl : forall (A : Type) (x : K A), equiv x x.
Parameter equiv_sym : forall (A : Type) (x y : K A), equiv x y -> equiv y x.
Parameter equiv_trans : forall (A : Type) (x y z : K A), equiv x y -> equiv y z
-> equiv x z.

(* basic operations *)
Parameter val : forall A : Type, A -> K A.
Parameter bind : forall A B : Type, K A -> (A -> K B) -> K B.

Parameter
  bind_compat :
    forall (A B : Type) (m1 m2 : K A) (f1 f2 : A -> K B),
    equiv m1 m2 ->
    (forall x : A, equiv (f1 x) (f2 x)) -> equiv (bind m1 f1) (bind m2 f2).

(* monad axioms *)
Parameter
  bind_val_l :
    forall (A B : Type) (a : A) (f : A -> K B), equiv (bind (val a) f) (f a).
Parameter
  bind_val_r :
    forall (A : Type) (m : K A), equiv (bind m (fun a => val a)) m.
Parameter
  bind_assoc :
    forall (A B C : Type) (m : K A) (f : A -> K B) (g : B -> K C),
    equiv (bind (bind m f) g) (bind m (fun a => bind (f a) g)).


Hint Resolve equiv_refl equiv_sym equiv_trans: monad.

Add Parametric Relation A : (K A) (@equiv A)
    reflexivity proved by (@equiv_refl A)
    symmetry proved by (@equiv_sym A)
    transitivity proved by (@equiv_trans A)
      as equiv_rel.

Add Parametric Morphism A B : (@bind A B)
    with signature (@equiv A) ==> (pointwise_relation A (@equiv B)) ==> (@equiv B)
      as bind_mor.
Proof.
  unfold pointwise_relation; intros; apply bind_compat; auto.
Qed.

Lemma test:
  forall (A B: Type) (m1 m2 m3: K A) (f: A -> A -> K B),
    (equiv m1 m2) -> (equiv m2 m3) ->
    equiv (bind m1 (fun a => bind m2 (fun a' => f a a')))
          (bind m2 (fun a => bind m3 (fun a' => f a a'))).
Proof.
  intros A B m1 m2 m3 f H1 H2.
  setoid_rewrite H1. (* this works *)
  setoid_rewrite H2.
  reflexivity.
Qed.
