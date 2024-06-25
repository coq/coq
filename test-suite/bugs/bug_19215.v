Set Implicit Arguments.
Set Universe Polymorphism.

Require Export Notations.
Require Import Ltac.

Notation "A -> B" := (forall (_ : A), B) : type_scope.


Inductive True : Prop :=
  I : True.

Register True as core.True.type.
Register I as core.True.I.

Inductive False : Prop :=.

Register False as core.False.type.

(** [not A], written [~A], is the negation of [A] *)
Definition not (A:Prop) := A -> False.

Notation "~ x" := (not x) : type_scope.

Register not as core.not.type.

Polymorphic Inductive eq@{s s'|u v|} (A:Type@{s|u}) (x:A) : A -> Type@{s'|v} :=
    eq_refl : x = x :>A

where "x = y :> A" := (@eq A x y) : type_scope.

Arguments eq {A} x _.
Arguments eq_refl {A x} , [A] x.

Polymorphic Definition eq_elim@{s s' | u v w |} [A:Type@{s|u}] [x:A]
  (P : forall a : A, x = a :> A -> Type@{s'|w}) :
  P x (eq_refl@{s s'|u v} x) -> forall [a : A] (e : x = a :> A), P a e :=
  fun t _ e => match e with eq_refl => t end.

Polymorphic Definition eq_ind@{s | u|} [A] [x] P := @eq_elim@{s Prop|u Set Set} A x (fun a _ => P a).

Polymorphic Definition eq_singleton@{s s' | u v|} [A:Type@{s|u}] [x:A]
  (P : forall a : A, (eq@{s Prop|u Set} x a) -> Type@{s'|v}) :
  P x (eq_refl x) -> forall [a : A] (e : x = a :> A), P a e :=
  fun t _ e => match e with eq_refl => t end.

Definition eq_rect@{u v|} [A:Type@{u}] [x:A]
  (P : forall a : A, Type@{v}) :
  P x -> forall [a : A] (e : x = a :> A), P a := @eq_singleton A x (fun a _ => P a).

Definition eq_rec@{u|} [A:Type@{u}] [x:A]
  (P : forall a : A, Set) :
  P x -> forall [a : A] (e : x = a :> A), P a := @eq_singleton A x (fun a _ => P a).

Definition eq_sind [A:Set] [x:A]
  (P : forall a : A, SProp) :
  P x -> forall [a : A] (e : x = a :> A), P a := @eq_singleton A x (fun a _ => P a).

Arguments eq_ind [A] x P _ y _ : rename.
Arguments eq_sind [A] x P _ y _ : rename.
Arguments eq_rec [A] x P _ y _ : rename.
Arguments eq_rect [A] x P _ y _ : rename.

Notation "x = y" := (eq@{_ Prop|_ Set} x y) : type_scope.
Notation "x <> y  :> T" := (~ x = y :>T) : type_scope.
Notation "x <> y" := (~ (x = y)) : type_scope.

#[global]
Hint Resolve eq_refl: core.

Register eq as core.eq.type.
Register eq_refl as core.eq.refl.
Register eq_ind as core.eq.ind.
Register eq_rect as core.eq.rect.
Register eq_elim as core.eq.rect.

  Section equality.

    Theorem eq_sym@{s|u|} (A : Type@{s|u}) (x y : A) : x = y -> y = x.
    Proof.
      destruct 1; trivial.
    Defined.

    Register eq_sym as core.eq.sym.

    Theorem eq_trans@{s|u|} (A : Type@{s|u}) (x y z : A) : x = y -> y = z -> x = z.
    Proof.
      destruct 2; trivial.
    Defined.

    Register eq_trans as core.eq.trans.

    Theorem f_equal@{s s'|u v|} (A : Type@{s|u}) (B : Type@{s'|v})
      (x y : A) (f : A -> B) : x = y -> f x = f y.
    Proof.
      destruct 1; trivial.
    Defined.

    Register f_equal as core.eq.congr.

  End equality.

  Inductive comparison : Set :=
  | Eq : comparison
  | Lt : comparison
  | Gt : comparison.

Register comparison as core.comparison.type.
Register Eq as core.comparison.Eq.
Register Lt as core.comparison.Lt.
Register Gt as core.comparison.Gt.

Inductive CompareSpecT (Peq Plt Pgt : Prop) : comparison -> Type :=
 | CompEqT : Peq -> CompareSpecT Peq Plt Pgt Eq
 | CompLtT : Plt -> CompareSpecT Peq Plt Pgt Lt
 | CompGtT : Pgt -> CompareSpecT Peq Plt Pgt Gt.
#[global]
Hint Constructors CompareSpecT : core.

Register CompareSpecT as core.CompareSpecT.type.
Register CompEqT as core.CompareSpecT.CompEqT.
Register CompLtT as core.CompareSpecT.CompLtT.
Register CompGtT as core.CompareSpecT.CompGtT.

Inductive CompareSpec (Peq Plt Pgt : Prop) : comparison -> Prop :=
 | CompEq : Peq -> CompareSpec Peq Plt Pgt Eq
 | CompLt : Plt -> CompareSpec Peq Plt Pgt Lt
 | CompGt : Pgt -> CompareSpec Peq Plt Pgt Gt.
#[global]
Hint Constructors CompareSpec : core.

Register CompareSpec as core.CompareSpec.type.
Register CompEq as core.CompareSpec.CompEq.
Register CompLt as core.CompareSpec.CompLt.
Register CompGt as core.CompareSpec.CompGt.

Lemma CompareSpec2Type Peq Plt Pgt c :
 CompareSpec Peq Plt Pgt c -> CompareSpecT Peq Plt Pgt c.
Proof.
 destruct c; intros H; constructor; inversion_clear H; auto.
Qed.
