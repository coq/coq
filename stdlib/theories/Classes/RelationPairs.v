(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Relations over pairs *)


Require Import SetoidList.
Require Import Relations Morphisms.
(* NB: This should be system-wide someday, but for that we need to
    fix the simpl tactic, since "simpl fst" would be refused for
    the moment.

Arguments fst {A B}.
Arguments snd {A B}.
Arguments pair {A B}.

/NB *)

Local Notation Fst := (@fst _ _).
Local Notation Snd := (@snd _ _).

Arguments relation_conjunction A%_type (R R')%_signature _ _.
Arguments relation_equivalence A%_type (_ _)%_signature.
Arguments subrelation A%_type (R R')%_signature.
Arguments Reflexive A%_type R%_signature.
Arguments Irreflexive A%_type R%_signature.
Arguments Symmetric A%_type R%_signature.
Arguments Transitive A%_type R%_signature.
Arguments PER A%_type R%_signature.
Arguments Equivalence A%_type R%_signature.
Arguments StrictOrder A%_type R%_signature.

Generalizable Variables A B RA RB Ri Ro f.

(** Any function from [A] to [B] allow to obtain a relation over [A]
    out of a relation over [B]. *)

Definition RelCompFun {A} {B : Type}(R:relation B)(f:A->B) : relation A :=
 fun a a' => R (f a) (f a').

(** Instances on RelCompFun must match syntactically *)
Global Typeclasses Opaque RelCompFun.

Infix "@@" := RelCompFun (at level 30, right associativity) : signature_scope.

Notation "R @@1" := (R @@ Fst)%signature (at level 30) : signature_scope.
Notation "R @@2" := (R @@ Snd)%signature (at level 30) : signature_scope.

(** We declare measures to the system using the [Measure] class.
   Otherwise the instances would easily introduce loops,
   never instantiating the [f] function.  *)

Class Measure {A B} (f : A -> B).

(** Standard measures. *)

#[global]
Instance fst_measure {A B} : @Measure (A * B) A Fst := {}.

#[global]
Instance snd_measure {A B} : @Measure (A * B) B Snd := {}.

(** We define a product relation over [A*B]: each components should
    satisfy the corresponding initial relation. *)

Definition RelProd {A : Type} {B : Type} (RA:relation A)(RB:relation B) : relation (A*B) :=
 relation_conjunction (@RelCompFun (A * B) A RA fst) (RB @@2).

Global Typeclasses Opaque RelProd.

Infix "*" := RelProd : signature_scope.

Section RelCompFun_Instances.
  Context {A : Type} {B : Type} (R : relation B).

  Global Instance RelCompFun_Reflexive
    `(Measure A B f, Reflexive _ R) : Reflexive (R@@f).
  Proof. firstorder. Qed.

  Global Instance RelCompFun_Symmetric
    `(Measure A B f, Symmetric _ R) : Symmetric (R@@f).
  Proof. firstorder. Qed.

  Global Instance RelCompFun_Transitive
    `(Measure A B f, Transitive _ R) : Transitive (R@@f).
  Proof. firstorder. Qed.

  Global Instance RelCompFun_Irreflexive
    `(Measure A B f, Irreflexive _ R) : Irreflexive (R@@f).
  Proof. firstorder. Qed.

  Global Instance RelCompFun_Equivalence
    `(Measure A B f, Equivalence _ R) : Equivalence (R@@f) := {}.

  Global Instance RelCompFun_StrictOrder
    `(Measure A B f, StrictOrder _ R) : StrictOrder (R@@f) := {}.

End RelCompFun_Instances.

Section RelProd_Instances.

  Context {A : Type} {B : Type} (RA : relation A) (RB : relation B).

  Global Instance RelProd_Reflexive `(Reflexive _ RA, Reflexive _ RB) : Reflexive (RA*RB).
  Proof. firstorder. Qed.

  Global Instance RelProd_Symmetric `(Symmetric _ RA, Symmetric _ RB)
  : Symmetric (RA*RB).
  Proof. firstorder. Qed.

  Global Instance RelProd_Transitive
           `(Transitive _ RA, Transitive _ RB) : Transitive (RA*RB).
  Proof. firstorder. Qed.

  Global Program Instance RelProd_Equivalence
          `(Equivalence _ RA, Equivalence _ RB) : Equivalence (RA*RB).

  Lemma FstRel_ProdRel :
    relation_equivalence (RA @@1) (RA*(fun _ _ : B => True)).
  Proof. firstorder. Qed.

  Lemma SndRel_ProdRel :
    relation_equivalence (RB @@2) ((fun _ _ : A =>True) * RB).
  Proof. firstorder. Qed.

  Global Instance FstRel_sub :
    subrelation (RA*RB) (RA @@1).
  Proof. firstorder. Qed.

  Global Instance SndRel_sub :
    subrelation (RA*RB) (RB @@2).
  Proof. firstorder. Qed.

  Global Instance pair_compat :
    Proper (RA==>RB==> RA*RB) (@pair _ _).
  Proof. firstorder. Qed.

  Global Instance fst_compat :
    Proper (RA*RB ==> RA) Fst.
  Proof.
    intros (x,y) (x',y') (Hx,Hy); compute in *; auto.
  Qed.

  Global Instance snd_compat :
    Proper (RA*RB ==> RB) Snd.
  Proof.
    intros (x,y) (x',y') (Hx,Hy); compute in *; auto.
  Qed.

  Global Instance RelCompFun_compat (f:A->B)
           `(Proper _ (Ri==>Ri==>Ro) RB) :
    Proper (Ri@@f==>Ri@@f==>Ro) (RB@@f)%signature.
  Proof. unfold RelCompFun; firstorder. Qed.
End RelProd_Instances.

#[global]
Hint Unfold RelProd RelCompFun : core.
#[global]
Hint Extern 2 (RelProd _ _ _ _) => split : core.

#[export] Instance Proper_RelProd_flip_impl: forall A B RA1 RA2 RB1 RB2 (RA : relation A) (RB : relation B),
    Proper (RA1 ==> RA2 ==> Basics.flip Basics.impl) RA
    -> Proper (RB1 ==> RB2 ==> Basics.flip Basics.impl) RB
    -> Proper (RA1 * RB1 ==> RA2 * RB2 ==> Basics.flip Basics.impl) (RA * RB)%signature.
Proof. cbv; intuition eauto. Qed.

#[export] Instance Proper_RelProd_impl: forall A B RA1 RA2 RB1 RB2 (RA : relation A) (RB : relation B),
    Proper (RA1 ==> RA2 ==> Basics.impl) RA
    -> Proper (RB1 ==> RB2 ==> Basics.impl) RB
    -> Proper (RA1 * RB1 ==> RA2 * RB2 ==> Basics.impl) (RA * RB)%signature.
Proof. cbv; intuition eauto. Qed.

#[export] Instance Proper_RelProd_iff: forall A B RA1 RA2 RB1 RB2 (RA : relation A) (RB : relation B),
    Proper (RA1 ==> RA2 ==> iff) RA
    -> Proper (RB1 ==> RB2 ==> iff) RB
    -> Proper (RA1 * RB1 ==> RA2 * RB2 ==> iff) (RA * RB)%signature.
Proof.
  intros A B RA1 RA2 RB1 RB2 RA RB H H0. cbv in *.
  intros x y H1 x0 y0 H2. intuition eauto;
  destruct x as [a b], y as [a0 b0], x0 as [a1 b1], y0 as [a2 b2];
  destruct H with a a0 a1 a2;
  destruct H0 with b b0 b1 b2;
  eauto.
Qed.
