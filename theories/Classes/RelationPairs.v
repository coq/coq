(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

Arguments relation_conjunction A%type (R R')%signature _ _.
Arguments relation_equivalence A%type (_ _)%signature.
Arguments subrelation A%type (R R')%signature.
Arguments Reflexive A%type R%signature.
Arguments Irreflexive A%type R%signature.
Arguments Symmetric A%type R%signature.
Arguments Transitive A%type R%signature.
Arguments PER A%type R%signature.
Arguments Equivalence A%type R%signature.
Arguments StrictOrder A%type R%signature.

Generalizable Variables A B RA RB Ri Ro f.

(** Any function from [A] to [B] allow to obtain a relation over [A]
    out of a relation over [B]. *)

Definition RelCompFun {A} {B : Type}(R:relation B)(f:A->B) : relation A :=
 fun a a' => R (f a) (f a').

(** Instances on RelCompFun must match syntactically *)
Typeclasses Opaque RelCompFun. 

Infix "@@" := RelCompFun (at level 30, right associativity) : signature_scope.

Notation "R @@1" := (R @@ Fst)%signature (at level 30) : signature_scope.
Notation "R @@2" := (R @@ Snd)%signature (at level 30) : signature_scope.

(** We declare measures to the system using the [Measure] class.
   Otherwise the instances would easily introduce loops,
   never instantiating the [f] function.  *)

Class Measure {A B} (f : A -> B).

(** Standard measures. *)

Instance fst_measure : @Measure (A * B) A Fst.
Instance snd_measure : @Measure (A * B) B Snd.

(** We define a product relation over [A*B]: each components should
    satisfy the corresponding initial relation. *)

Definition RelProd {A : Type} {B : Type} (RA:relation A)(RB:relation B) : relation (A*B) :=
 relation_conjunction (@RelCompFun (A * B) A RA fst) (RB @@2).

Typeclasses Opaque RelProd.

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

  Global Program Instance RelCompFun_Equivalence
    `(Measure A B f, Equivalence _ R) : Equivalence (R@@f).

  Global Program Instance RelCompFun_StrictOrder
    `(Measure A B f, StrictOrder _ R) : StrictOrder (R@@f).

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

Hint Unfold RelProd RelCompFun.
Hint Extern 2 (RelProd _ _ _ _) => split.

