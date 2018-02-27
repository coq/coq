(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Some facts and definitions about extensionality

We investigate the relations between the following extensionality principles

- Functional extensionality
- Equality of projections from diagonal
- Unicity of inverse bijections
- Bijectivity of bijective composition

Table of contents

1. Definitions

2. Functional extensionality <-> Equality of projections from diagonal

3. Functional extensionality <-> Unicity of inverse bijections

4. Functional extensionality <-> Bijectivity of bijective composition

*)

Set Implicit Arguments.

(**********************************************************************)
(** * Definitions *)

(** Being an inverse *)

Definition is_inverse A B f g := (forall a:A, g (f a) = a) /\ (forall b:B, f (g b) = b).

(** The diagonal over A and the one-one correspondence with A *)

Record Delta A := { pi1:A; pi2:A; eq:pi1=pi2 }.

Definition delta {A} (a:A) := {|pi1 := a; pi2 := a; eq := eq_refl a |}.

Arguments pi1 {A} _.
Arguments pi2 {A} _.

Lemma diagonal_projs_same_behavior : forall A (x:Delta A), pi1 x = pi2 x.
Proof.
  destruct x as (a1,a2,Heq); assumption.
Qed.

Lemma diagonal_inverse1 : forall A, is_inverse (A:=A) delta pi1.
Proof.
  split; [trivial|]; destruct b as (a1,a2,[]); reflexivity.
Qed.

Lemma diagonal_inverse2 : forall A, is_inverse (A:=A) delta pi2.
Proof.
  split; [trivial|]; destruct b as (a1,a2,[]); reflexivity.
Qed.

(** Functional extensionality *)

Local Notation FunctionalExtensionality := 
  (forall A B (f g : A -> B), (forall x, f x = g x) -> f = g).

(** Equality of projections from diagonal *)

Local Notation EqDeltaProjs := (forall A, pi1 = pi2 :> (Delta A -> A)).

(** Unicity of bijection inverse *)

Local Notation UniqueInverse := (forall A B (f:A->B) g1 g2, is_inverse f g1 -> is_inverse f g2 -> g1 = g2).

(** Bijectivity of bijective composition *)

Definition action A B C (f:A->B) := (fun h:B->C => fun x => h (f x)).

Local Notation BijectivityBijectiveComp := (forall A B C (f:A->B) g,
  is_inverse f g -> is_inverse (A:=B->C) (action f) (action g)).

(**********************************************************************)
(** * Functional extensionality <-> Equality of projections from diagonal *)

Theorem FunctExt_iff_EqDeltaProjs : FunctionalExtensionality <-> EqDeltaProjs.
Proof.
  split.
  - intros FunExt *; apply FunExt, diagonal_projs_same_behavior. 
  - intros EqProjs **; change f with (fun x => pi1 {|pi1:=f x; pi2:=g x; eq:=H x|}).
    rewrite EqProjs; reflexivity.
Qed.

(**********************************************************************)
(** * Functional extensionality <-> Unicity of bijection inverse *)

Lemma FunctExt_UniqInverse : FunctionalExtensionality -> UniqueInverse.
Proof.
  intros FunExt * (Hg1f,Hfg1) (Hg2f,Hfg2).
  apply FunExt. intros; congruence.
Qed.

Lemma UniqInverse_EqDeltaProjs : UniqueInverse -> EqDeltaProjs.
Proof.
  intros UniqInv *.
  apply UniqInv with delta; [apply diagonal_inverse1 | apply diagonal_inverse2].
Qed.

Theorem FunctExt_iff_UniqInverse : FunctionalExtensionality <-> UniqueInverse.
Proof.
  split. 
  - apply FunctExt_UniqInverse.
  - intro; apply FunctExt_iff_EqDeltaProjs, UniqInverse_EqDeltaProjs; trivial.
Qed.

(**********************************************************************)
(** * Functional extensionality <-> Bijectivity of bijective composition *)

Lemma FunctExt_BijComp : FunctionalExtensionality -> BijectivityBijectiveComp.
Proof.
  intros FunExt * (Hgf,Hfg). split; unfold action.
  - intros h; apply FunExt; intro b; rewrite Hfg; reflexivity.
  - intros h; apply FunExt; intro a; rewrite Hgf; reflexivity.
Qed.

Lemma BijComp_FunctExt : BijectivityBijectiveComp -> FunctionalExtensionality.
Proof.
  intros BijComp.
  apply FunctExt_iff_UniqInverse. intros * H1 H2.
  destruct BijComp with (C:=A) (1:=H2) as (Hg2f,_).
  destruct BijComp with (C:=A) (1:=H1) as (_,Hfg1).
  rewrite <- (Hg2f g1).
  change g1 with (action g1 (fun x => x)).
  rewrite -> (Hfg1 (fun x => x)).
  reflexivity.
Qed.
