(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Permutation SetoidList.
(* Set Universe Polymorphism. *)

Set Implicit Arguments.
Unset Strict Implicit.

(** Permutations of list modulo a setoid equality. *)

(** Contribution by Robbert Krebbers (Nijmegen University). *)

Section Permutation.
Context {A : Type} (eqA : relation A) (e : Equivalence eqA).

Inductive PermutationA : list A -> list A -> Prop :=
  | permA_nil: PermutationA nil nil
  | permA_skip x₁ x₂ l₁ l₂ :
     eqA x₁ x₂ -> PermutationA l₁ l₂ -> PermutationA (x₁ :: l₁) (x₂ :: l₂)
  | permA_swap x y l : PermutationA (y :: x :: l) (x :: y :: l)
  | permA_trans l₁ l₂ l₃ :
     PermutationA l₁ l₂ -> PermutationA l₂ l₃ -> PermutationA l₁ l₃.
Local Hint Constructors PermutationA.

Global Instance: Equivalence PermutationA.
Proof.
 constructor.
 - intro l. induction l; intuition.
 - intros l₁ l₂. induction 1; eauto. apply permA_skip; intuition.
 - exact permA_trans.
Qed.

Global Instance PermutationA_cons :
  Proper (eqA ==> PermutationA ==> PermutationA) (@cons A).
Proof.
 repeat intro. now apply permA_skip.
Qed.

Lemma PermutationA_app_head l₁ l₂ l :
  PermutationA l₁ l₂ -> PermutationA (l ++ l₁) (l ++ l₂).
Proof.
 induction l; trivial; intros. apply permA_skip; intuition.
Qed.

Global Instance PermutationA_app :
  Proper (PermutationA ==> PermutationA ==> PermutationA) (@app A).
Proof.
 intros l₁ l₂ Pl k₁ k₂ Pk.
 induction Pl.
 - easy.
 - now apply permA_skip.
 - etransitivity.
   * rewrite <-!app_comm_cons. now apply permA_swap.
   * rewrite !app_comm_cons. now apply PermutationA_app_head.
 - do 2 (etransitivity; try eassumption).
   apply PermutationA_app_head. now symmetry.
Qed.

Lemma PermutationA_app_tail l₁ l₂ l :
  PermutationA l₁ l₂ -> PermutationA (l₁ ++ l) (l₂ ++ l).
Proof.
 intros E. now rewrite E.
Qed.

Lemma PermutationA_cons_append l x :
  PermutationA (x :: l) (l ++ x :: nil).
Proof.
 induction l.
 - easy.
 - simpl. rewrite <-IHl. intuition.
Qed.

Lemma PermutationA_app_comm l₁ l₂ :
  PermutationA (l₁ ++ l₂) (l₂ ++ l₁).
Proof.
 induction l₁.
 - now rewrite app_nil_r.
 - rewrite <-app_comm_cons, IHl₁, app_comm_cons.
   now rewrite PermutationA_cons_append, <-app_assoc.
Qed.

Lemma PermutationA_cons_app l l₁ l₂ x :
  PermutationA l (l₁ ++ l₂) -> PermutationA (x :: l) (l₁ ++ x :: l₂).
Proof.
 intros E. rewrite E.
 now rewrite app_comm_cons, (PermutationA_cons_append l₁ x), <- app_assoc.
Qed.

Lemma PermutationA_middle l₁ l₂ x :
  PermutationA (x :: l₁ ++ l₂) (l₁ ++ x :: l₂).
Proof.
 now apply PermutationA_cons_app.
Qed.

Lemma PermutationA_equivlistA l₁ l₂ :
  PermutationA l₁ l₂ -> equivlistA eqA l₁ l₂.
Proof.
 induction 1.
 - reflexivity.
 - now apply equivlistA_cons_proper.
 - now apply equivlistA_permute_heads.
 - etransitivity; eassumption.
Qed.

Lemma NoDupA_equivlistA_PermutationA l₁ l₂ :
  NoDupA eqA l₁ -> NoDupA eqA l₂ ->
   equivlistA eqA l₁ l₂ -> PermutationA l₁ l₂.
Proof.
  intros Pl₁. revert l₂. induction Pl₁ as [|x l₁ E1].
  - intros l₂ _ H₂. symmetry in H₂. now rewrite (equivlistA_nil_eq eqA).
  - intros l₂ Pl₂ E2.
    destruct (@InA_split _ eqA l₂ x) as [l₂h [y [l₂t [E3 ?]]]].
    { rewrite <-E2. intuition. }
    subst. transitivity (y :: l₁); [intuition |].
    apply PermutationA_cons_app, IHPl₁.
    now apply NoDupA_split with y.
    apply equivlistA_NoDupA_split with x y; intuition.
Qed.

Lemma Permutation_eqlistA_commute l₁ l₂ l₃ :
 eqlistA eqA l₁ l₂ -> Permutation l₂ l₃ ->
 exists l₂', Permutation l₁ l₂' /\ eqlistA eqA l₂' l₃.
Proof.
 intros E P. revert l₁ E.
 induction P; intros.
 - inversion_clear E. now exists nil.
 - inversion_clear E.
   destruct (IHP l0) as (l0',(P',E')); trivial. clear IHP.
   exists (x0::l0'). split; auto.
 - inversion_clear E. inversion_clear H0.
   exists (x1::x0::l1). now repeat constructor.
 - clear P1 P2.
   destruct (IHP1 _ E) as (l₁',(P₁,E₁)).
   destruct (IHP2 _ E₁) as (l₂',(P₂,E₂)).
   exists l₂'. split; trivial. econstructor; eauto.
Qed.

Lemma PermutationA_decompose l₁ l₂ :
 PermutationA l₁ l₂ ->
 exists l, Permutation l₁ l /\ eqlistA eqA l l₂.
Proof.
 induction 1.
 - now exists nil.
 - destruct IHPermutationA as (l,(P,E)). exists (x₁::l); auto.
 - exists (x::y::l). split. constructor. reflexivity.
 - destruct IHPermutationA1 as (l₁',(P,E)).
   destruct IHPermutationA2 as (l₂',(P',E')).
   destruct (@Permutation_eqlistA_commute l₁' l₂ l₂') as (l₁'',(P'',E''));
    trivial.
   exists l₁''. split. now transitivity l₁'. now transitivity l₂'.
Qed.

Lemma Permutation_PermutationA l₁ l₂ :
 Permutation l₁ l₂ -> PermutationA l₁ l₂.
Proof.
 induction 1.
 - constructor.
 - now constructor.
 - apply permA_swap.
 - econstructor; eauto.
Qed.

Lemma eqlistA_PermutationA l₁ l₂ :
 eqlistA eqA l₁ l₂ -> PermutationA l₁ l₂.
Proof.
 induction 1; now constructor.
Qed.

Lemma NoDupA_equivlistA_decompose l1 l2 :
  NoDupA eqA l1 -> NoDupA eqA l2 -> equivlistA eqA l1 l2 ->
  exists l, Permutation l1 l /\ eqlistA eqA l l2.
Proof.
 intros. apply PermutationA_decompose.
 now apply NoDupA_equivlistA_PermutationA.
Qed.

Lemma PermutationA_preserves_NoDupA l₁ l₂ :
 PermutationA l₁ l₂ -> NoDupA eqA l₁ -> NoDupA eqA l₂.
Proof.
 induction 1; trivial.
 - inversion_clear 1; constructor; auto.
   apply PermutationA_equivlistA in H0. contradict H2.
   now rewrite H, H0.
 - inversion_clear 1. inversion_clear H1. constructor.
   + contradict H. inversion_clear H; trivial.
     elim H0. now constructor.
   + constructor; trivial.
     contradict H0. now apply InA_cons_tl.
 - eauto.
Qed.

End Permutation.
