(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

Require Import SetoidList.
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

End Permutation.
