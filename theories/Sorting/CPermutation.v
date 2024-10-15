(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Circular Shifts (aka Cyclic Permutations) *)

(** The main inductive [CPermutation] relates lists up to circular shifts of their elements.

For example: [CPermutation [a1;a2;a3;a4;a5] [a4;a5;a1;a2;a3]]

Note: Terminology does not seem to be strongly fixed in English. For the record, it is "permutations circulaires" in French.
*)

Require Import List Permutation Morphisms PeanoNat.
Import ListNotations. (* For notations [] and [a;b;c] *)
Set Implicit Arguments.

Local Ltac Tauto.intuition_solver ::= auto with datatypes.

Section CPermutation.

Variable A:Type.

(** Definition *)

Inductive CPermutation : list A -> list A -> Prop :=
| cperm : forall l1 l2, CPermutation (l1 ++ l2) (l2 ++ l1).

Instance CPermutation_Permutation : Proper (CPermutation ==> (@Permutation A)) id.
Proof. intros ? ? [? ?]; apply Permutation_app_comm. Qed.

(** Some facts about [CPermutation] *)

Theorem CPermutation_nil : forall l, CPermutation [] l -> l = [].
Proof.
intros l HC; inversion HC as [l1 l2 Heq]; subst.
now apply app_eq_nil in Heq; destruct Heq; subst.
Qed.

Theorem CPermutation_nil_cons : forall l a, ~ CPermutation [] (a :: l).
Proof. intros l a HC; apply CPermutation_nil in HC; inversion HC. Qed.

Theorem CPermutation_nil_app_cons : forall l1 l2 a,
 ~ CPermutation [] (l1 ++ a ::l2).
Proof.
intros l1 l2 a HC; apply CPermutation_nil in HC; destruct l1; inversion HC.
Qed.

Lemma CPermutation_split : forall l1 l2,
  CPermutation l1 l2 <-> exists n, l2 = skipn n l1 ++ firstn n l1.
Proof.
intros l1 l2; split.
- intros [l1' l2'].
  exists (length l1').
  rewrite skipn_app, skipn_all, Nat.sub_diag; simpl; f_equal.
  now rewrite firstn_app, firstn_all, Nat.sub_diag; simpl; rewrite app_nil_r.
- now intros [n ->]; rewrite <- (firstn_skipn n) at 1.
Qed.


(** Equivalence relation *)

Theorem CPermutation_refl : forall l, CPermutation l l.
Proof.
intros l; now rewrite <- (app_nil_l l) at 1; rewrite <- (app_nil_r l) at 2.
Qed.

Instance CPermutation_refl' : Proper (Logic.eq ==> CPermutation) id.
Proof. intros ? ? ->; apply CPermutation_refl. Qed.

Theorem CPermutation_sym : forall l l', CPermutation l l' -> CPermutation l' l.
Proof. now intros ? ? [? ?]. Qed.

Theorem CPermutation_trans : forall l l' l'',
 CPermutation l l' -> CPermutation l' l'' -> CPermutation l l''.
Proof.
intros l l' l'' HC1 HC2.
inversion HC1 as [l1 l2]; inversion HC2 as [l3 l4 Heq Heq']; subst.
clear - Heq; revert l1 l2 l4 Heq; clear; induction l3; simpl; intros.
- now subst; rewrite app_nil_r.
- destruct l2 as [| b].
  + simpl in Heq; subst.
    now rewrite app_nil_r, app_comm_cons.
  + inversion Heq as [[Heqb Heq']]; subst.
    replace (l1 ++ b :: l2) with ((l1 ++ b :: nil) ++ l2)
      by now rewrite <- app_assoc, <- app_comm_cons.
    replace (l4 ++ b :: l3) with ((l4 ++ b :: nil) ++ l3)
      by now rewrite <- app_assoc, <- app_comm_cons.
    apply IHl3.
    now rewrite 2 app_assoc, Heq'.
Qed.

End CPermutation.

#[global]
Hint Resolve CPermutation_refl : core.

(* These hints do not reduce the size of the problem to solve and they
   must be used with care to avoid combinatoric explosions *)

Local Hint Resolve cperm CPermutation_sym CPermutation_trans : core.

#[global]
Instance CPermutation_Equivalence A : Equivalence (@CPermutation A) | 10 := {
  Equivalence_Reflexive := @CPermutation_refl A ;
  Equivalence_Symmetric := @CPermutation_sym A ;
  Equivalence_Transitive := @CPermutation_trans A }.


Section CPermutation_properties.

Variable A B:Type.

Implicit Types a b : A.
Implicit Types l : list A.

(** Compatibility with others operations on lists *)

Lemma CPermutation_app : forall l1 l2 l3,
  CPermutation (l1 ++ l2) l3 -> CPermutation (l2 ++ l1) l3.
Proof. intros l1 l2 l3 HC; now transitivity (l1 ++ l2). Qed.

Theorem CPermutation_app_comm : forall l1 l2, CPermutation (l1 ++ l2) (l2 ++ l1).
Proof. apply cperm. Qed.

Lemma CPermutation_app_rot : forall l1 l2 l3,
   CPermutation (l1 ++ l2 ++ l3) (l2 ++ l3 ++ l1).
Proof. intros l1 l2 l3; now rewrite (app_assoc l2). Qed.

Lemma CPermutation_cons_append : forall l a,
  CPermutation (a :: l) (l ++ [a]).
Proof. intros l a; now rewrite <- (app_nil_l l), app_comm_cons. Qed.

Lemma CPermutation_morph_cons : forall P : list A -> Prop,
  (forall a l, P (l ++ [a]) -> P (a :: l)) ->
  Proper (@CPermutation A ==> iff) P.
Proof.
enough (forall P : list A -> Prop,
         (forall a l, P (l ++ [a]) -> P (a :: l)) ->
         forall l1 l2, CPermutation l1 l2 -> P l1 -> P l2)
  as Himp
  by now intros P HP l1 l2 HC; split; [ | symmetry in HC ]; apply Himp.
intros P HP l1 l2 [l1' l2'].
revert l1'; induction l2' using rev_ind; intros l1' HPl.
- now rewrite app_nil_r in HPl.
- rewrite app_assoc in HPl.
  apply HP in HPl.
  rewrite <- app_assoc, <- app_comm_cons, app_nil_l.
  now apply IHl2'.
Qed.

Lemma CPermutation_length_1 : forall a b, CPermutation [a] [b] -> a = b.
Proof. intros; now apply Permutation_length_1, CPermutation_Permutation. Qed.

Lemma CPermutation_length_1_inv : forall a l, CPermutation [a] l -> l = [a].
Proof. intros; now apply Permutation_length_1_inv, CPermutation_Permutation. Qed.

Lemma CPermutation_swap : forall a b, CPermutation [a; b] [b; a].
Proof.
intros; now change [a; b] with ([a] ++ [b]); change [b; a] with ([b] ++ [a]).
Qed.

Lemma CPermutation_length_2 : forall a1 a2 b1 b2,
  CPermutation [a1; a2] [b1; b2] ->
    a1 = b1 /\ a2 = b2 \/ a1 = b2 /\ a2 = b1.
Proof. intros; now apply Permutation_length_2, CPermutation_Permutation. Qed.

Lemma CPermutation_length_2_inv : forall a b l,
  CPermutation [a; b] l -> l = [a; b] \/ l = [b; a].
Proof. intros; now apply Permutation_length_2_inv, CPermutation_Permutation. Qed.

Lemma CPermutation_vs_elt_inv : forall l l1 l2 a,
  CPermutation l (l1 ++ a :: l2) ->
  exists l' l'', l2 ++ l1 = l'' ++ l' /\ l = l' ++ a :: l''.
Proof.
intros l l1 l2 a HC.
inversion HC as [l1' l2' Heq' Heq]; clear HC; subst.
enough (exists l3, (l2' ++ l3 = l1 /\ l1' = l3 ++ a :: l2)
                \/ (l2' = l1 ++ a :: l3 /\ l3 ++ l1' = l2))
  as [l3 [[<- ->]|[-> <-]]].
- exists l3, (l2 ++ l2'); rewrite app_comm_cons; intuition.
- exists (l1' ++ l1), l3; intuition.
- revert l1' l2' l2 Heq; induction l1; simpl; intros l1' l2' l2 Heq.
  + destruct l2'; inversion Heq; subst.
    * exists nil; intuition.
    * exists l2'; intuition.
  + destruct l2'; inversion Heq; subst.
    * exists (a0 :: l1); intuition.
    * apply IHl1 in H1 as [l3 [[<- ->]|[-> <-]]]; exists l3; intuition.
Qed.

Lemma CPermutation_vs_cons_inv : forall l l0 a,
  CPermutation l (a :: l0) -> exists l' l'', l0 = l'' ++ l' /\ l = l' ++ a :: l''.
Proof. intros; rewrite <- (app_nil_r l0); now apply CPermutation_vs_elt_inv. Qed.

End CPermutation_properties.


(** [rev], [in], [map], [Forall], [Exists], etc. *)

Global Instance CPermutation_rev A :
  Proper (@CPermutation A ==> @CPermutation A) (@rev A) | 10.
Proof.
intro l; induction l; intros l' HC.
- now apply CPermutation_nil in HC; subst.
- symmetry in HC.
  destruct (CPermutation_vs_cons_inv HC) as [l1 [l2 [-> ->]]].
  simpl; rewrite ? rev_app_distr; simpl.
  now rewrite <- app_assoc.
Qed.

Global Instance CPermutation_in A a :
  Proper (@CPermutation A ==> Basics.impl) (In a).
Proof.
intros l l' HC Hin.
now apply Permutation_in with l; [ apply CPermutation_Permutation | ].
Qed.

Global Instance CPermutation_in' A :
  Proper (Logic.eq ==> @CPermutation A ==> iff) (@In A) | 10.
Proof. intros a a' <- l l' HC; split; now apply CPermutation_in. Qed.

Global Instance CPermutation_map A B (f : A -> B) :
   Proper (@CPermutation A ==> @CPermutation B) (map f) | 10.
Proof. now intros ? ? [l1 l2]; rewrite 2 map_app. Qed.

Lemma CPermutation_map_inv A B : forall (f : A -> B) m l,
  CPermutation m (map f l) -> exists l', m = map f l' /\ CPermutation l l'.
Proof.
induction m as [| b m]; intros l HC.
- exists nil; split; auto.
  destruct l; auto.
  apply CPermutation_nil in HC; inversion HC.
- symmetry in HC.
  destruct (CPermutation_vs_cons_inv HC) as [m1 [m2 [-> Heq]]].
  apply map_eq_app in Heq as [l1 [l1' [-> [<- Heq]]]].
  apply map_eq_cons in Heq as [a [l1'' [-> [<- <-]]]].
  exists (a :: l1'' ++ l1); split.
  + now simpl; rewrite map_app.
  + now rewrite app_comm_cons.
Qed.

Lemma CPermutation_image A B : forall (f : A -> B) a l l',
  CPermutation (a :: l) (map f l') -> exists a', a = f a'.
Proof.
intros f a l l' HP.
now apply CPermutation_Permutation, Permutation_image in HP.
Qed.

#[global]
Instance CPermutation_Forall A (P : A -> Prop) :
  Proper (@CPermutation A ==> Basics.impl) (Forall P).
Proof.
intros ? ? [? ?] HF.
now apply Forall_app in HF; apply Forall_app.
Qed.

#[global]
Instance CPermutation_Exists A (P : A -> Prop) :
  Proper (@CPermutation A ==> Basics.impl) (Exists P).
Proof.
intros ? ? [? ?] HE.
apply Exists_app in HE; apply Exists_app; intuition.
Qed.

Lemma CPermutation_Forall2 A B (P : A -> B -> Prop) :
  forall l1 l1' l2, CPermutation l1 l1' -> Forall2 P l1 l2 -> exists l2',
    CPermutation l2 l2' /\ Forall2 P l1' l2'.
Proof.
intros ? ? ? [? ?] HF.
apply Forall2_app_inv_l in HF as (l2' & l2'' & HF' & HF'' & ->).
exists (l2'' ++ l2'); intuition.
now apply Forall2_app.
Qed.


(** As an equivalence relation compatible with some operations,
[CPermutation] can be used through [rewrite]. *)
Example CPermutation_rewrite_rev A (l1 l2 l3: list A) :
  CPermutation l1 l2 ->
  CPermutation (rev l1) l3 -> CPermutation l3 (rev l2).
Proof. intros HP1 HP2; rewrite <- HP1, HP2; reflexivity. Qed.
