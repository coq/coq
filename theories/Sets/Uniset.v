(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Sets as characteristic functions *)

(* G. Huet 1-9-95 *)
(* Updated Papageno 12/98 *)

Require Import Bool Permut.

Set Implicit Arguments.

Section defs.

Variable A : Set.
Variable eqA : A -> A -> Prop.
Hypothesis eqA_dec : forall x y:A, {eqA x y} + {~ eqA x y}.

Inductive uniset : Set :=
    Charac : (A -> bool) -> uniset.

Definition charac (s:uniset) (a:A) : bool := let (f) := s in f a.

Definition Emptyset := Charac (fun a:A => false).

Definition Fullset := Charac (fun a:A => true).

Definition Singleton (a:A) :=
  Charac
    (fun a':A =>
       match eqA_dec a a' with
       | left h => true
       | right h => false
       end).

Definition In (s:uniset) (a:A) : Prop := charac s a = true.
Hint Unfold In.

(** uniset inclusion *)
Definition incl (s1 s2:uniset) := forall a:A, leb (charac s1 a) (charac s2 a).
Hint Unfold incl.

(** uniset equality *)
Definition seq (s1 s2:uniset) := forall a:A, charac s1 a = charac s2 a.
Hint Unfold seq.

Lemma leb_refl : forall b:bool, leb b b.
Proof.
destruct b; simpl; auto.
Qed.
Hint Resolve leb_refl.

Lemma incl_left : forall s1 s2:uniset, seq s1 s2 -> incl s1 s2.
Proof.
unfold incl; intros s1 s2 E a; elim (E a); auto.
Qed.

Lemma incl_right : forall s1 s2:uniset, seq s1 s2 -> incl s2 s1.
Proof.
unfold incl; intros s1 s2 E a; elim (E a); auto.
Qed.

Lemma seq_refl : forall x:uniset, seq x x.
Proof.
destruct x; unfold seq; auto.
Qed.
Hint Resolve seq_refl.

Lemma seq_trans : forall x y z:uniset, seq x y -> seq y z -> seq x z.
Proof.
unfold seq.
destruct x; destruct y; destruct z; simpl; intros.
rewrite H; auto.
Qed.

Lemma seq_sym : forall x y:uniset, seq x y -> seq y x.
Proof.
unfold seq.
destruct x; destruct y; simpl; auto.
Qed.

(** uniset union *)
Definition union (m1 m2:uniset) :=
  Charac (fun a:A => orb (charac m1 a) (charac m2 a)).

Lemma union_empty_left : forall x:uniset, seq x (union Emptyset x).
Proof.
unfold seq; unfold union; simpl; auto.
Qed.
Hint Resolve union_empty_left.

Lemma union_empty_right : forall x:uniset, seq x (union x Emptyset).
Proof.
unfold seq; unfold union; simpl.
intros x a; rewrite (orb_b_false (charac x a)); auto.
Qed.
Hint Resolve union_empty_right.

Lemma union_comm : forall x y:uniset, seq (union x y) (union y x).
Proof.
unfold seq; unfold charac; unfold union.
destruct x; destruct y; auto with bool.
Qed.
Hint Resolve union_comm.

Lemma union_ass :
 forall x y z:uniset, seq (union (union x y) z) (union x (union y z)).
Proof.
unfold seq; unfold union; unfold charac.
destruct x; destruct y; destruct z; auto with bool.
Qed.
Hint Resolve union_ass.

Lemma seq_left : forall x y z:uniset, seq x y -> seq (union x z) (union y z).
Proof.
unfold seq; unfold union; unfold charac.
destruct x; destruct y; destruct z.
intros; elim H; auto.
Qed.
Hint Resolve seq_left.

Lemma seq_right : forall x y z:uniset, seq x y -> seq (union z x) (union z y).
Proof.
unfold seq; unfold union; unfold charac.
destruct x; destruct y; destruct z.
intros; elim H; auto.
Qed.
Hint Resolve seq_right.


(** All the proofs that follow duplicate [Multiset_of_A] *)

(** Here we should make uniset an abstract datatype, by hiding [Charac],
    [union], [charac]; all further properties are proved abstractly *)

Lemma union_rotate :
 forall x y z:uniset, seq (union x (union y z)) (union z (union x y)).
Proof.
intros; apply (op_rotate uniset union seq); auto.
exact seq_trans.
Qed.

Lemma seq_congr :
 forall x y z t:uniset, seq x y -> seq z t -> seq (union x z) (union y t).
Proof.
intros; apply (cong_congr uniset union seq); auto.
exact seq_trans.
Qed.

Lemma union_perm_left :
 forall x y z:uniset, seq (union x (union y z)) (union y (union x z)).
Proof.
intros; apply (perm_left uniset union seq); auto.
exact seq_trans.
Qed.

Lemma uniset_twist1 :
 forall x y z t:uniset,
   seq (union x (union (union y z) t)) (union (union y (union x t)) z).
Proof.
intros; apply (twist uniset union seq); auto.
exact seq_trans.
Qed.

Lemma uniset_twist2 :
 forall x y z t:uniset,
   seq (union x (union (union y z) t)) (union (union y (union x z)) t).
Proof.
intros; apply seq_trans with (union (union x (union y z)) t).
apply seq_sym; apply union_ass.
apply seq_left; apply union_perm_left.
Qed.

(** specific for treesort *)

Lemma treesort_twist1 :
 forall x y z t u:uniset,
   seq u (union y z) ->
   seq (union x (union u t)) (union (union y (union x t)) z).
Proof.
intros; apply seq_trans with (union x (union (union y z) t)).
apply seq_right; apply seq_left; trivial.
apply uniset_twist1.
Qed.

Lemma treesort_twist2 :
 forall x y z t u:uniset,
   seq u (union y z) ->
   seq (union x (union u t)) (union (union y (union x z)) t).
Proof.
intros; apply seq_trans with (union x (union (union y z) t)).
apply seq_right; apply seq_left; trivial.
apply uniset_twist2.
Qed.


(*i theory of minter to do similarly
Require Min.
(* uniset intersection *)
Definition minter := [m1,m2:uniset]
    (Charac [a:A](andb (charac m1 a)(charac m2 a))).
i*)

End defs.

Unset Implicit Arguments.
