(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Nnat.
Require Import NMinus.
Require Export BigN.

(** * [BigN] implements [NAxiomsSig] *)

Module BigNAxiomsMod <: NAxiomsSig.
Import BigN.
Open Local Scope bigN_scope.
Module Export NZOrdAxiomsMod <: NZOrdAxiomsSig.
Module Export NZAxiomsMod <: NZAxiomsSig.

Definition NZ := bigN.
Definition NZeq n m := (to_Z n = to_Z m).
Definition NZ0 := 0.
Definition NZsucc := succ.
Definition NZpred := pred.
Definition NZplus := add.
Definition NZminus := sub.
Definition NZtimes := mul.

Delimit Scope IntScope with Int.
Bind Scope IntScope with NZ.
Open Local Scope IntScope.
Notation "[ x ]" := (to_Z x).
Notation "x == y"  := (NZeq x y) (at level 70) : IntScope.
Notation "x ~= y" := (~ NZeq x y) (at level 70) : IntScope.
Notation "0" := NZ0 : IntScope.
Notation "'S'" := NZsucc : IntScope.
Notation "'P'" := NZpred : IntScope.
Notation "x + y" := (NZplus x y) : IntScope.
Notation "x - y" := (NZminus x y) : IntScope.
Notation "x * y" := (NZtimes x y) : IntScope.

Theorem NZeq_equiv : equiv NZ NZeq.
Proof.
unfold NZeq; repeat split; repeat red; intros; auto; congruence.
Qed.

Add Relation NZ NZeq
 reflexivity proved by (proj1 NZeq_equiv)
 symmetry proved by (proj2 (proj2 NZeq_equiv))
 transitivity proved by (proj1 (proj2 NZeq_equiv))
 as NZeq_rel.

Add Morphism NZsucc with signature NZeq ==> NZeq as NZsucc_wd.
Proof.
unfold NZeq; intros; rewrite 2 spec_succ; f_equal; auto.
Qed.

Add Morphism NZpred with signature NZeq ==> NZeq as NZpred_wd.
Proof.
unfold NZeq; intros.
generalize (spec_pos y) (spec_pos x) (spec_eq_bool x 0).
destruct eq_bool; change (to_Z 0) with 0%Z; intros.
rewrite 2 spec_pred0; congruence.
rewrite 2 spec_pred; f_equal; auto; try omega.
Qed.

Add Morphism NZplus with signature NZeq ==> NZeq ==> NZeq as NZplus_wd.
Proof.
unfold NZeq; intros; rewrite 2 spec_add; f_equal; auto.
Qed.

Add Morphism NZminus with signature NZeq ==> NZeq ==> NZeq as NZminus_wd.
Proof.
unfold NZeq; intros x x' Hx y y' Hy.
destruct (Z_lt_le_dec [x] [y]).
rewrite 2 spec_sub0; f_equal; congruence.
rewrite 2 spec_sub; f_equal; congruence.
Qed.

Add Morphism NZtimes with signature NZeq ==> NZeq ==> NZeq as NZtimes_wd.
Proof.
unfold NZeq; intros; rewrite 2 spec_mul; f_equal; auto.
Qed.

Theorem NZpred_succ : forall n : NZ, P (S n) == n.
Proof.
unfold NZeq; intros.
rewrite BigN.spec_pred; rewrite BigN.spec_succ.
omega.
generalize (BigN.spec_pos n); omega.
Qed.

Definition of_Z z := of_N (Zabs_N z).

Section Induction.

Variable A : NZ -> Prop.
Hypothesis A_wd : predicate_wd NZeq A.
Hypothesis A0 : A 0.
Hypothesis AS : forall n : NZ, A n <-> A (S n). 

Add Morphism A with signature NZeq ==> iff as A_morph.
Proof. apply A_wd. Qed.

Let B (z : Z) := A (of_Z z).

Lemma B0 : B 0.
Proof.
exact A0.
Qed.

Lemma BS : forall z : Z, 0 <= z -> B z -> B (z + 1).
Proof.
intros z H1 H2.
unfold B in *. apply -> AS in H2.
setoid_replace (of_Z (z + 1)) with (S (of_Z z)); auto.
unfold NZeq. rewrite spec_succ.
unfold of_Z.
rewrite 2 spec_of_N, 2 Z_of_N_abs, 2 Zabs_eq; auto with zarith.
Qed.

Lemma B_holds : forall z : Z, 0 <= z -> B z.
Proof.
exact (natlike_ind B B0 BS).
Qed.

Theorem NZinduction : forall n : NZ, A n.
Proof.
intro n. setoid_replace n with (of_Z (to_Z n)).
apply B_holds. apply spec_pos.
red; unfold of_Z.
rewrite spec_of_N, Z_of_N_abs, Zabs_eq; auto.
apply spec_pos.
Qed.

End Induction.

Theorem NZplus_0_l : forall n : NZ, 0 + n == n.
Proof.
intros; red; rewrite spec_add; auto with zarith.
Qed.

Theorem NZplus_succ_l : forall n m : NZ, (S n) + m == S (n + m).
Proof.
intros; red; rewrite spec_add, 2 spec_succ, spec_add; auto with zarith.
Qed.

Theorem NZminus_0_r : forall n : NZ, n - 0 == n.
Proof.
intros; red; rewrite spec_sub; change [0] with 0%Z; auto with zarith.
apply spec_pos.
Qed.

Theorem NZminus_succ_r : forall n m : NZ, n - (S m) == P (n - m).
Proof.
intros; red.
destruct (Z_lt_le_dec [n] [S m]) as [H|H].
rewrite spec_sub0; auto.
rewrite spec_succ in H.
rewrite spec_pred0; auto.
destruct (Z_eq_dec [n] [m]).
rewrite spec_sub; auto with zarith.
rewrite spec_sub0; auto with zarith.

rewrite spec_sub, spec_succ in *; auto.
rewrite spec_pred, spec_sub; auto with zarith.
rewrite spec_sub; auto with zarith.
Qed.

Theorem NZtimes_0_l : forall n : NZ, 0 * n == 0.
Proof.
intros; red.
rewrite spec_mul; auto with zarith.
Qed.

Theorem NZtimes_succ_l : forall n m : NZ, (S n) * m == n * m + m.
Proof.
intros; red.
rewrite spec_add, 2 spec_mul, spec_succ; ring.
Qed.

End NZAxiomsMod.

Open Scope bigN_scope.
Open Scope IntScope.

Definition NZlt n m := (compare n m = Lt).
Definition NZle n m := (compare n m <> Gt).
Definition NZmin n m := match compare n m with Gt => m | _ => n end.
Definition NZmax n m := match compare n m with Lt => m | _ => n end.

Infix "<=" := NZle : IntScope.
Infix "<" := NZlt : IntScope.

Lemma spec_compare_alt : forall x y, (x ?= y) = ([x] ?= [y])%Z.
Proof.
 intros; generalize (spec_compare x y).
 destruct (x ?= y); auto.
 intros H; rewrite H; symmetry; apply Zcompare_refl.
Qed.

Lemma spec_lt : forall x y, (x<y) <-> ([x]<[y])%Z.
Proof.
 intros; unfold NZlt, Zlt; rewrite spec_compare_alt; intuition.
Qed.

Lemma spec_le : forall x y, (x<=y) <-> ([x]<=[y])%Z.
Proof.
 intros; unfold NZle, Zle; rewrite spec_compare_alt; intuition.
Qed.

Lemma spec_min : forall x y, [NZmin x y] = Zmin [x] [y].
Proof.
 intros; unfold NZmin, Zmin.
 rewrite spec_compare_alt; destruct Zcompare; auto.
Qed.

Lemma spec_max : forall x y, [NZmax x y] = Zmax [x] [y].
Proof.
 intros; unfold NZmax, Zmax.
 rewrite spec_compare_alt; destruct Zcompare; auto.
Qed.

Add Morphism compare with signature NZeq ==> NZeq ==> (@eq comparison) as compare_wd.
Proof. 
intros x x' Hx y y' Hy.
rewrite 2 spec_compare_alt; rewrite Hx, Hy; intuition.
Qed.

Add Morphism NZlt with signature NZeq ==> NZeq ==> iff as NZlt_wd.
Proof.
intros x x' Hx y y' Hy; unfold NZlt; rewrite Hx, Hy; intuition.
Qed.

Add Morphism NZle with signature NZeq ==> NZeq ==> iff as NZle_wd.
Proof.
intros x x' Hx y y' Hy; unfold NZle; rewrite Hx, Hy; intuition.
Qed.

Add Morphism NZmin with signature NZeq ==> NZeq ==> NZeq as NZmin_wd.
Proof.
intros; red; rewrite 2 spec_min; congruence.
Qed.

Add Morphism NZmax with signature NZeq ==> NZeq ==> NZeq as NZmax_wd.
Proof.
intros; red; rewrite 2 spec_max; congruence.
Qed.

Theorem NZlt_eq_cases : forall n m : NZ, n <= m <-> n < m \/ n == m.
Proof.
intros.
unfold NZeq; rewrite spec_lt, spec_le; omega.
Qed.

Theorem NZlt_irrefl : forall n : NZ, ~ n < n.
Proof.
intros; rewrite spec_lt; auto with zarith.
Qed.

Theorem NZlt_succ_r : forall n m : NZ, n < (NZsucc m) <-> n <= m.
Proof.
intros; rewrite spec_lt, spec_le, spec_succ; omega.
Qed.

Theorem NZmin_l : forall n m : NZ, n <= m -> NZmin n m == n.
Proof.
intros n m; unfold NZeq; rewrite spec_le, spec_min.
generalize (Zmin_spec [n] [m]); omega.
Qed.

Theorem NZmin_r : forall n m : NZ, m <= n -> NZmin n m == m.
Proof.
intros n m; unfold NZeq; rewrite spec_le, spec_min.
generalize (Zmin_spec [n] [m]); omega.
Qed.

Theorem NZmax_l : forall n m : NZ, m <= n -> NZmax n m == n.
Proof.
intros n m; unfold NZeq; rewrite spec_le, spec_max.
generalize (Zmax_spec [n] [m]); omega.
Qed.

Theorem NZmax_r : forall n m : NZ, n <= m -> NZmax n m == m.
Proof.
intros n m; unfold NZeq; rewrite spec_le, spec_max.
generalize (Zmax_spec [n] [m]); omega.
Qed.

End NZOrdAxiomsMod.

Theorem pred_0 : P 0 == 0.
Proof.
reflexivity.
Qed.

Definition to_N n := Zabs_N (to_Z n).

Definition recursion (A : Type) (a : A) (f : NZ -> A -> A) (n : NZ) :=
  Nrect (fun _ => A) a (fun n a => f (of_N n) a) (to_N n).
Implicit Arguments recursion [A].

Theorem recursion_wd :
forall (A : Type) (Aeq : relation A),
  forall a a' : A, Aeq a a' ->
    forall f f' : NZ -> A -> A, fun2_eq NZeq Aeq Aeq f f' ->
      forall x x' : NZ, x == x' ->
        Aeq (recursion a f x) (recursion a' f' x').
Proof.
unfold fun2_wd, NZeq, fun2_eq.
intros A Aeq a a' Eaa' f f' Eff' x x' Exx'.
unfold recursion.
unfold to_N.
rewrite <- Exx'; clear x' Exx'.
replace (Zabs_N [x]) with (N_of_nat (Zabs_nat [x])).
induction (Zabs_nat [x]).
simpl; auto.
rewrite N_of_S, 2 Nrect_step; auto.
destruct [x]; simpl; auto.
change (nat_of_P p) with (nat_of_N (Npos p)); apply N_of_nat_of_N.
change (nat_of_P p) with (nat_of_N (Npos p)); apply N_of_nat_of_N.
Qed.

Theorem recursion_0 :
  forall (A : Type) (a : A) (f : NZ -> A -> A), recursion a f 0 = a.
Proof.
intros A a f; unfold recursion; now rewrite Nrect_base.
Qed.

Theorem recursion_succ :
  forall (A : Type) (Aeq : relation A) (a : A) (f : NZ -> A -> A),
    Aeq a a -> fun2_wd NZeq Aeq Aeq f ->
      forall n : NZ, Aeq (recursion a f (S n)) (f n (recursion a f n)).
Proof.
unfold NZeq, recursion, fun2_wd; intros A Aeq a f EAaa f_wd n.
replace (to_N (S n)) with (Nsucc (to_N n)).
rewrite Nrect_step.
apply f_wd; auto.
unfold to_N.
rewrite spec_of_N, Z_of_N_abs, Zabs_eq; auto.
 apply spec_pos.

fold (recursion a f n).
apply recursion_wd; auto.
red; auto.
red; auto.
unfold to_N.

rewrite spec_succ.
change ([n]+1)%Z with (Zsucc [n]).
apply Z_of_N_eq_rev.
rewrite Z_of_N_succ.
rewrite 2 Z_of_N_abs.
rewrite 2 Zabs_eq; auto.
generalize (spec_pos n); auto with zarith.
apply spec_pos; auto.
Qed.

End BigNAxiomsMod.

Module Export BigNMinusPropMod := NMinusPropFunct BigNAxiomsMod.
