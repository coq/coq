(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import ZArith.
Require Import Nnat.
Require Import NAxioms.
Require Import NSig.

(** * The interface [NSig.NType] implies the interface [NAxiomsSig] *)

Module NSig_NAxioms (N:NType) <: NAxiomsSig.

Delimit Scope IntScope with Int.
Bind Scope IntScope with N.t.
Open Local Scope IntScope.
Notation "[ x ]" := (N.to_Z x) : IntScope.
Infix "=="  := N.eq (at level 70) : IntScope.
Notation "0" := N.zero : IntScope.
Infix "+" := N.add : IntScope.
Infix "-" := N.sub : IntScope.
Infix "*" := N.mul : IntScope.

Module Export NZOrdAxiomsMod <: NZOrdAxiomsSig.
Module Export NZAxiomsMod <: NZAxiomsSig.

Definition NZ := N.t.
Definition NZeq := N.eq.
Definition NZ0 := N.zero.
Definition NZsucc := N.succ.
Definition NZpred := N.pred.
Definition NZadd := N.add.
Definition NZsub := N.sub.
Definition NZmul := N.mul.

Theorem NZeq_equiv : equiv N.t N.eq.
Proof.
repeat split; repeat red; intros; auto; congruence.
Qed.

Add Relation N.t N.eq
 reflexivity proved by (proj1 NZeq_equiv)
 symmetry proved by (proj2 (proj2 NZeq_equiv))
 transitivity proved by (proj1 (proj2 NZeq_equiv))
 as NZeq_rel.

Add Morphism NZsucc with signature N.eq ==> N.eq as NZsucc_wd.
Proof.
unfold N.eq; intros; rewrite 2 N.spec_succ; f_equal; auto.
Qed.

Add Morphism NZpred with signature N.eq ==> N.eq as NZpred_wd.
Proof.
unfold N.eq; intros.
generalize (N.spec_pos y) (N.spec_pos x) (N.spec_eq_bool x 0).
destruct N.eq_bool; rewrite N.spec_0; intros.
rewrite 2 N.spec_pred0; congruence.
rewrite 2 N.spec_pred; f_equal; auto; try omega.
Qed.

Add Morphism NZadd with signature N.eq ==> N.eq ==> N.eq as NZadd_wd.
Proof.
unfold N.eq; intros; rewrite 2 N.spec_add; f_equal; auto.
Qed.

Add Morphism NZsub with signature N.eq ==> N.eq ==> N.eq as NZsub_wd.
Proof.
unfold N.eq; intros x x' Hx y y' Hy.
destruct (Z_lt_le_dec [x] [y]).
rewrite 2 N.spec_sub0; f_equal; congruence.
rewrite 2 N.spec_sub; f_equal; congruence.
Qed.

Add Morphism NZmul with signature N.eq ==> N.eq ==> N.eq as NZmul_wd.
Proof.
unfold N.eq; intros; rewrite 2 N.spec_mul; f_equal; auto.
Qed.

Theorem NZpred_succ : forall n, N.pred (N.succ n) == n.
Proof.
unfold N.eq; intros.
rewrite N.spec_pred; rewrite N.spec_succ.
omega.
generalize (N.spec_pos n); omega.
Qed.

Definition N_of_Z z := N.of_N (Zabs_N z).

Section Induction.

Variable A : N.t -> Prop.
Hypothesis A_wd : predicate_wd N.eq A.
Hypothesis A0 : A 0.
Hypothesis AS : forall n, A n <-> A (N.succ n). 

Add Morphism A with signature N.eq ==> iff as A_morph.
Proof. apply A_wd. Qed.

Let B (z : Z) := A (N_of_Z z).

Lemma B0 : B 0.
Proof.
unfold B, N_of_Z; simpl.
rewrite <- (A_wd 0); auto.
red; rewrite N.spec_0, N.spec_of_N; auto.
Qed.

Lemma BS : forall z : Z, (0 <= z)%Z -> B z -> B (z + 1).
Proof.
intros z H1 H2.
unfold B in *. apply -> AS in H2.
setoid_replace (N_of_Z (z + 1)) with (N.succ (N_of_Z z)); auto.
unfold N.eq. rewrite N.spec_succ.
unfold N_of_Z.
rewrite 2 N.spec_of_N, 2 Z_of_N_abs, 2 Zabs_eq; auto with zarith.
Qed.

Lemma B_holds : forall z : Z, (0 <= z)%Z -> B z.
Proof.
exact (natlike_ind B B0 BS).
Qed.

Theorem NZinduction : forall n, A n.
Proof.
intro n. setoid_replace n with (N_of_Z (N.to_Z n)).
apply B_holds. apply N.spec_pos.
red; unfold N_of_Z.
rewrite N.spec_of_N, Z_of_N_abs, Zabs_eq; auto.
apply N.spec_pos.
Qed.

End Induction.

Theorem NZadd_0_l : forall n, 0 + n == n.
Proof.
intros; red; rewrite N.spec_add, N.spec_0; auto with zarith.
Qed.

Theorem NZadd_succ_l : forall n m, (N.succ n) + m == N.succ (n + m).
Proof.
intros; red; rewrite N.spec_add, 2 N.spec_succ, N.spec_add; auto with zarith.
Qed.

Theorem NZsub_0_r : forall n, n - 0 == n.
Proof.
intros; red; rewrite N.spec_sub; rewrite N.spec_0; auto with zarith.
apply N.spec_pos.
Qed.

Theorem NZsub_succ_r : forall n m, n - (N.succ m) == N.pred (n - m).
Proof.
intros; red.
destruct (Z_lt_le_dec [n] [N.succ m]) as [H|H].
rewrite N.spec_sub0; auto.
rewrite N.spec_succ in H.
rewrite N.spec_pred0; auto.
destruct (Z_eq_dec [n] [m]).
rewrite N.spec_sub; auto with zarith.
rewrite N.spec_sub0; auto with zarith.

rewrite N.spec_sub, N.spec_succ in *; auto.
rewrite N.spec_pred, N.spec_sub; auto with zarith.
rewrite N.spec_sub; auto with zarith.
Qed.

Theorem NZmul_0_l : forall n, 0 * n == 0.
Proof.
intros; red.
rewrite N.spec_mul, N.spec_0; auto with zarith.
Qed.

Theorem NZmul_succ_l : forall n m, (N.succ n) * m == n * m + m.
Proof.
intros; red.
rewrite N.spec_add, 2 N.spec_mul, N.spec_succ; ring.
Qed.

End NZAxiomsMod.

Definition NZlt := N.lt.
Definition NZle := N.le.
Definition NZmin := N.min.
Definition NZmax := N.max.

Infix "<=" := N.le : IntScope.
Infix "<" := N.lt : IntScope.

Lemma spec_compare_alt : forall x y, N.compare x y = ([x] ?= [y])%Z.
Proof.
 intros; generalize (N.spec_compare x y).
 destruct (N.compare x y); auto.
 intros H; rewrite H; symmetry; apply Zcompare_refl.
Qed.

Lemma spec_lt : forall x y, (x<y) <-> ([x]<[y])%Z.
Proof.
 intros; unfold N.lt, Zlt; rewrite spec_compare_alt; intuition.
Qed.

Lemma spec_le : forall x y, (x<=y) <-> ([x]<=[y])%Z.
Proof.
 intros; unfold N.le, Zle; rewrite spec_compare_alt; intuition.
Qed.

Lemma spec_min : forall x y, [N.min x y] = Zmin [x] [y].
Proof.
 intros; unfold N.min, Zmin.
 rewrite spec_compare_alt; destruct Zcompare; auto.
Qed.

Lemma spec_max : forall x y, [N.max x y] = Zmax [x] [y].
Proof.
 intros; unfold N.max, Zmax.
 rewrite spec_compare_alt; destruct Zcompare; auto.
Qed.

Add Morphism N.compare with signature N.eq ==> N.eq ==> (@eq comparison) as compare_wd.
Proof. 
intros x x' Hx y y' Hy.
rewrite 2 spec_compare_alt. unfold N.eq in *. rewrite Hx, Hy; intuition.
Qed.

Add Morphism N.lt with signature N.eq ==> N.eq ==> iff as NZlt_wd.
Proof.
intros x x' Hx y y' Hy; unfold N.lt; rewrite Hx, Hy; intuition.
Qed.

Add Morphism N.le with signature N.eq ==> N.eq ==> iff as NZle_wd.
Proof.
intros x x' Hx y y' Hy; unfold N.le; rewrite Hx, Hy; intuition.
Qed.

Add Morphism N.min with signature N.eq ==> N.eq ==> N.eq as NZmin_wd.
Proof.
intros; red; rewrite 2 spec_min; congruence.
Qed.

Add Morphism N.max with signature N.eq ==> N.eq ==> N.eq as NZmax_wd.
Proof.
intros; red; rewrite 2 spec_max; congruence.
Qed.

Theorem NZlt_eq_cases : forall n m, n <= m <-> n < m \/ n == m.
Proof.
intros.
unfold N.eq; rewrite spec_lt, spec_le; omega.
Qed.

Theorem NZlt_irrefl : forall n, ~ n < n.
Proof.
intros; rewrite spec_lt; auto with zarith.
Qed.

Theorem NZlt_succ_r : forall n m, n < (N.succ m) <-> n <= m.
Proof.
intros; rewrite spec_lt, spec_le, N.spec_succ; omega.
Qed.

Theorem NZmin_l : forall n m, n <= m -> N.min n m == n.
Proof.
intros n m; unfold N.eq; rewrite spec_le, spec_min.
generalize (Zmin_spec [n] [m]); omega.
Qed.

Theorem NZmin_r : forall n m, m <= n -> N.min n m == m.
Proof.
intros n m; unfold N.eq; rewrite spec_le, spec_min.
generalize (Zmin_spec [n] [m]); omega.
Qed.

Theorem NZmax_l : forall n m, m <= n -> N.max n m == n.
Proof.
intros n m; unfold N.eq; rewrite spec_le, spec_max.
generalize (Zmax_spec [n] [m]); omega.
Qed.

Theorem NZmax_r : forall n m, n <= m -> N.max n m == m.
Proof.
intros n m; unfold N.eq; rewrite spec_le, spec_max.
generalize (Zmax_spec [n] [m]); omega.
Qed.

End NZOrdAxiomsMod.

Theorem pred_0 : N.pred 0 == 0.
Proof.
red; rewrite N.spec_pred0; rewrite N.spec_0; auto.
Qed.

Definition recursion (A : Type) (a : A) (f : N.t -> A -> A) (n : N.t) :=
  Nrect (fun _ => A) a (fun n a => f (N.of_N n) a) (N.to_N n).
Implicit Arguments recursion [A].

Theorem recursion_wd :
forall (A : Type) (Aeq : relation A),
  forall a a' : A, Aeq a a' ->
    forall f f' : N.t -> A -> A, fun2_eq N.eq Aeq Aeq f f' ->
      forall x x' : N.t, x == x' ->
        Aeq (recursion a f x) (recursion a' f' x').
Proof.
unfold fun2_wd, N.eq, fun2_eq.
intros A Aeq a a' Eaa' f f' Eff' x x' Exx'.
unfold recursion.
unfold N.to_N.
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
  forall (A : Type) (a : A) (f : N.t -> A -> A), recursion a f 0 = a.
Proof.
intros A a f; unfold recursion, N.to_N; rewrite N.spec_0; simpl; auto.
Qed.

Theorem recursion_succ :
  forall (A : Type) (Aeq : relation A) (a : A) (f : N.t -> A -> A),
    Aeq a a -> fun2_wd N.eq Aeq Aeq f ->
      forall n, Aeq (recursion a f (N.succ n)) (f n (recursion a f n)).
Proof.
unfold N.eq, recursion, fun2_wd; intros A Aeq a f EAaa f_wd n.
replace (N.to_N (N.succ n)) with (Nsucc (N.to_N n)).
rewrite Nrect_step.
apply f_wd; auto.
unfold N.to_N.
rewrite N.spec_of_N, Z_of_N_abs, Zabs_eq; auto.
 apply N.spec_pos.

fold (recursion a f n).
apply recursion_wd; auto.
red; auto.
red; auto.
unfold N.to_N.

rewrite N.spec_succ.
change ([n]+1)%Z with (Zsucc [n]).
apply Z_of_N_eq_rev.
rewrite Z_of_N_succ.
rewrite 2 Z_of_N_abs.
rewrite 2 Zabs_eq; auto.
generalize (N.spec_pos n); auto with zarith.
apply N.spec_pos; auto.
Qed.

End NSig_NAxioms.
