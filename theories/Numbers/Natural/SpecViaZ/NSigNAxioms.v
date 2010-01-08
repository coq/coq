(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import ZArith Nnat NAxioms NDiv NSig.

(** * The interface [NSig.NType] implies the interface [NAxiomsSig] *)

Module NSig_NAxioms (N:NType) <: NAxiomsSig <: NDivSig.

Delimit Scope NumScope with Num.
Bind Scope NumScope with N.t.
Local Open Scope NumScope.
Local Notation "[ x ]" := (N.to_Z x) : NumScope.
Local Infix "=="  := N.eq (at level 70) : NumScope.
Local Notation "0" := N.zero : NumScope.
Local Infix "+" := N.add : NumScope.
Local Infix "-" := N.sub : NumScope.
Local Infix "*" := N.mul : NumScope.

Hint Rewrite
 N.spec_0 N.spec_succ N.spec_add N.spec_mul N.spec_pred N.spec_sub
 N.spec_div N.spec_modulo : num.
Ltac nsimpl := autorewrite with num.
Ltac ncongruence := unfold N.eq; repeat red; intros; nsimpl; congruence.

Obligation Tactic := ncongruence.

Instance eq_equiv : Equivalence N.eq.
Proof. unfold N.eq. firstorder. Qed.

Program Instance succ_wd : Proper (N.eq==>N.eq) N.succ.
Program Instance pred_wd : Proper (N.eq==>N.eq) N.pred.
Program Instance add_wd : Proper (N.eq==>N.eq==>N.eq) N.add.
Program Instance sub_wd : Proper (N.eq==>N.eq==>N.eq) N.sub.
Program Instance mul_wd : Proper (N.eq==>N.eq==>N.eq) N.mul.

Theorem pred_succ : forall n, N.pred (N.succ n) == n.
Proof.
unfold N.eq; repeat red; intros.
rewrite N.spec_pred; rewrite N.spec_succ.
generalize (N.spec_pos n); omega with *.
Qed.

Definition N_of_Z z := N.of_N (Zabs_N z).

Section Induction.

Variable A : N.t -> Prop.
Hypothesis A_wd : Proper (N.eq==>iff) A.
Hypothesis A0 : A 0.
Hypothesis AS : forall n, A n <-> A (N.succ n).

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

Theorem bi_induction : forall n, A n.
Proof.
intro n. setoid_replace n with (N_of_Z (N.to_Z n)).
apply B_holds. apply N.spec_pos.
red; unfold N_of_Z.
rewrite N.spec_of_N, Z_of_N_abs, Zabs_eq; auto.
apply N.spec_pos.
Qed.

End Induction.

Theorem add_0_l : forall n, 0 + n == n.
Proof.
intros; red; nsimpl; auto with zarith.
Qed.

Theorem add_succ_l : forall n m, (N.succ n) + m == N.succ (n + m).
Proof.
intros; red; nsimpl; auto with zarith.
Qed.

Theorem sub_0_r : forall n, n - 0 == n.
Proof.
intros; red; nsimpl. generalize (N.spec_pos n); omega with *.
Qed.

Theorem sub_succ_r : forall n m, n - (N.succ m) == N.pred (n - m).
Proof.
intros; red; nsimpl. omega with *.
Qed.

Theorem mul_0_l : forall n, 0 * n == 0.
Proof.
intros; red; nsimpl; auto with zarith.
Qed.

Theorem mul_succ_l : forall n m, (N.succ n) * m == n * m + m.
Proof.
intros; red; nsimpl. ring.
Qed.

(** Order *)

Infix "<=" := N.le : NumScope.
Infix "<" := N.lt : NumScope.

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

Instance compare_wd : Proper (N.eq ==> N.eq ==> eq) N.compare.
Proof.
intros x x' Hx y y' Hy.
rewrite 2 spec_compare_alt. unfold N.eq in *. rewrite Hx, Hy; intuition.
Qed.

Instance lt_wd : Proper (N.eq ==> N.eq ==> iff) N.lt.
Proof.
intros x x' Hx y y' Hy; unfold N.lt; rewrite Hx, Hy; intuition.
Qed.

Theorem lt_eq_cases : forall n m, n <= m <-> n < m \/ n == m.
Proof.
intros.
unfold N.eq; rewrite spec_lt, spec_le; omega.
Qed.

Theorem lt_irrefl : forall n, ~ n < n.
Proof.
intros; rewrite spec_lt; auto with zarith.
Qed.

Theorem lt_succ_r : forall n m, n < (N.succ m) <-> n <= m.
Proof.
intros; rewrite spec_lt, spec_le, N.spec_succ; omega.
Qed.

Theorem min_l : forall n m, n <= m -> N.min n m == n.
Proof.
intros n m; red; rewrite spec_le, spec_min; omega with *.
Qed.

Theorem min_r : forall n m, m <= n -> N.min n m == m.
Proof.
intros n m; red; rewrite spec_le, spec_min; omega with *.
Qed.

Theorem max_l : forall n m, m <= n -> N.max n m == n.
Proof.
intros n m; red; rewrite spec_le, spec_max; omega with *.
Qed.

Theorem max_r : forall n m, n <= m -> N.max n m == m.
Proof.
intros n m; red; rewrite spec_le, spec_max; omega with *.
Qed.

(** Properties specific to natural numbers, not integers. *)

Theorem pred_0 : N.pred 0 == 0.
Proof.
red; nsimpl; auto.
Qed.

Program Instance div_wd : Proper (N.eq==>N.eq==>N.eq) N.div.
Program Instance mod_wd : Proper (N.eq==>N.eq==>N.eq) N.modulo.

Theorem div_mod : forall a b, ~b==0 -> a == b*(N.div a b) + (N.modulo a b).
Proof.
intros a b. unfold N.eq. nsimpl. intros.
apply Z_div_mod_eq_full; auto.
Qed.

Theorem mod_upper_bound : forall a b, ~b==0 -> N.modulo a b < b.
Proof.
intros a b. unfold N.eq. rewrite spec_lt. nsimpl. intros.
destruct (Z_mod_lt [a] [b]); auto.
generalize (N.spec_pos b); auto with zarith.
Qed.

Definition recursion (A : Type) (a : A) (f : N.t -> A -> A) (n : N.t) :=
  Nrect (fun _ => A) a (fun n a => f (N.of_N n) a) (N.to_N n).
Implicit Arguments recursion [A].

Instance recursion_wd (A : Type) (Aeq : relation A) :
 Proper (Aeq ==> (N.eq==>Aeq==>Aeq) ==> N.eq ==> Aeq) (@recursion A).
Proof.
unfold N.eq.
intros A Aeq a a' Eaa' f f' Eff' x x' Exx'.
unfold recursion.
unfold N.to_N.
rewrite <- Exx'; clear x' Exx'.
replace (Zabs_N [x]) with (N_of_nat (Zabs_nat [x])).
induction (Zabs_nat [x]).
simpl; auto.
rewrite N_of_S, 2 Nrect_step; auto. apply Eff'; auto.
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
    Aeq a a -> Proper (N.eq==>Aeq==>Aeq) f ->
      forall n, Aeq (recursion a f (N.succ n)) (f n (recursion a f n)).
Proof.
unfold N.eq, recursion; intros A Aeq a f EAaa f_wd n.
replace (N.to_N (N.succ n)) with (Nsucc (N.to_N n)).
rewrite Nrect_step.
apply f_wd; auto.
unfold N.to_N.
rewrite N.spec_of_N, Z_of_N_abs, Zabs_eq; auto.
 apply N.spec_pos.

fold (recursion a f n).
apply recursion_wd; auto.
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

(** The instantiation of operations.
    Placing them at the very end avoids having indirections in above lemmas. *)

Definition t := N.t.
Definition eq := N.eq.
Definition zero := N.zero.
Definition succ := N.succ.
Definition pred := N.pred.
Definition add := N.add.
Definition sub := N.sub.
Definition mul := N.mul.
Definition lt := N.lt.
Definition le := N.le.
Definition min := N.min.
Definition max := N.max.
Definition div := N.div.
Definition modulo := N.modulo.

End NSig_NAxioms.
