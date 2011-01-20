(************************************************************************)

(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import ZArith Nnat Ndigits NAxioms NDiv NSig.

(** * The interface [NSig.NType] implies the interface [NAxiomsSig] *)

Module NTypeIsNAxioms (Import N : NType').

Hint Rewrite
 spec_0 spec_1 spec_2 spec_succ spec_add spec_mul spec_pred spec_sub
 spec_div spec_modulo spec_gcd spec_compare spec_eq_bool spec_sqrt
 spec_log2 spec_max spec_min spec_pow_pos spec_pow_N spec_pow
 spec_even spec_odd spec_testbit spec_shiftl spec_shiftr
 spec_land spec_lor spec_ldiff spec_lxor spec_div2 spec_of_N
 : nsimpl.
Ltac nsimpl := autorewrite with nsimpl.
Ltac ncongruence := unfold eq, to_N; repeat red; intros; nsimpl; congruence.
Ltac zify := unfold eq, lt, le, to_N in *; nsimpl.

Local Obligation Tactic := ncongruence.

Instance eq_equiv : Equivalence eq.
Proof. unfold eq. firstorder. Qed.

Program Instance succ_wd : Proper (eq==>eq) succ.
Program Instance pred_wd : Proper (eq==>eq) pred.
Program Instance add_wd : Proper (eq==>eq==>eq) add.
Program Instance sub_wd : Proper (eq==>eq==>eq) sub.
Program Instance mul_wd : Proper (eq==>eq==>eq) mul.

Theorem pred_succ : forall n, pred (succ n) == n.
Proof.
intros. zify. generalize (spec_pos n); omega with *.
Qed.

Theorem one_succ : 1 == succ 0.
Proof.
now zify.
Qed.

Theorem two_succ : 2 == succ 1.
Proof.
now zify.
Qed.

Definition N_of_Z z := of_N (Zabs_N z).

Section Induction.

Variable A : N.t -> Prop.
Hypothesis A_wd : Proper (eq==>iff) A.
Hypothesis A0 : A 0.
Hypothesis AS : forall n, A n <-> A (succ n).

Let B (z : Z) := A (N_of_Z z).

Lemma B0 : B 0.
Proof.
unfold B, N_of_Z; simpl.
rewrite <- (A_wd 0); auto.
red; rewrite spec_0, spec_of_N; auto.
Qed.

Lemma BS : forall z : Z, (0 <= z)%Z -> B z -> B (z + 1).
Proof.
intros z H1 H2.
unfold B in *. apply -> AS in H2.
setoid_replace (N_of_Z (z + 1)) with (succ (N_of_Z z)); auto.
unfold eq. rewrite spec_succ.
unfold N_of_Z.
rewrite 2 spec_of_N, 2 Z_of_N_abs, 2 Zabs_eq; auto with zarith.
Qed.

Lemma B_holds : forall z : Z, (0 <= z)%Z -> B z.
Proof.
exact (natlike_ind B B0 BS).
Qed.

Theorem bi_induction : forall n, A n.
Proof.
intro n. setoid_replace n with (N_of_Z (to_Z n)).
apply B_holds. apply spec_pos.
red; unfold N_of_Z.
rewrite spec_of_N, Z_of_N_abs, Zabs_eq; auto.
apply spec_pos.
Qed.

End Induction.

Theorem add_0_l : forall n, 0 + n == n.
Proof.
intros. zify. auto with zarith.
Qed.

Theorem add_succ_l : forall n m, (succ n) + m == succ (n + m).
Proof.
intros. zify. auto with zarith.
Qed.

Theorem sub_0_r : forall n, n - 0 == n.
Proof.
intros. zify. generalize (spec_pos n); omega with *.
Qed.

Theorem sub_succ_r : forall n m, n - (succ m) == pred (n - m).
Proof.
intros. zify. omega with *.
Qed.

Theorem mul_0_l : forall n, 0 * n == 0.
Proof.
intros. zify. auto with zarith.
Qed.

Theorem mul_succ_l : forall n m, (succ n) * m == n * m + m.
Proof.
intros. zify. ring.
Qed.

(** Order *)

Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
Proof.
 intros. zify. destruct (Zcompare_spec [x] [y]); auto.
Qed.

Definition eqb := eq_bool.

Lemma eqb_eq : forall x y, eq_bool x y = true <-> x == y.
Proof.
 intros. zify. symmetry. apply Zeq_is_eq_bool.
Qed.

Instance compare_wd : Proper (eq ==> eq ==> Logic.eq) compare.
Proof.
intros x x' Hx y y' Hy. rewrite 2 spec_compare, Hx, Hy; intuition.
Qed.

Instance lt_wd : Proper (eq ==> eq ==> iff) lt.
Proof.
intros x x' Hx y y' Hy; unfold lt; rewrite Hx, Hy; intuition.
Qed.

Theorem lt_eq_cases : forall n m, n <= m <-> n < m \/ n == m.
Proof.
intros. zify. omega.
Qed.

Theorem lt_irrefl : forall n, ~ n < n.
Proof.
intros. zify. omega.
Qed.

Theorem lt_succ_r : forall n m, n < (succ m) <-> n <= m.
Proof.
intros. zify. omega.
Qed.

Theorem min_l : forall n m, n <= m -> min n m == n.
Proof.
intros n m. zify. omega with *.
Qed.

Theorem min_r : forall n m, m <= n -> min n m == m.
Proof.
intros n m. zify. omega with *.
Qed.

Theorem max_l : forall n m, m <= n -> max n m == n.
Proof.
intros n m. zify. omega with *.
Qed.

Theorem max_r : forall n m, n <= m -> max n m == m.
Proof.
intros n m. zify. omega with *.
Qed.

(** Properties specific to natural numbers, not integers. *)

Theorem pred_0 : pred 0 == 0.
Proof.
zify. auto.
Qed.

(** Power *)

Program Instance pow_wd : Proper (eq==>eq==>eq) pow.

Lemma pow_0_r : forall a, a^0 == 1.
Proof.
 intros. now zify.
Qed.

Lemma pow_succ_r : forall a b, 0<=b -> a^(succ b) == a * a^b.
Proof.
 intros a b. zify. intro Hb.
 rewrite Zpower_exp; auto with zarith.
 simpl. unfold Zpower_pos; simpl. ring.
Qed.

Lemma pow_neg_r : forall a b, b<0 -> a^b == 0.
Proof.
 intros a b. zify. intro Hb. exfalso.
 generalize (spec_pos b); omega.
Qed.

Lemma pow_pow_N : forall a b, a^b == pow_N a (to_N b).
Proof.
 intros. zify. f_equal.
 now rewrite Z_of_N_abs, Zabs_eq by apply spec_pos.
Qed.

Lemma pow_N_pow : forall a b, pow_N a b == a^(of_N b).
Proof.
 intros. now zify.
Qed.

Lemma pow_pos_N : forall a p, pow_pos a p == pow_N a (Npos p).
Proof.
 intros. now zify.
Qed.

(** Sqrt *)

Lemma sqrt_spec : forall n, 0<=n ->
 (sqrt n)*(sqrt n) <= n /\ n < (succ (sqrt n))*(succ (sqrt n)).
Proof.
 intros n. zify. apply Zsqrt_spec.
Qed.

Lemma sqrt_neg : forall n, n<0 -> sqrt n == 0.
Proof.
 intros n. zify. intro H. exfalso.
 generalize (spec_pos n); omega.
Qed.

(** Log2 *)

Lemma log2_spec : forall n, 0<n ->
 2^(log2 n) <= n /\ n < 2^(succ (log2 n)).
Proof.
 intros n. zify. change (Zlog2 [n]+1)%Z with (Zsucc (Zlog2 [n])).
 apply Zlog2_spec.
Qed.

Lemma log2_nonpos : forall n, n<=0 -> log2 n == 0.
Proof.
 intros n. zify. apply Zlog2_nonpos.
Qed.

(** Even / Odd *)

Definition Even n := exists m, n == 2*m.
Definition Odd n := exists m, n == 2*m+1.

Lemma even_spec : forall n, even n = true <-> Even n.
Proof.
 intros n. unfold Even. zify.
 rewrite Zeven_bool_iff, Zeven_ex_iff.
 split; intros (m,Hm).
 exists (of_N (Zabs_N m)).
 zify. rewrite Z_of_N_abs, Zabs_eq; trivial.
 generalize (spec_pos n); auto with zarith.
 exists [m]. revert Hm. now zify.
Qed.

Lemma odd_spec : forall n, odd n = true <-> Odd n.
Proof.
 intros n. unfold Odd. zify.
 rewrite Zodd_bool_iff, Zodd_ex_iff.
 split; intros (m,Hm).
 exists (of_N (Zabs_N m)).
 zify. rewrite Z_of_N_abs, Zabs_eq; trivial.
 generalize (spec_pos n); auto with zarith.
 exists [m]. revert Hm. now zify.
Qed.

(** Div / Mod *)

Program Instance div_wd : Proper (eq==>eq==>eq) div.
Program Instance mod_wd : Proper (eq==>eq==>eq) modulo.

Theorem div_mod : forall a b, ~b==0 -> a == b*(div a b) + (modulo a b).
Proof.
intros a b. zify. intros. apply Z_div_mod_eq_full; auto.
Qed.

Theorem mod_bound_pos : forall a b, 0<=a -> 0<b ->
 0 <= modulo a b /\ modulo a b < b.
Proof.
intros a b. zify. apply Z.mod_bound_pos.
Qed.

(** Gcd *)

Definition divide n m := exists p, n*p == m.
Local Notation "( x | y )" := (divide x y) (at level 0).

Lemma spec_divide : forall n m, (n|m) <-> Zdivide' [n] [m].
Proof.
 intros n m. split.
 intros (p,H). exists [p]. revert H; now zify.
 intros (z,H). exists (of_N (Zabs_N z)). zify.
 rewrite Z_of_N_abs.
 rewrite <- (Zabs_eq [n]) by apply spec_pos.
 rewrite <- Zabs_Zmult, H.
 apply Zabs_eq, spec_pos.
Qed.

Lemma gcd_divide_l : forall n m, (gcd n m | n).
Proof.
 intros n m. apply spec_divide. zify. apply Zgcd_divide_l.
Qed.

Lemma gcd_divide_r : forall n m, (gcd n m | m).
Proof.
 intros n m. apply spec_divide. zify. apply Zgcd_divide_r.
Qed.

Lemma gcd_greatest : forall n m p, (p|n) -> (p|m) -> (p|gcd n m).
Proof.
 intros n m p. rewrite !spec_divide. zify. apply Zgcd_greatest.
Qed.

Lemma gcd_nonneg : forall n m, 0 <= gcd n m.
Proof.
 intros. zify. apply Zgcd_nonneg.
Qed.

(** Bitwise operations *)

Program Instance testbit_wd : Proper (eq==>eq==>Logic.eq) testbit.

Lemma testbit_odd_0 : forall a, testbit (2*a+1) 0 = true.
Proof.
 intros. zify. apply Ztestbit_odd_0.
Qed.

Lemma testbit_even_0 : forall a, testbit (2*a) 0 = false.
Proof.
 intros. zify. apply Ztestbit_even_0.
Qed.

Lemma testbit_odd_succ : forall a n, 0<=n ->
 testbit (2*a+1) (succ n) = testbit a n.
Proof.
 intros a n. zify. apply Ztestbit_odd_succ.
Qed.

Lemma testbit_even_succ : forall a n, 0<=n ->
 testbit (2*a) (succ n) = testbit a n.
Proof.
 intros a n. zify. apply Ztestbit_even_succ.
Qed.

Lemma testbit_neg_r : forall a n, n<0 -> testbit a n = false.
Proof.
 intros a n. zify. apply Ztestbit_neg_r.
Qed.

Lemma shiftr_spec : forall a n m, 0<=m ->
 testbit (shiftr a n) m = testbit a (m+n).
Proof.
 intros a n m. zify. apply Zshiftr_spec.
Qed.

Lemma shiftl_spec_high : forall a n m, 0<=m -> n<=m ->
 testbit (shiftl a n) m = testbit a (m-n).
Proof.
 intros a n m. zify. intros Hn H. rewrite Zmax_r by auto with zarith.
 now apply Zshiftl_spec_high.
Qed.

Lemma shiftl_spec_low : forall a n m, m<n ->
 testbit (shiftl a n) m = false.
Proof.
 intros a n m. zify. intros H. now apply Zshiftl_spec_low.
Qed.

Lemma land_spec : forall a b n,
 testbit (land a b) n = testbit a n && testbit b n.
Proof.
 intros a n m. zify. now apply Zand_spec.
Qed.

Lemma lor_spec : forall a b n,
 testbit (lor a b) n = testbit a n || testbit b n.
Proof.
 intros a n m. zify. now apply Zor_spec.
Qed.

Lemma ldiff_spec : forall a b n,
 testbit (ldiff a b) n = testbit a n && negb (testbit b n).
Proof.
 intros a n m. zify. now apply Zdiff_spec.
Qed.

Lemma lxor_spec : forall a b n,
 testbit (lxor a b) n = xorb (testbit a n) (testbit b n).
Proof.
 intros a n m. zify. now apply Zxor_spec.
Qed.

Lemma div2_spec : forall a, div2 a == shiftr a 1.
Proof.
 intros a. zify. now apply Zdiv2_spec.
Qed.

(** Recursion *)

Definition recursion (A : Type) (a : A) (f : N.t -> A -> A) (n : N.t) :=
  Nrect (fun _ => A) a (fun n a => f (N.of_N n) a) (N.to_N n).
Implicit Arguments recursion [A].

Instance recursion_wd (A : Type) (Aeq : relation A) :
 Proper (Aeq ==> (eq==>Aeq==>Aeq) ==> eq ==> Aeq) (@recursion A).
Proof.
unfold eq.
intros a a' Eaa' f f' Eff' x x' Exx'.
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
    Aeq a a -> Proper (eq==>Aeq==>Aeq) f ->
      forall n, Aeq (recursion a f (succ n)) (f n (recursion a f n)).
Proof.
unfold N.eq, recursion; intros A Aeq a f EAaa f_wd n.
replace (N.to_N (succ n)) with (Nsucc (N.to_N n)).
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
generalize (spec_pos n); auto with zarith.
apply spec_pos; auto.
Qed.

End NTypeIsNAxioms.

Module NType_NAxioms (N : NType)
 <: NAxiomsSig <: HasCompare N <: HasEqBool N <: HasMinMax N
 := N <+ NTypeIsNAxioms.
