(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import ZArith OrdersFacts Nnat NAxioms NSig.

(** * The interface [NSig.NType] implies the interface [NAxiomsSig] *)

Module NTypeIsNAxioms (Import NN : NType').

Hint Rewrite
 spec_0 spec_1 spec_2 spec_succ spec_add spec_mul spec_pred spec_sub
 spec_div spec_modulo spec_gcd spec_compare spec_eqb spec_ltb spec_leb
 spec_square spec_sqrt spec_log2 spec_max spec_min spec_pow_pos spec_pow_N
 spec_pow spec_even spec_odd spec_testbit spec_shiftl spec_shiftr
 spec_land spec_lor spec_ldiff spec_lxor spec_div2 spec_of_N
 : nsimpl.
Ltac nsimpl := autorewrite with nsimpl.
Ltac ncongruence := unfold eq, to_N; repeat red; intros; nsimpl; congruence.
Ltac zify := unfold eq, lt, le, to_N in *; nsimpl.
Ltac omega_pos n := generalize (spec_pos n); omega with *.

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
intros. zify. omega_pos n.
Qed.

Theorem one_succ : 1 == succ 0.
Proof.
now zify.
Qed.

Theorem two_succ : 2 == succ 1.
Proof.
now zify.
Qed.

Definition N_of_Z z := of_N (Z.to_N z).

Lemma spec_N_of_Z z : (0<=z)%Z -> [N_of_Z z] = z.
Proof.
 unfold N_of_Z. zify. apply Z2N.id.
Qed.

Section Induction.

Variable A : NN.t -> Prop.
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
unfold eq. rewrite spec_succ, 2 spec_N_of_Z; auto with zarith.
Qed.

Lemma B_holds : forall z : Z, (0 <= z)%Z -> B z.
Proof.
exact (natlike_ind B B0 BS).
Qed.

Theorem bi_induction : forall n, A n.
Proof.
intro n. setoid_replace n with (N_of_Z (to_Z n)).
apply B_holds. apply spec_pos.
red. now rewrite spec_N_of_Z by apply spec_pos.
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
intros. zify. omega_pos n.
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

Lemma eqb_eq x y : eqb x y = true <-> x == y.
Proof.
 zify. apply Z.eqb_eq.
Qed.

Lemma leb_le x y : leb x y = true <-> x <= y.
Proof.
 zify. apply Z.leb_le.
Qed.

Lemma ltb_lt x y : ltb x y = true <-> x < y.
Proof.
 zify. apply Z.ltb_lt.
Qed.

Lemma compare_eq_iff n m : compare n m = Eq <-> n == m.
Proof.
 intros. zify. apply Z.compare_eq_iff.
Qed.

Lemma compare_lt_iff n m : compare n m = Lt <-> n < m.
Proof.
 intros. zify. reflexivity.
Qed.

Lemma compare_le_iff n m : compare n m <> Gt <-> n <= m.
Proof.
 intros. zify. reflexivity.
Qed.

Lemma compare_antisym n m : compare m n = CompOpp (compare n m).
Proof.
 intros. zify. apply Z.compare_antisym.
Qed.

Include BoolOrderFacts NN NN NN [no inline].

Instance compare_wd : Proper (eq ==> eq ==> Logic.eq) compare.
Proof.
intros x x' Hx y y' Hy. zify. now rewrite Hx, Hy.
Qed.

Instance eqb_wd : Proper (eq ==> eq ==> Logic.eq) eqb.
Proof.
intros x x' Hx y y' Hy. zify. now rewrite Hx, Hy.
Qed.

Instance ltb_wd : Proper (eq ==> eq ==> Logic.eq) ltb.
Proof.
intros x x' Hx y y' Hy. zify. now rewrite Hx, Hy.
Qed.

Instance leb_wd : Proper (eq ==> eq ==> Logic.eq) leb.
Proof.
intros x x' Hx y y' Hy. zify. now rewrite Hx, Hy.
Qed.

Instance lt_wd : Proper (eq ==> eq ==> iff) lt.
Proof.
intros x x' Hx y y' Hy; unfold lt; rewrite Hx, Hy; intuition.
Qed.

Theorem lt_succ_r : forall n m, n < succ m <-> n <= m.
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
 intros a b. zify. intros. now Z.nzsimpl.
Qed.

Lemma pow_neg_r : forall a b, b<0 -> a^b == 0.
Proof.
 intros a b. zify. intro Hb. exfalso. omega_pos b.
Qed.

Lemma pow_pow_N : forall a b, a^b == pow_N a (to_N b).
Proof.
 intros. zify. f_equal.
 now rewrite Z2N.id by apply spec_pos.
Qed.

Lemma pow_N_pow : forall a b, pow_N a b == a^(of_N b).
Proof.
 intros. now zify.
Qed.

Lemma pow_pos_N : forall a p, pow_pos a p == pow_N a (Npos p).
Proof.
 intros. now zify.
Qed.

(** Square *)

Lemma square_spec n : square n == n * n.
Proof.
 now zify.
Qed.

(** Sqrt *)

Lemma sqrt_spec : forall n, 0<=n ->
 (sqrt n)*(sqrt n) <= n /\ n < (succ (sqrt n))*(succ (sqrt n)).
Proof.
 intros n. zify. apply Z.sqrt_spec.
Qed.

Lemma sqrt_neg : forall n, n<0 -> sqrt n == 0.
Proof.
 intros n. zify. intro H. exfalso. omega_pos n.
Qed.

(** Log2 *)

Lemma log2_spec : forall n, 0<n ->
 2^(log2 n) <= n /\ n < 2^(succ (log2 n)).
Proof.
 intros n. zify. change (Z.log2 [n]+1)%Z with (Z.succ (Z.log2 [n])).
 apply Z.log2_spec.
Qed.

Lemma log2_nonpos : forall n, n<=0 -> log2 n == 0.
Proof.
 intros n. zify. apply Z.log2_nonpos.
Qed.

(** Even / Odd *)

Definition Even n := exists m, n == 2*m.
Definition Odd n := exists m, n == 2*m+1.

Lemma even_spec n : even n = true <-> Even n.
Proof.
 unfold Even. zify. rewrite Z.even_spec.
 split; intros (m,Hm).
 - exists (N_of_Z m). zify. rewrite spec_N_of_Z; trivial. omega_pos n.
 - exists [m]. revert Hm; now zify.
Qed.

Lemma odd_spec n : odd n = true <-> Odd n.
Proof.
 unfold Odd. zify. rewrite Z.odd_spec.
 split; intros (m,Hm).
 - exists (N_of_Z m). zify. rewrite spec_N_of_Z; trivial. omega_pos n.
 - exists [m]. revert Hm; now zify.
Qed.

(** Div / Mod *)

Program Instance div_wd : Proper (eq==>eq==>eq) div.
Program Instance mod_wd : Proper (eq==>eq==>eq) modulo.

Theorem div_mod : forall a b, ~b==0 -> a == b*(div a b) + (modulo a b).
Proof.
intros a b. zify. intros. apply Z.div_mod; auto.
Qed.

Theorem mod_bound_pos : forall a b, 0<=a -> 0<b ->
 0 <= modulo a b /\ modulo a b < b.
Proof.
intros a b. zify. apply Z.mod_bound_pos.
Qed.

(** Gcd *)

Definition divide n m := exists p, m == p*n.
Local Notation "( x | y )" := (divide x y) (at level 0).

Lemma spec_divide : forall n m, (n|m) <-> Z.divide [n] [m].
Proof.
 intros n m. split.
 - intros (p,H). exists [p]. revert H; now zify.
 - intros (z,H). exists (of_N (Z.abs_N z)). zify.
   rewrite N2Z.inj_abs_N.
   rewrite <- (Z.abs_eq [m]), <- (Z.abs_eq [n]) by apply spec_pos.
   now rewrite H, Z.abs_mul.
Qed.

Lemma gcd_divide_l : forall n m, (gcd n m | n).
Proof.
 intros n m. apply spec_divide. zify. apply Z.gcd_divide_l.
Qed.

Lemma gcd_divide_r : forall n m, (gcd n m | m).
Proof.
 intros n m. apply spec_divide. zify. apply Z.gcd_divide_r.
Qed.

Lemma gcd_greatest : forall n m p, (p|n) -> (p|m) -> (p|gcd n m).
Proof.
 intros n m p. rewrite !spec_divide. zify. apply Z.gcd_greatest.
Qed.

Lemma gcd_nonneg : forall n m, 0 <= gcd n m.
Proof.
 intros. zify. apply Z.gcd_nonneg.
Qed.

(** Bitwise operations *)

Program Instance testbit_wd : Proper (eq==>eq==>Logic.eq) testbit.

Lemma testbit_odd_0 : forall a, testbit (2*a+1) 0 = true.
Proof.
 intros. zify. apply Z.testbit_odd_0.
Qed.

Lemma testbit_even_0 : forall a, testbit (2*a) 0 = false.
Proof.
 intros. zify. apply Z.testbit_even_0.
Qed.

Lemma testbit_odd_succ : forall a n, 0<=n ->
 testbit (2*a+1) (succ n) = testbit a n.
Proof.
 intros a n. zify. apply Z.testbit_odd_succ.
Qed.

Lemma testbit_even_succ : forall a n, 0<=n ->
 testbit (2*a) (succ n) = testbit a n.
Proof.
 intros a n. zify. apply Z.testbit_even_succ.
Qed.

Lemma testbit_neg_r : forall a n, n<0 -> testbit a n = false.
Proof.
 intros a n. zify. apply Z.testbit_neg_r.
Qed.

Lemma shiftr_spec : forall a n m, 0<=m ->
 testbit (shiftr a n) m = testbit a (m+n).
Proof.
 intros a n m. zify. apply Z.shiftr_spec.
Qed.

Lemma shiftl_spec_high : forall a n m, 0<=m -> n<=m ->
 testbit (shiftl a n) m = testbit a (m-n).
Proof.
 intros a n m. zify. intros Hn H. rewrite Z.max_r by auto with zarith.
 now apply Z.shiftl_spec_high.
Qed.

Lemma shiftl_spec_low : forall a n m, m<n ->
 testbit (shiftl a n) m = false.
Proof.
 intros a n m. zify. intros H. now apply Z.shiftl_spec_low.
Qed.

Lemma land_spec : forall a b n,
 testbit (land a b) n = testbit a n && testbit b n.
Proof.
 intros a n m. zify. now apply Z.land_spec.
Qed.

Lemma lor_spec : forall a b n,
 testbit (lor a b) n = testbit a n || testbit b n.
Proof.
 intros a n m. zify. now apply Z.lor_spec.
Qed.

Lemma ldiff_spec : forall a b n,
 testbit (ldiff a b) n = testbit a n && negb (testbit b n).
Proof.
 intros a n m. zify. now apply Z.ldiff_spec.
Qed.

Lemma lxor_spec : forall a b n,
 testbit (lxor a b) n = xorb (testbit a n) (testbit b n).
Proof.
 intros a n m. zify. now apply Z.lxor_spec.
Qed.

Lemma div2_spec : forall a, div2 a == shiftr a 1.
Proof.
 intros a. zify. now apply Z.div2_spec.
Qed.

(** Recursion *)

Definition recursion (A : Type) (a : A) (f : NN.t -> A -> A) (n : NN.t) :=
  N.peano_rect (fun _ => A) a (fun n a => f (NN.of_N n) a) (NN.to_N n).
Arguments recursion [A] a f n.

Instance recursion_wd (A : Type) (Aeq : relation A) :
 Proper (Aeq ==> (eq==>Aeq==>Aeq) ==> eq ==> Aeq) (@recursion A).
Proof.
unfold eq.
intros a a' Eaa' f f' Eff' x x' Exx'.
unfold recursion.
unfold NN.to_N.
rewrite <- Exx'; clear x' Exx'.
induction (Z.to_N [x]) using N.peano_ind.
simpl; auto.
rewrite 2 N.peano_rect_succ. now apply Eff'.
Qed.

Theorem recursion_0 :
  forall (A : Type) (a : A) (f : NN.t -> A -> A), recursion a f 0 = a.
Proof.
intros A a f; unfold recursion, NN.to_N; rewrite NN.spec_0; simpl; auto.
Qed.

Theorem recursion_succ :
  forall (A : Type) (Aeq : relation A) (a : A) (f : NN.t -> A -> A),
    Aeq a a -> Proper (eq==>Aeq==>Aeq) f ->
      forall n, Aeq (recursion a f (succ n)) (f n (recursion a f n)).
Proof.
unfold eq, recursion; intros A Aeq a f EAaa f_wd n.
replace (to_N (succ n)) with (N.succ (to_N n)) by
 (zify; now rewrite <- Z2N.inj_succ by apply spec_pos).
rewrite N.peano_rect_succ.
apply f_wd; auto.
zify. now rewrite Z2N.id by apply spec_pos.
fold (recursion a f n). apply recursion_wd; auto. red; auto.
Qed.

End NTypeIsNAxioms.

Module NType_NAxioms (NN : NType)
 <: NAxiomsSig <: OrderFunctions NN <: HasMinMax NN
 := NN <+ NTypeIsNAxioms.
