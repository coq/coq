(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Bool ZArith OrdersFacts Nnat ZAxioms ZSig.

(** * The interface [ZSig.ZType] implies the interface [ZAxiomsSig] *)

Module ZTypeIsZAxioms (Import ZZ : ZType').

Hint Rewrite
 spec_0 spec_1 spec_2 spec_add spec_sub spec_pred spec_succ
 spec_mul spec_opp spec_of_Z spec_div spec_modulo spec_square spec_sqrt
 spec_compare spec_eqb spec_ltb spec_leb spec_max spec_min
 spec_abs spec_sgn spec_pow spec_log2 spec_even spec_odd spec_gcd
 spec_quot spec_rem spec_testbit spec_shiftl spec_shiftr
 spec_land spec_lor spec_ldiff spec_lxor spec_div2
 : zsimpl.

Ltac zsimpl := autorewrite with zsimpl.
Ltac zcongruence := repeat red; intros; zsimpl; congruence.
Ltac zify := unfold eq, lt, le in *; zsimpl.

Instance eq_equiv : Equivalence eq.
Proof. unfold eq. firstorder. Qed.

Local Obligation Tactic := zcongruence.

Program Instance succ_wd : Proper (eq ==> eq) succ.
Program Instance pred_wd : Proper (eq ==> eq) pred.
Program Instance add_wd : Proper (eq ==> eq ==> eq) add.
Program Instance sub_wd : Proper (eq ==> eq ==> eq) sub.
Program Instance mul_wd : Proper (eq ==> eq ==> eq) mul.

Theorem pred_succ : forall n, pred (succ n) == n.
Proof.
intros. zify. auto with zarith.
Qed.

Theorem one_succ : 1 == succ 0.
Proof.
now zify.
Qed.

Theorem two_succ : 2 == succ 1.
Proof.
now zify.
Qed.

Section Induction.

Variable A : ZZ.t -> Prop.
Hypothesis A_wd : Proper (eq==>iff) A.
Hypothesis A0 : A 0.
Hypothesis AS : forall n, A n <-> A (succ n).

Let B (z : Z) := A (of_Z z).

Lemma B0 : B 0.
Proof.
unfold B; simpl.
rewrite <- (A_wd 0); auto.
zify. auto.
Qed.

Lemma BS : forall z : Z, B z -> B (z + 1).
Proof.
intros z H.
unfold B in *. apply -> AS in H.
setoid_replace (of_Z (z + 1)) with (succ (of_Z z)); auto.
zify. auto.
Qed.

Lemma BP : forall z : Z, B z -> B (z - 1).
Proof.
intros z H.
unfold B in *. rewrite AS.
setoid_replace (succ (of_Z (z - 1))) with (of_Z z); auto.
zify. auto with zarith.
Qed.

Lemma B_holds : forall z : Z, B z.
Proof.
intros; destruct (Z_lt_le_dec 0 z).
apply natlike_ind; auto with zarith.
apply B0.
intros; apply BS; auto.
replace z with (-(-z))%Z in * by (auto with zarith).
remember (-z)%Z as z'.
pattern z'; apply natlike_ind.
apply B0.
intros; rewrite Z.opp_succ; unfold Z.pred; apply BP; auto.
subst z'; auto with zarith.
Qed.

Theorem bi_induction : forall n, A n.
Proof.
intro n. setoid_replace n with (of_Z (to_Z n)).
apply B_holds.
zify. auto.
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
intros. zify. auto with zarith.
Qed.

Theorem sub_succ_r : forall n m, n - (succ m) == pred (n - m).
Proof.
intros. zify. auto with zarith.
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

Include BoolOrderFacts ZZ ZZ ZZ [no inline].

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

(** Part specific to integers, not natural numbers *)

Theorem succ_pred : forall n, succ (pred n) == n.
Proof.
intros. zify. auto with zarith.
Qed.

(** Opp *)

Program Instance opp_wd : Proper (eq ==> eq) opp.

Theorem opp_0 : - 0 == 0.
Proof.
intros. zify. auto with zarith.
Qed.

Theorem opp_succ : forall n, - (succ n) == pred (- n).
Proof.
intros. zify. auto with zarith.
Qed.

(** Abs / Sgn *)

Theorem abs_eq : forall n, 0 <= n -> abs n == n.
Proof.
intros n. zify. omega with *.
Qed.

Theorem abs_neq : forall n, n <= 0 -> abs n == -n.
Proof.
intros n. zify. omega with *.
Qed.

Theorem sgn_null : forall n, n==0 -> sgn n == 0.
Proof.
intros n. zify. omega with *.
Qed.

Theorem sgn_pos : forall n, 0<n -> sgn n == 1.
Proof.
intros n. zify. omega with *.
Qed.

Theorem sgn_neg : forall n, n<0 -> sgn n == opp 1.
Proof.
intros n. zify. omega with *.
Qed.

(** Power *)

Program Instance pow_wd : Proper (eq==>eq==>eq) pow.

Lemma pow_0_r : forall a, a^0 == 1.
Proof.
 intros. now zify.
Qed.

Lemma pow_succ_r : forall a b, 0<=b -> a^(succ b) == a * a^b.
Proof.
 intros a b. zify. intros. now rewrite Z.add_1_r, Z.pow_succ_r.
Qed.

Lemma pow_neg_r : forall a b, b<0 -> a^b == 0.
Proof.
 intros a b. zify. intros Hb.
 destruct [b]; reflexivity || discriminate.
Qed.

Lemma pow_pow_N : forall a b, 0<=b -> a^b == pow_N a (Z.to_N (to_Z b)).
Proof.
 intros a b. zify. intros Hb. now rewrite spec_pow_N, Z2N.id.
Qed.

Lemma pow_pos_N : forall a p, pow_pos a p == pow_N a (Npos p).
Proof.
 intros a b. red. now rewrite spec_pow_N, spec_pow_pos.
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
 intros n. zify. apply Z.sqrt_neg.
Qed.

(** Log2 *)

Lemma log2_spec : forall n, 0<n ->
 2^(log2 n) <= n /\ n < 2^(succ (log2 n)).
Proof.
 intros n. zify. apply Z.log2_spec.
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
 - exists (of_Z m). now zify.
 - exists [m]. revert Hm. now zify.
Qed.

Lemma odd_spec n : odd n = true <-> Odd n.
Proof.
 unfold Odd. zify. rewrite Z.odd_spec.
 split; intros (m,Hm).
 - exists (of_Z m). now zify.
 - exists [m]. revert Hm. now zify.
Qed.

(** Div / Mod *)

Program Instance div_wd : Proper (eq==>eq==>eq) div.
Program Instance mod_wd : Proper (eq==>eq==>eq) modulo.

Theorem div_mod : forall a b, ~b==0 -> a == b*(div a b) + (modulo a b).
Proof.
intros a b. zify. intros. apply Z.div_mod; auto.
Qed.

Theorem mod_pos_bound :
 forall a b, 0 < b -> 0 <= modulo a b /\ modulo a b < b.
Proof.
intros a b. zify. intros. apply Z_mod_lt; auto with zarith.
Qed.

Theorem mod_neg_bound :
 forall a b, b < 0 -> b < modulo a b /\ modulo a b <= 0.
Proof.
intros a b. zify. intros. apply Z_mod_neg; auto with zarith.
Qed.

Definition mod_bound_pos :
 forall a b, 0<=a -> 0<b -> 0 <= modulo a b /\ modulo a b < b :=
 fun a b _ H => mod_pos_bound a b H.

(** Quot / Rem *)

Program Instance quot_wd : Proper (eq==>eq==>eq) quot.
Program Instance rem_wd : Proper (eq==>eq==>eq) rem.

Theorem quot_rem : forall a b, ~b==0 -> a == b*(quot a b) + rem a b.
Proof.
intros a b. zify. apply Z.quot_rem.
Qed.

Theorem rem_bound_pos :
 forall a b, 0<=a -> 0<b -> 0 <= rem a b /\ rem a b < b.
Proof.
intros a b. zify. apply Z.rem_bound_pos.
Qed.

Theorem rem_opp_l : forall a b, ~b==0 -> rem (-a) b == -(rem a b).
Proof.
intros a b. zify. apply Z.rem_opp_l.
Qed.

Theorem rem_opp_r : forall a b, ~b==0 -> rem a (-b) == rem a b.
Proof.
intros a b. zify. apply Z.rem_opp_r.
Qed.

(** Gcd *)

Definition divide n m := exists p, m == p*n.
Local Notation "( x | y )" := (divide x y) (at level 0).

Lemma spec_divide : forall n m, (n|m) <-> Z.divide [n] [m].
Proof.
 intros n m. split.
 - intros (p,H). exists [p]. revert H; now zify.
 - intros (z,H). exists (of_Z z). now zify.
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
 intros a n m. zify. intros Hn H.
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

End ZTypeIsZAxioms.

Module ZType_ZAxioms (ZZ : ZType)
 <: ZAxiomsSig <: OrderFunctions ZZ <: HasMinMax ZZ
 := ZZ <+ ZTypeIsZAxioms.
