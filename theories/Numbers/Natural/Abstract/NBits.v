(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Bool NAxioms NSub NPow NDiv NParity NLog.

(** Derived properties of bitwise operations *)

Module Type NBitsProp
 (Import A : NAxiomsSig')
 (Import B : NSubProp A)
 (Import C : NParityProp A B)
 (Import D : NPowProp A B C)
 (Import E : NDivProp A B)
 (Import F : NLog2Prop A B C D).

Include BoolEqualityFacts A.

Ltac order_nz := try apply pow_nonzero; order'.
Hint Rewrite div_0_l mod_0_l div_1_r mod_1_r : nz.

(** Some properties of power and division *)

Lemma pow_sub_r : forall a b c, a~=0 -> c<=b -> a^(b-c) == a^b / a^c.
Proof.
 intros a b c Ha H.
 apply div_unique with 0.
 generalize (pow_nonzero a c Ha) (le_0_l (a^c)); order'.
 nzsimpl. now rewrite <- pow_add_r, add_comm, sub_add.
Qed.

Lemma pow_div_l : forall a b c, b~=0 -> a mod b == 0 ->
 (a/b)^c == a^c / b^c.
Proof.
 intros a b c Hb H.
 apply div_unique with 0.
 generalize (pow_nonzero b c Hb) (le_0_l (b^c)); order'.
 nzsimpl. rewrite <- pow_mul_l. f_equiv. now apply div_exact.
Qed.

(** An injection from bits [true] and [false] to numbers 1 and 0.
    We declare it as a (local) coercion for shorter statements. *)

Definition b2n (b:bool) := if b then 1 else 0.
Local Coercion b2n : bool >-> t.

Instance b2n_proper : Proper (Logic.eq ==> eq) b2n.
Proof. solve_proper. Qed.

Lemma exists_div2 a : exists a' (b:bool), a == 2*a' + b.
Proof.
 elim (Even_or_Odd a); [intros (a',H)| intros (a',H)].
 exists a'. exists false. now nzsimpl.
 exists a'. exists true. now simpl.
Qed.

(** We can compact [testbit_odd_0] [testbit_even_0]
    [testbit_even_succ] [testbit_odd_succ] in only two lemmas. *)

Lemma testbit_0_r a (b:bool) : testbit (2*a+b) 0 = b.
Proof.
 destruct b; simpl; rewrite ?add_0_r.
 apply testbit_odd_0.
 apply testbit_even_0.
Qed.

Lemma testbit_succ_r a (b:bool) n :
 testbit (2*a+b) (succ n) = testbit a n.
Proof.
 destruct b; simpl; rewrite ?add_0_r.
 apply testbit_odd_succ, le_0_l.
 apply testbit_even_succ, le_0_l.
Qed.

(** Alternative characterisations of [testbit] *)

(** This concise equation could have been taken as specification
   for testbit in the interface, but it would have been hard to
   implement with little initial knowledge about div and mod *)

Lemma testbit_spec' a n : a.[n] == (a / 2^n) mod 2.
Proof.
 revert a. induct n.
 intros a. nzsimpl.
 destruct (exists_div2 a) as (a' & b & H). rewrite H at 1.
 rewrite testbit_0_r. apply mod_unique with a'; trivial.
 destruct b; order'.
 intros n IH a.
 destruct (exists_div2 a) as (a' & b & H). rewrite H at 1.
 rewrite testbit_succ_r, IH. f_equiv.
 rewrite pow_succ_r', <- div_div by order_nz. f_equiv.
 apply div_unique with b; trivial.
 destruct b; order'.
Qed.

(** This characterisation that uses only basic operations and
   power was initially taken as specification for testbit.
   We describe [a] as having a low part and a high part, with
   the corresponding bit in the middle. This characterisation
   is moderatly complex to implement, but also moderately
   usable... *)

Lemma testbit_spec a n :
  exists l h, 0<=l<2^n /\ a == l + (a.[n] + 2*h)*2^n.
Proof.
 exists (a mod 2^n). exists (a / 2^n / 2). split.
 split; [apply le_0_l | apply mod_upper_bound; order_nz].
 rewrite add_comm, mul_comm, (add_comm a.[n]).
 rewrite (div_mod a (2^n)) at 1 by order_nz. do 2 f_equiv.
 rewrite testbit_spec'. apply div_mod. order'.
Qed.

Lemma testbit_true : forall a n,
 a.[n] = true <-> (a / 2^n) mod 2 == 1.
Proof.
 intros a n.
 rewrite <- testbit_spec'; destruct a.[n]; split; simpl; now try order'.
Qed.

Lemma testbit_false : forall a n,
 a.[n] = false <-> (a / 2^n) mod 2 == 0.
Proof.
 intros a n.
 rewrite <- testbit_spec'; destruct a.[n]; split; simpl; now try order'.
Qed.

Lemma testbit_eqb : forall a n,
 a.[n] = eqb ((a / 2^n) mod 2) 1.
Proof.
 intros a n.
 apply eq_true_iff_eq. now rewrite testbit_true, eqb_eq.
Qed.

(** Results about the injection [b2n] *)

Lemma b2n_inj : forall (a0 b0:bool), a0 == b0 -> a0 = b0.
Proof.
 intros [|] [|]; simpl; trivial; order'.
Qed.

Lemma add_b2n_double_div2 : forall (a0:bool) a, (a0+2*a)/2 == a.
Proof.
 intros a0 a. rewrite mul_comm, div_add by order'.
 now rewrite div_small, add_0_l by (destruct a0; order').
Qed.

Lemma add_b2n_double_bit0 : forall (a0:bool) a, (a0+2*a).[0] = a0.
Proof.
 intros a0 a. apply b2n_inj.
 rewrite testbit_spec'. nzsimpl. rewrite mul_comm, mod_add by order'.
 now rewrite mod_small by (destruct a0; order').
Qed.

Lemma b2n_div2 : forall (a0:bool), a0/2 == 0.
Proof.
 intros a0. rewrite <- (add_b2n_double_div2 a0 0). now nzsimpl.
Qed.

Lemma b2n_bit0 : forall (a0:bool), a0.[0] = a0.
Proof.
 intros a0. rewrite <- (add_b2n_double_bit0 a0 0) at 2. now nzsimpl.
Qed.

(** The specification of testbit by low and high parts is complete *)

Lemma testbit_unique : forall a n (a0:bool) l h,
 l<2^n -> a == l + (a0 + 2*h)*2^n -> a.[n] = a0.
Proof.
 intros a n a0 l h Hl EQ.
 apply b2n_inj. rewrite testbit_spec' by trivial.
 symmetry. apply mod_unique with h. destruct a0; simpl; order'.
 symmetry. apply div_unique with l; trivial.
 now rewrite add_comm, (add_comm _ a0), mul_comm.
Qed.

(** All bits of number 0 are 0 *)

Lemma bits_0 : forall n, 0.[n] = false.
Proof.
 intros n. apply testbit_false. nzsimpl; order_nz.
Qed.

(** Various ways to refer to the lowest bit of a number *)

Lemma bit0_odd : forall a, a.[0] = odd a.
Proof.
 intros. symmetry.
 destruct (exists_div2 a) as (a' & b & EQ).
 rewrite EQ, testbit_0_r, add_comm, odd_add_mul_2.
 destruct b; simpl; apply odd_1 || apply odd_0.
Qed.

Lemma bit0_eqb : forall a, a.[0] = eqb (a mod 2) 1.
Proof.
 intros a. rewrite testbit_eqb. now nzsimpl.
Qed.

Lemma bit0_mod : forall a, a.[0] == a mod 2.
Proof.
 intros a. rewrite testbit_spec'. now nzsimpl.
Qed.

(** Hence testing a bit is equivalent to shifting and testing parity *)

Lemma testbit_odd : forall a n, a.[n] = odd (a>>n).
Proof.
 intros. now rewrite <- bit0_odd, shiftr_spec, add_0_l.
Qed.

(** [log2] gives the highest nonzero bit *)

Lemma bit_log2 : forall a, a~=0 -> a.[log2 a] = true.
Proof.
 intros a Ha.
 assert (Ha' : 0 < a) by (generalize (le_0_l a); order).
 destruct (log2_spec_alt a Ha') as (r & EQ & (_,Hr)).
 rewrite EQ at 1.
 rewrite testbit_true, add_comm.
 rewrite <- (mul_1_l (2^log2 a)) at 1.
 rewrite div_add by order_nz.
 rewrite div_small by trivial.
 rewrite add_0_l. apply mod_small. order'.
Qed.

Lemma bits_above_log2 : forall a n, log2 a < n ->
 a.[n] = false.
Proof.
 intros a n H.
 rewrite testbit_false.
 rewrite div_small. nzsimpl; order'.
 apply log2_lt_cancel. rewrite log2_pow2; trivial using le_0_l.
Qed.

(** Hence the number of bits of [a] is [1+log2 a]
    (see [Pos.size_nat] and [Pos.size]).
*)

(** Testing bits after division or multiplication by a power of two *)

Lemma div2_bits : forall a n, (a/2).[n] = a.[S n].
Proof.
 intros. apply eq_true_iff_eq.
 rewrite 2 testbit_true.
 rewrite pow_succ_r by apply le_0_l.
 now rewrite div_div by order_nz.
Qed.

Lemma div_pow2_bits : forall a n m, (a/2^n).[m] = a.[m+n].
Proof.
 intros a n. revert a. induct n.
 intros a m. now nzsimpl.
 intros n IH a m. nzsimpl; try apply le_0_l.
 rewrite <- div_div by order_nz.
 now rewrite IH, div2_bits.
Qed.

Lemma double_bits_succ : forall a n, (2*a).[S n] = a.[n].
Proof.
 intros. rewrite <- div2_bits. now rewrite mul_comm, div_mul by order'.
Qed.

Lemma mul_pow2_bits_add : forall a n m, (a*2^n).[m+n] = a.[m].
Proof.
 intros. rewrite <- div_pow2_bits. now rewrite div_mul by order_nz.
Qed.

Lemma mul_pow2_bits_high : forall a n m, n<=m -> (a*2^n).[m] = a.[m-n].
Proof.
 intros.
 rewrite <- (sub_add n m) at 1 by order'.
 now rewrite mul_pow2_bits_add.
Qed.

Lemma mul_pow2_bits_low : forall a n m, m<n -> (a*2^n).[m] = false.
Proof.
 intros. apply testbit_false.
 rewrite <- (sub_add m n) by order'. rewrite pow_add_r, mul_assoc.
 rewrite div_mul by order_nz.
 rewrite <- (succ_pred (n-m)). rewrite pow_succ_r.
 now rewrite (mul_comm 2), mul_assoc, mod_mul by order'.
 apply lt_le_pred.
 apply sub_gt in H. generalize (le_0_l (n-m)); order.
 now apply sub_gt.
Qed.

(** Selecting the low part of a number can be done by a modulo *)

Lemma mod_pow2_bits_high : forall a n m, n<=m ->
 (a mod 2^n).[m] = false.
Proof.
 intros a n m H.
 destruct (eq_0_gt_0_cases (a mod 2^n)) as [EQ|LT].
 now rewrite EQ, bits_0.
 apply bits_above_log2.
 apply lt_le_trans with n; trivial.
 apply log2_lt_pow2; trivial.
 apply mod_upper_bound; order_nz.
Qed.

Lemma mod_pow2_bits_low : forall a n m, m<n ->
 (a mod 2^n).[m] = a.[m].
Proof.
 intros a n m H.
 rewrite testbit_eqb.
 rewrite <- (mod_add _ (2^(P (n-m))*(a/2^n))) by order'.
 rewrite <- div_add by order_nz.
 rewrite (mul_comm _ 2), mul_assoc, <- pow_succ_r', succ_pred
   by now apply sub_gt.
 rewrite mul_comm, mul_assoc, <- pow_add_r, (add_comm m), sub_add
   by order.
 rewrite add_comm, <- div_mod by order_nz.
 symmetry. apply testbit_eqb.
Qed.

(** We now prove that having the same bits implies equality.
    For that we use a notion of equality over functional
    streams of bits. *)

Definition eqf (f g:t -> bool) := forall n:t, f n = g n.

Instance eqf_equiv : Equivalence eqf.
Proof.
 split; congruence.
Qed.

Local Infix "===" := eqf (at level 70, no associativity).

Instance testbit_eqf : Proper (eq==>eqf) testbit.
Proof.
 intros a a' Ha n. now rewrite Ha.
Qed.

(** Only zero corresponds to the always-false stream. *)

Lemma bits_inj_0 :
 forall a, (forall n, a.[n] = false) -> a == 0.
Proof.
 intros a H. destruct (eq_decidable a 0) as [EQ|NEQ]; trivial.
 apply bit_log2 in NEQ. now rewrite H in NEQ.
Qed.

(** If two numbers produce the same stream of bits, they are equal. *)

Lemma bits_inj : forall a b, testbit a === testbit b -> a == b.
Proof.
 intros a. pattern a.
 apply strong_right_induction with 0;[solve_proper|clear a|apply le_0_l].
 intros a _ IH b H.
 destruct (eq_0_gt_0_cases a) as [EQ|LT].
 rewrite EQ in H |- *. symmetry. apply bits_inj_0.
 intros n. now rewrite <- H, bits_0.
 rewrite (div_mod a 2), (div_mod b 2) by order'.
 f_equiv; [ | now rewrite <- 2 bit0_mod, H].
 f_equiv.
 apply IH; trivial using le_0_l.
 apply div_lt; order'.
 intro n. rewrite 2 div2_bits. apply H.
Qed.

Lemma bits_inj_iff : forall a b, testbit a === testbit b <-> a == b.
Proof.
 split. apply bits_inj. intros EQ; now rewrite EQ.
Qed.

Hint Rewrite lxor_spec lor_spec land_spec ldiff_spec bits_0 : bitwise.

Ltac bitwise := apply bits_inj; intros ?m; autorewrite with bitwise.

(** The streams of bits that correspond to a natural numbers are
  exactly the ones that are always 0 after some point *)

Lemma are_bits : forall (f:t->bool), Proper (eq==>Logic.eq) f ->
 ((exists n, f === testbit n) <->
  (exists k, forall m, k<=m -> f m = false)).
Proof.
 intros f Hf. split.
 intros (a,H).
  exists (S (log2 a)). intros m Hm. apply le_succ_l in Hm.
  rewrite H, bits_above_log2; trivial using lt_succ_diag_r.
 intros (k,Hk).
  revert f Hf Hk. induct k.
  intros f Hf H0.
  exists 0. intros m. rewrite bits_0, H0; trivial. apply le_0_l.
  intros k IH f Hf Hk.
  destruct (IH (fun m => f (S m))) as (n, Hn).
  solve_proper.
  intros m Hm. apply Hk. now rewrite <- succ_le_mono.
  exists (f 0 + 2*n). intros m.
  destruct (zero_or_succ m) as [Hm|(m', Hm)]; rewrite Hm.
  symmetry. apply add_b2n_double_bit0.
  rewrite Hn, <- div2_bits.
  rewrite mul_comm, div_add, b2n_div2, add_0_l; trivial. order'.
Qed.

(** Properties of shifts *)

Lemma shiftr_spec' : forall a n m, (a >> n).[m] = a.[m+n].
Proof.
 intros. apply shiftr_spec. apply le_0_l.
Qed.

Lemma shiftl_spec_high' : forall a n m, n<=m -> (a << n).[m] = a.[m-n].
Proof.
 intros. apply shiftl_spec_high; trivial. apply le_0_l.
Qed.

Lemma shiftr_div_pow2 : forall a n, a >> n == a / 2^n.
Proof.
 intros. bitwise. rewrite shiftr_spec'.
 symmetry. apply div_pow2_bits.
Qed.

Lemma shiftl_mul_pow2 : forall a n, a << n == a * 2^n.
Proof.
 intros. bitwise.
 destruct (le_gt_cases n m) as [H|H].
 now rewrite shiftl_spec_high', mul_pow2_bits_high.
 now rewrite shiftl_spec_low, mul_pow2_bits_low.
Qed.

Lemma shiftl_spec_alt : forall a n m, (a << n).[m+n] = a.[m].
Proof.
 intros. now rewrite shiftl_mul_pow2, mul_pow2_bits_add.
Qed.

Instance shiftr_wd : Proper (eq==>eq==>eq) shiftr.
Proof.
 intros a a' Ha b b' Hb. now rewrite 2 shiftr_div_pow2, Ha, Hb.
Qed.

Instance shiftl_wd : Proper (eq==>eq==>eq) shiftl.
Proof.
 intros a a' Ha b b' Hb. now rewrite 2 shiftl_mul_pow2, Ha, Hb.
Qed.

Lemma shiftl_shiftl : forall a n m,
 (a << n) << m == a << (n+m).
Proof.
 intros. now rewrite !shiftl_mul_pow2, pow_add_r, mul_assoc.
Qed.

Lemma shiftr_shiftr : forall a n m,
 (a >> n) >> m == a >> (n+m).
Proof.
 intros.
 now rewrite !shiftr_div_pow2, pow_add_r, div_div by order_nz.
Qed.

Lemma shiftr_shiftl_l : forall a n m, m<=n ->
 (a << n) >> m == a << (n-m).
Proof.
 intros.
 rewrite shiftr_div_pow2, !shiftl_mul_pow2.
 rewrite <- (sub_add m n) at 1 by trivial.
 now rewrite pow_add_r, mul_assoc, div_mul by order_nz.
Qed.

Lemma shiftr_shiftl_r : forall a n m, n<=m ->
 (a << n) >> m == a >> (m-n).
Proof.
 intros.
 rewrite !shiftr_div_pow2, shiftl_mul_pow2.
 rewrite <- (sub_add n m) at 1 by trivial.
 rewrite pow_add_r, (mul_comm (2^(m-n))).
 now rewrite <- div_div, div_mul by order_nz.
Qed.

(** shifts and constants *)

Lemma shiftl_1_l : forall n, 1 << n == 2^n.
Proof.
 intros. now rewrite shiftl_mul_pow2, mul_1_l.
Qed.

Lemma shiftl_0_r : forall a, a << 0 == a.
Proof.
 intros. rewrite shiftl_mul_pow2. now nzsimpl.
Qed.

Lemma shiftr_0_r : forall a, a >> 0 == a.
Proof.
 intros. rewrite shiftr_div_pow2. now nzsimpl.
Qed.

Lemma shiftl_0_l : forall n, 0 << n == 0.
Proof.
 intros. rewrite shiftl_mul_pow2. now nzsimpl.
Qed.

Lemma shiftr_0_l : forall n, 0 >> n == 0.
Proof.
 intros. rewrite shiftr_div_pow2. nzsimpl; order_nz.
Qed.

Lemma shiftl_eq_0_iff : forall a n, a << n == 0 <-> a == 0.
Proof.
 intros a n. rewrite shiftl_mul_pow2. rewrite eq_mul_0. split.
 intros [H | H]; trivial. contradict H; order_nz.
 intros H. now left.
Qed.

Lemma shiftr_eq_0_iff : forall a n,
 a >> n == 0 <-> a==0 \/ (0<a /\ log2 a < n).
Proof.
 intros a n.
 rewrite shiftr_div_pow2, div_small_iff by order_nz.
 destruct (eq_0_gt_0_cases a) as [EQ|LT].
 rewrite EQ. split. now left. intros _.
  assert (H : 2~=0) by order'.
  generalize (pow_nonzero 2 n H) (le_0_l (2^n)); order.
 rewrite log2_lt_pow2; trivial.
 split. right; split; trivial. intros [H|[_ H]]; now order.
Qed.

Lemma shiftr_eq_0 : forall a n, log2 a < n -> a >> n == 0.
Proof.
 intros a n H. rewrite shiftr_eq_0_iff.
 destruct (eq_0_gt_0_cases a) as [EQ|LT]. now left. right; now split.
Qed.

(** Properties of [div2]. *)

Lemma div2_div : forall a, div2 a == a/2.
Proof.
 intros. rewrite div2_spec, shiftr_div_pow2. now nzsimpl.
Qed.

Instance div2_wd : Proper (eq==>eq) div2.
Proof.
 intros a a' Ha. now rewrite 2 div2_div, Ha.
Qed.

Lemma div2_odd : forall a, a == 2*(div2 a) + odd a.
Proof.
 intros a. rewrite div2_div, <- bit0_odd, bit0_mod.
 apply div_mod. order'.
Qed.

(** Properties of [lxor] and others, directly deduced
    from properties of [xorb] and others. *)

Instance lxor_wd : Proper (eq ==> eq ==> eq) lxor.
Proof.
 intros a a' Ha b b' Hb. bitwise. now rewrite Ha, Hb.
Qed.

Instance land_wd : Proper (eq ==> eq ==> eq) land.
Proof.
 intros a a' Ha b b' Hb. bitwise. now rewrite Ha, Hb.
Qed.

Instance lor_wd : Proper (eq ==> eq ==> eq) lor.
Proof.
 intros a a' Ha b b' Hb. bitwise. now rewrite Ha, Hb.
Qed.

Instance ldiff_wd : Proper (eq ==> eq ==> eq) ldiff.
Proof.
 intros a a' Ha b b' Hb. bitwise. now rewrite Ha, Hb.
Qed.

Lemma lxor_eq : forall a a', lxor a a' == 0 -> a == a'.
Proof.
 intros a a' H. bitwise. apply xorb_eq.
 now rewrite <- lxor_spec, H, bits_0.
Qed.

Lemma lxor_nilpotent : forall a, lxor a a == 0.
Proof.
 intros. bitwise. apply xorb_nilpotent.
Qed.

Lemma lxor_eq_0_iff : forall a a', lxor a a' == 0 <-> a == a'.
Proof.
 split. apply lxor_eq. intros EQ; rewrite EQ; apply lxor_nilpotent.
Qed.

Lemma lxor_0_l : forall a, lxor 0 a == a.
Proof.
 intros. bitwise. apply xorb_false_l.
Qed.

Lemma lxor_0_r : forall a, lxor a 0 == a.
Proof.
 intros. bitwise. apply xorb_false_r.
Qed.

Lemma lxor_comm : forall a b, lxor a b == lxor b a.
Proof.
 intros. bitwise. apply xorb_comm.
Qed.

Lemma lxor_assoc :
 forall a b c, lxor (lxor a b) c == lxor a (lxor b c).
Proof.
 intros. bitwise. apply xorb_assoc.
Qed.

Lemma lor_0_l : forall a, lor 0 a == a.
Proof.
 intros. bitwise. trivial.
Qed.

Lemma lor_0_r : forall a, lor a 0 == a.
Proof.
 intros. bitwise. apply orb_false_r.
Qed.

Lemma lor_comm : forall a b, lor a b == lor b a.
Proof.
 intros. bitwise. apply orb_comm.
Qed.

Lemma lor_assoc :
 forall a b c, lor a (lor b c) == lor (lor a b) c.
Proof.
 intros. bitwise. apply orb_assoc.
Qed.

Lemma lor_diag : forall a, lor a a == a.
Proof.
 intros. bitwise. apply orb_diag.
Qed.

Lemma lor_eq_0_l : forall a b, lor a b == 0 -> a == 0.
Proof.
 intros a b H. bitwise.
 apply (orb_false_iff a.[m] b.[m]).
 now rewrite <- lor_spec, H, bits_0.
Qed.

Lemma lor_eq_0_iff : forall a b, lor a b == 0 <-> a == 0 /\ b == 0.
Proof.
 intros a b. split.
 split. now apply lor_eq_0_l in H.
 rewrite lor_comm in H. now apply lor_eq_0_l in H.
 intros (EQ,EQ'). now rewrite EQ, lor_0_l.
Qed.

Lemma land_0_l : forall a, land 0 a == 0.
Proof.
 intros. bitwise. trivial.
Qed.

Lemma land_0_r : forall a, land a 0 == 0.
Proof.
 intros. bitwise. apply andb_false_r.
Qed.

Lemma land_comm : forall a b, land a b == land b a.
Proof.
 intros. bitwise. apply andb_comm.
Qed.

Lemma land_assoc :
 forall a b c, land a (land b c) == land (land a b) c.
Proof.
 intros. bitwise. apply andb_assoc.
Qed.

Lemma land_diag : forall a, land a a == a.
Proof.
 intros. bitwise. apply andb_diag.
Qed.

Lemma ldiff_0_l : forall a, ldiff 0 a == 0.
Proof.
 intros. bitwise. trivial.
Qed.

Lemma ldiff_0_r : forall a, ldiff a 0 == a.
Proof.
 intros. bitwise. now rewrite andb_true_r.
Qed.

Lemma ldiff_diag : forall a, ldiff a a == 0.
Proof.
 intros. bitwise. apply andb_negb_r.
Qed.

Lemma lor_land_distr_l : forall a b c,
 lor (land a b) c == land (lor a c) (lor b c).
Proof.
 intros. bitwise. apply orb_andb_distrib_l.
Qed.

Lemma lor_land_distr_r : forall a b c,
 lor a (land b c) == land (lor a b) (lor a c).
Proof.
 intros. bitwise. apply orb_andb_distrib_r.
Qed.

Lemma land_lor_distr_l : forall a b c,
 land (lor a b) c == lor (land a c) (land b c).
Proof.
 intros. bitwise. apply andb_orb_distrib_l.
Qed.

Lemma land_lor_distr_r : forall a b c,
 land a (lor b c) == lor (land a b) (land a c).
Proof.
 intros. bitwise. apply andb_orb_distrib_r.
Qed.

Lemma ldiff_ldiff_l : forall a b c,
 ldiff (ldiff a b) c == ldiff a (lor b c).
Proof.
 intros. bitwise. now rewrite negb_orb, andb_assoc.
Qed.

Lemma lor_ldiff_and : forall a b,
 lor (ldiff a b) (land a b) == a.
Proof.
 intros. bitwise.
 now rewrite <- andb_orb_distrib_r, orb_comm, orb_negb_r, andb_true_r.
Qed.

Lemma land_ldiff : forall a b,
 land (ldiff a b) b == 0.
Proof.
 intros. bitwise.
 now rewrite <-andb_assoc, (andb_comm (negb _)), andb_negb_r, andb_false_r.
Qed.

(** Properties of [setbit] and [clearbit] *)

Definition setbit a n := lor a (1<<n).
Definition clearbit a n := ldiff a (1<<n).

Lemma setbit_spec' : forall a n, setbit a n == lor a (2^n).
Proof.
 intros. unfold setbit. now rewrite shiftl_1_l.
Qed.

Lemma clearbit_spec' : forall a n, clearbit a n == ldiff a (2^n).
Proof.
 intros. unfold clearbit. now rewrite shiftl_1_l.
Qed.

Instance setbit_wd : Proper (eq==>eq==>eq) setbit.
Proof. unfold setbit. solve_proper. Qed.

Instance clearbit_wd : Proper (eq==>eq==>eq) clearbit.
Proof. unfold clearbit. solve_proper. Qed.

Lemma pow2_bits_true : forall n, (2^n).[n] = true.
Proof.
 intros. rewrite <- (mul_1_l (2^n)). rewrite <- (add_0_l n) at 2.
 now rewrite mul_pow2_bits_add, bit0_odd, odd_1.
Qed.

Lemma pow2_bits_false : forall n m, n~=m -> (2^n).[m] = false.
Proof.
 intros.
 rewrite <- (mul_1_l (2^n)).
 destruct (le_gt_cases n m).
 rewrite mul_pow2_bits_high; trivial.
 rewrite <- (succ_pred (m-n)) by (apply sub_gt; order).
 now rewrite <- div2_bits, div_small, bits_0 by order'.
 rewrite mul_pow2_bits_low; trivial.
Qed.

Lemma pow2_bits_eqb : forall n m, (2^n).[m] = eqb n m.
Proof.
 intros. apply eq_true_iff_eq. rewrite eqb_eq. split.
 destruct (eq_decidable n m) as [H|H]. trivial.
 now rewrite (pow2_bits_false _ _ H).
 intros EQ. rewrite EQ. apply pow2_bits_true.
Qed.

Lemma setbit_eqb : forall a n m,
 (setbit a n).[m] = eqb n m || a.[m].
Proof.
 intros. now rewrite setbit_spec', lor_spec, pow2_bits_eqb, orb_comm.
Qed.

Lemma setbit_iff : forall a n m,
 (setbit a n).[m] = true <-> n==m \/ a.[m] = true.
Proof.
 intros. now rewrite setbit_eqb, orb_true_iff, eqb_eq.
Qed.

Lemma setbit_eq : forall a n, (setbit a n).[n] = true.
Proof.
 intros. apply setbit_iff. now left.
Qed.

Lemma setbit_neq : forall a n m, n~=m ->
 (setbit a n).[m] = a.[m].
Proof.
 intros a n m H. rewrite setbit_eqb.
 rewrite <- eqb_eq in H. apply not_true_is_false in H. now rewrite H.
Qed.

Lemma clearbit_eqb : forall a n m,
 (clearbit a n).[m] = a.[m] && negb (eqb n m).
Proof.
 intros. now rewrite clearbit_spec', ldiff_spec, pow2_bits_eqb.
Qed.

Lemma clearbit_iff : forall a n m,
 (clearbit a n).[m] = true <-> a.[m] = true /\ n~=m.
Proof.
 intros. rewrite clearbit_eqb, andb_true_iff, <- eqb_eq.
 now rewrite negb_true_iff, not_true_iff_false.
Qed.

Lemma clearbit_eq : forall a n, (clearbit a n).[n] = false.
Proof.
 intros. rewrite clearbit_eqb, (proj2 (eqb_eq _ _) (eq_refl n)).
 apply andb_false_r.
Qed.

Lemma clearbit_neq : forall a n m, n~=m ->
 (clearbit a n).[m] = a.[m].
Proof.
 intros a n m H. rewrite clearbit_eqb.
 rewrite <- eqb_eq in H. apply not_true_is_false in H. rewrite H.
 apply andb_true_r.
Qed.

(** Shifts of bitwise operations *)

Lemma shiftl_lxor : forall a b n,
 (lxor a b) << n == lxor (a << n) (b << n).
Proof.
 intros. bitwise.
 destruct (le_gt_cases n m).
 now rewrite !shiftl_spec_high', lxor_spec.
 now rewrite !shiftl_spec_low.
Qed.

Lemma shiftr_lxor : forall a b n,
 (lxor a b) >> n == lxor (a >> n) (b >> n).
Proof.
 intros. bitwise. now rewrite !shiftr_spec', lxor_spec.
Qed.

Lemma shiftl_land : forall a b n,
 (land a b) << n == land (a << n) (b << n).
Proof.
 intros. bitwise.
 destruct (le_gt_cases n m).
 now rewrite !shiftl_spec_high', land_spec.
 now rewrite !shiftl_spec_low.
Qed.

Lemma shiftr_land : forall a b n,
 (land a b) >> n == land (a >> n) (b >> n).
Proof.
 intros. bitwise. now rewrite !shiftr_spec', land_spec.
Qed.

Lemma shiftl_lor : forall a b n,
 (lor a b) << n == lor (a << n) (b << n).
Proof.
 intros. bitwise.
 destruct (le_gt_cases n m).
 now rewrite !shiftl_spec_high', lor_spec.
 now rewrite !shiftl_spec_low.
Qed.

Lemma shiftr_lor : forall a b n,
 (lor a b) >> n == lor (a >> n) (b >> n).
Proof.
 intros. bitwise. now rewrite !shiftr_spec', lor_spec.
Qed.

Lemma shiftl_ldiff : forall a b n,
 (ldiff a b) << n == ldiff (a << n) (b << n).
Proof.
 intros. bitwise.
 destruct (le_gt_cases n m).
 now rewrite !shiftl_spec_high', ldiff_spec.
 now rewrite !shiftl_spec_low.
Qed.

Lemma shiftr_ldiff : forall a b n,
 (ldiff a b) >> n == ldiff (a >> n) (b >> n).
Proof.
 intros. bitwise. now rewrite !shiftr_spec', ldiff_spec.
Qed.

(** We cannot have a function complementing all bits of a number,
    otherwise it would have an infinity of bit 1. Nonetheless,
    we can design a bounded complement *)

Definition ones n := P (1 << n).

Definition lnot a n := lxor a (ones n).

Instance ones_wd : Proper (eq==>eq) ones.
Proof. unfold ones. solve_proper. Qed.

Instance lnot_wd : Proper (eq==>eq==>eq) lnot.
Proof. unfold lnot. solve_proper. Qed.

Lemma ones_equiv : forall n, ones n == P (2^n).
Proof.
 intros; unfold ones; now rewrite shiftl_1_l.
Qed.

Lemma ones_add : forall n m, ones (m+n) == 2^m * ones n + ones m.
Proof.
 intros n m. rewrite !ones_equiv.
 rewrite <- !sub_1_r, mul_sub_distr_l, mul_1_r, <- pow_add_r.
 rewrite add_sub_assoc, sub_add. reflexivity.
 apply pow_le_mono_r. order'.
 rewrite <- (add_0_r m) at 1. apply add_le_mono_l, le_0_l.
 rewrite <- (pow_0_r 2). apply pow_le_mono_r. order'. apply le_0_l.
Qed.

Lemma ones_div_pow2 : forall n m, m<=n -> ones n / 2^m == ones (n-m).
Proof.
 intros n m H. symmetry. apply div_unique with (ones m).
 rewrite ones_equiv.
 apply le_succ_l. rewrite succ_pred; order_nz.
 rewrite <- (sub_add m n H) at 1. rewrite (add_comm _ m).
 apply ones_add.
Qed.

Lemma ones_mod_pow2 : forall n m, m<=n -> (ones n) mod (2^m) == ones m.
Proof.
 intros n m H. symmetry. apply mod_unique with (ones (n-m)).
 rewrite ones_equiv.
 apply le_succ_l. rewrite succ_pred; order_nz.
 rewrite <- (sub_add m n H) at 1. rewrite (add_comm _ m).
 apply ones_add.
Qed.

Lemma ones_spec_low : forall n m, m<n -> (ones n).[m] = true.
Proof.
 intros. apply testbit_true. rewrite ones_div_pow2 by order.
 rewrite <- (pow_1_r 2). rewrite ones_mod_pow2.
 rewrite ones_equiv. now nzsimpl'.
 apply le_add_le_sub_r. nzsimpl. now apply le_succ_l.
Qed.

Lemma ones_spec_high : forall n m, n<=m -> (ones n).[m] = false.
Proof.
 intros.
 destruct (eq_0_gt_0_cases n) as [EQ|LT]; rewrite ones_equiv.
 now rewrite EQ, pow_0_r, one_succ, pred_succ, bits_0.
 apply bits_above_log2.
 rewrite log2_pred_pow2; trivial. rewrite <-le_succ_l, succ_pred; order.
Qed.

Lemma ones_spec_iff : forall n m, (ones n).[m] = true <-> m<n.
Proof.
 intros. split. intros H.
 apply lt_nge. intro H'. apply ones_spec_high in H'.
 rewrite H in H'; discriminate.
 apply ones_spec_low.
Qed.

Lemma lnot_spec_low : forall a n m, m<n ->
 (lnot a n).[m] = negb a.[m].
Proof.
 intros. unfold lnot. now rewrite lxor_spec, ones_spec_low.
Qed.

Lemma lnot_spec_high : forall a n m, n<=m ->
 (lnot a n).[m] = a.[m].
Proof.
 intros. unfold lnot. now rewrite lxor_spec, ones_spec_high, xorb_false_r.
Qed.

Lemma lnot_involutive : forall a n, lnot (lnot a n) n == a.
Proof.
 intros a n. bitwise.
 destruct (le_gt_cases n m).
 now rewrite 2 lnot_spec_high.
 now rewrite 2 lnot_spec_low, negb_involutive.
Qed.

Lemma lnot_0_l : forall n, lnot 0 n == ones n.
Proof.
 intros. unfold lnot. apply lxor_0_l.
Qed.

Lemma lnot_ones : forall n, lnot (ones n) n == 0.
Proof.
 intros. unfold lnot. apply lxor_nilpotent.
Qed.

(** Bounded complement and other operations *)

Lemma lor_ones_low : forall a n, log2 a < n ->
 lor a (ones n) == ones n.
Proof.
 intros a n H. bitwise. destruct (le_gt_cases n m).
 rewrite ones_spec_high, bits_above_log2; trivial.
 now apply lt_le_trans with n.
 now rewrite ones_spec_low, orb_true_r.
Qed.

Lemma land_ones : forall a n, land a (ones n) == a mod 2^n.
Proof.
 intros a n. bitwise. destruct (le_gt_cases n m).
 now rewrite ones_spec_high, mod_pow2_bits_high, andb_false_r.
 now rewrite ones_spec_low, mod_pow2_bits_low, andb_true_r.
Qed.

Lemma land_ones_low : forall a n, log2 a < n ->
 land a (ones n) == a.
Proof.
 intros; rewrite land_ones. apply mod_small.
 apply log2_lt_cancel. rewrite log2_pow2; trivial using le_0_l.
Qed.

Lemma ldiff_ones_r : forall a n,
 ldiff a (ones n) == (a >> n) << n.
Proof.
 intros a n. bitwise. destruct (le_gt_cases n m).
 rewrite ones_spec_high, shiftl_spec_high', shiftr_spec'; trivial.
 rewrite sub_add; trivial. apply andb_true_r.
 now rewrite ones_spec_low, shiftl_spec_low, andb_false_r.
Qed.

Lemma ldiff_ones_r_low : forall a n, log2 a < n ->
 ldiff a (ones n) == 0.
Proof.
 intros a n H. bitwise. destruct (le_gt_cases n m).
 rewrite ones_spec_high, bits_above_log2; trivial.
 now apply lt_le_trans with n.
 now rewrite ones_spec_low, andb_false_r.
Qed.

Lemma ldiff_ones_l_low : forall a n, log2 a < n ->
 ldiff (ones n) a == lnot a n.
Proof.
 intros a n H. bitwise. destruct (le_gt_cases n m).
 rewrite ones_spec_high, lnot_spec_high, bits_above_log2; trivial.
 now apply lt_le_trans with n.
 now rewrite ones_spec_low, lnot_spec_low.
Qed.

Lemma lor_lnot_diag : forall a n,
 lor a (lnot a n) == lor a (ones n).
Proof.
 intros a n. bitwise.
 destruct (le_gt_cases n m).
 rewrite lnot_spec_high, ones_spec_high; trivial. now destruct a.[m].
 rewrite lnot_spec_low, ones_spec_low; trivial. now destruct a.[m].
Qed.

Lemma lor_lnot_diag_low : forall a n, log2 a < n ->
 lor a (lnot a n) == ones n.
Proof.
 intros a n H. now rewrite lor_lnot_diag, lor_ones_low.
Qed.

Lemma land_lnot_diag : forall a n,
 land a (lnot a n) == ldiff a (ones n).
Proof.
 intros a n. bitwise.
 destruct (le_gt_cases n m).
 rewrite lnot_spec_high, ones_spec_high; trivial. now destruct a.[m].
 rewrite lnot_spec_low, ones_spec_low; trivial. now destruct a.[m].
Qed.

Lemma land_lnot_diag_low : forall a n, log2 a < n ->
 land a (lnot a n) == 0.
Proof.
 intros. now rewrite land_lnot_diag, ldiff_ones_r_low.
Qed.

Lemma lnot_lor_low : forall a b n, log2 a < n -> log2 b < n ->
 lnot (lor a b) n == land (lnot a n) (lnot b n).
Proof.
 intros a b n Ha Hb. bitwise. destruct (le_gt_cases n m).
 rewrite !lnot_spec_high, lor_spec, !bits_above_log2; trivial.
 now apply lt_le_trans with n.
 now apply lt_le_trans with n.
 now rewrite !lnot_spec_low, lor_spec, negb_orb.
Qed.

Lemma lnot_land_low : forall a b n, log2 a < n -> log2 b < n ->
 lnot (land a b) n == lor (lnot a n) (lnot b n).
Proof.
 intros a b n Ha Hb. bitwise. destruct (le_gt_cases n m).
 rewrite !lnot_spec_high, land_spec, !bits_above_log2; trivial.
 now apply lt_le_trans with n.
 now apply lt_le_trans with n.
 now rewrite !lnot_spec_low, land_spec, negb_andb.
Qed.

Lemma ldiff_land_low : forall a b n, log2 a < n ->
 ldiff a b == land a (lnot b n).
Proof.
 intros a b n Ha. bitwise. destruct (le_gt_cases n m).
 rewrite (bits_above_log2 a m). trivial.
 now apply lt_le_trans with n.
 rewrite !lnot_spec_low; trivial.
Qed.

Lemma lnot_ldiff_low : forall a b n, log2 a < n -> log2 b < n ->
 lnot (ldiff a b) n == lor (lnot a n) b.
Proof.
 intros a b n Ha Hb. bitwise. destruct (le_gt_cases n m).
 rewrite !lnot_spec_high, ldiff_spec, !bits_above_log2; trivial.
 now apply lt_le_trans with n.
 now apply lt_le_trans with n.
 now rewrite !lnot_spec_low, ldiff_spec, negb_andb, negb_involutive.
Qed.

Lemma lxor_lnot_lnot : forall a b n,
 lxor (lnot a n) (lnot b n) == lxor a b.
Proof.
 intros a b n. bitwise. destruct (le_gt_cases n m).
 rewrite !lnot_spec_high; trivial.
 rewrite !lnot_spec_low, xorb_negb_negb; trivial.
Qed.

Lemma lnot_lxor_l : forall a b n,
 lnot (lxor a b) n == lxor (lnot a n) b.
Proof.
 intros a b n. bitwise. destruct (le_gt_cases n m).
 rewrite !lnot_spec_high, lxor_spec; trivial.
 rewrite !lnot_spec_low, lxor_spec, negb_xorb_l; trivial.
Qed.

Lemma lnot_lxor_r : forall a b n,
 lnot (lxor a b) n == lxor a (lnot b n).
Proof.
 intros a b n. bitwise. destruct (le_gt_cases n m).
 rewrite !lnot_spec_high, lxor_spec; trivial.
 rewrite !lnot_spec_low, lxor_spec, negb_xorb_r; trivial.
Qed.

Lemma lxor_lor : forall a b, land a b == 0 ->
 lxor a b == lor a b.
Proof.
 intros a b H. bitwise.
 assert (a.[m] && b.[m] = false)
   by now rewrite <- land_spec, H, bits_0.
 now destruct a.[m], b.[m].
Qed.

(** Bitwise operations and log2 *)

Lemma log2_bits_unique : forall a n,
 a.[n] = true ->
 (forall m, n<m -> a.[m] = false) ->
 log2 a == n.
Proof.
 intros a n H H'.
 destruct (eq_0_gt_0_cases a) as [Ha|Ha].
 now rewrite Ha, bits_0 in H.
 apply le_antisymm; apply le_ngt; intros LT.
 specialize (H' _ LT). now rewrite bit_log2 in H' by order.
 now rewrite bits_above_log2 in H by order.
Qed.

Lemma log2_shiftr : forall a n, log2 (a >> n) == log2 a - n.
Proof.
 intros a n.
 destruct (eq_0_gt_0_cases a) as [Ha|Ha].
 now rewrite Ha, shiftr_0_l, log2_nonpos, sub_0_l by order.
 destruct (lt_ge_cases (log2 a) n).
 rewrite shiftr_eq_0, log2_nonpos by order.
 symmetry. rewrite sub_0_le; order.
 apply log2_bits_unique.
 now rewrite shiftr_spec', sub_add, bit_log2 by order.
 intros m Hm.
 rewrite shiftr_spec'; trivial. apply bits_above_log2; try order.
 now apply lt_sub_lt_add_r.
Qed.

Lemma log2_shiftl : forall a n, a~=0 -> log2 (a << n) == log2 a + n.
Proof.
 intros a n Ha.
 rewrite shiftl_mul_pow2, add_comm by trivial.
 apply log2_mul_pow2. generalize (le_0_l a); order. apply le_0_l.
Qed.

Lemma log2_lor : forall a b,
 log2 (lor a b) == max (log2 a) (log2 b).
Proof.
 assert (AUX : forall a b, a<=b -> log2 (lor a b) == log2 b).
  intros a b H.
  destruct (eq_0_gt_0_cases a) as [Ha|Ha]. now rewrite Ha, lor_0_l.
  apply log2_bits_unique.
  now rewrite lor_spec, bit_log2, orb_true_r by order.
  intros m Hm. assert (H' := log2_le_mono _ _ H).
  now rewrite lor_spec, 2 bits_above_log2 by order.
 (* main *)
 intros a b. destruct (le_ge_cases a b) as [H|H].
 rewrite max_r by now apply log2_le_mono.
 now apply AUX.
 rewrite max_l by now apply log2_le_mono.
 rewrite lor_comm. now apply AUX.
Qed.

Lemma log2_land : forall a b,
 log2 (land a b) <= min (log2 a) (log2 b).
Proof.
 assert (AUX : forall a b, a<=b -> log2 (land a b) <= log2 a).
  intros a b H.
  apply le_ngt. intros H'.
  destruct (eq_decidable (land a b) 0) as [EQ|NEQ].
  rewrite EQ in H'. apply log2_lt_cancel in H'. generalize (le_0_l a); order.
  generalize (bit_log2 (land a b) NEQ).
  now rewrite land_spec, bits_above_log2.
 (* main *)
 intros a b.
 destruct (le_ge_cases a b) as [H|H].
 rewrite min_l by now apply log2_le_mono. now apply AUX.
 rewrite min_r by now apply log2_le_mono. rewrite land_comm. now apply AUX.
Qed.

Lemma log2_lxor : forall a b,
 log2 (lxor a b) <= max (log2 a) (log2 b).
Proof.
 assert (AUX : forall a b, a<=b -> log2 (lxor a b) <= log2 b).
  intros a b H.
  apply le_ngt. intros H'.
  destruct (eq_decidable (lxor a b) 0) as [EQ|NEQ].
  rewrite EQ in H'. apply log2_lt_cancel in H'. generalize (le_0_l a); order.
  generalize (bit_log2 (lxor a b) NEQ).
  rewrite lxor_spec, 2 bits_above_log2; try order. discriminate.
  apply le_lt_trans with (log2 b); trivial. now apply log2_le_mono.
 (* main *)
 intros a b.
 destruct (le_ge_cases a b) as [H|H].
 rewrite max_r by now apply log2_le_mono. now apply AUX.
 rewrite max_l by now apply log2_le_mono. rewrite lxor_comm. now apply AUX.
Qed.

(** Bitwise operations and arithmetical operations *)

Local Notation xor3 a b c := (xorb (xorb a b) c).
Local Notation lxor3 a b c := (lxor (lxor a b) c).

Local Notation nextcarry a b c := ((a&&b) || (c && (a||b))).
Local Notation lnextcarry a b c := (lor (land a b) (land c (lor a b))).

Lemma add_bit0 : forall a b, (a+b).[0] = xorb a.[0] b.[0].
Proof.
 intros. now rewrite !bit0_odd, odd_add.
Qed.

Lemma add3_bit0 : forall a b c,
 (a+b+c).[0] = xor3 a.[0] b.[0] c.[0].
Proof.
 intros. now rewrite !add_bit0.
Qed.

Lemma add3_bits_div2 : forall (a0 b0 c0 : bool),
 (a0 + b0 + c0)/2 == nextcarry a0 b0 c0.
Proof.
 assert (H : 1+1 == 2) by now nzsimpl'.
 intros [|] [|] [|]; simpl; rewrite ?add_0_l, ?add_0_r, ?H;
  (apply div_same; order') || (apply div_small; order') || idtac.
 symmetry. apply div_unique with 1. order'. now nzsimpl'.
Qed.

Lemma add_carry_div2 : forall a b (c0:bool),
 (a + b + c0)/2 == a/2 + b/2 + nextcarry a.[0] b.[0] c0.
Proof.
 intros.
 rewrite <- add3_bits_div2.
 rewrite (add_comm ((a/2)+_)).
 rewrite <- div_add by order'.
 f_equiv.
 rewrite <- !div2_div, mul_comm, mul_add_distr_l.
 rewrite (div2_odd a), <- bit0_odd at 1. fold (b2n a.[0]).
 rewrite (div2_odd b), <- bit0_odd at 1. fold (b2n b.[0]).
 rewrite add_shuffle1.
 rewrite <-(add_assoc _ _ c0). apply add_comm.
Qed.

(** The main result concerning addition: we express the bits of the sum
  in term of bits of [a] and [b] and of some carry stream which is also
  recursively determined by another equation.
*)

Lemma add_carry_bits : forall a b (c0:bool), exists c,
 a+b+c0 == lxor3 a b c /\ c/2 == lnextcarry a b c /\ c.[0] = c0.
Proof.
 intros a b c0.
 (* induction over some n such that [a<2^n] and [b<2^n] *)
 set (n:=max a b).
 assert (Ha : a<2^n).
  apply lt_le_trans with (2^a). apply pow_gt_lin_r, lt_1_2.
  apply pow_le_mono_r. order'. unfold n.
  destruct (le_ge_cases a b); [rewrite max_r|rewrite max_l]; order'.
 assert (Hb : b<2^n).
  apply lt_le_trans with (2^b). apply pow_gt_lin_r, lt_1_2.
  apply pow_le_mono_r. order'. unfold n.
  destruct (le_ge_cases a b); [rewrite max_r|rewrite max_l]; order'.
 clearbody n.
 revert a b c0 Ha Hb. induct n.
 (*base*)
 intros a b c0. rewrite !pow_0_r, !one_succ, !lt_succ_r. intros Ha Hb.
 exists c0.
 setoid_replace a with 0 by (generalize (le_0_l a); order').
 setoid_replace b with 0 by (generalize (le_0_l b); order').
 rewrite !add_0_l, !lxor_0_l, !lor_0_r, !land_0_r, !lor_0_r.
 rewrite b2n_div2, b2n_bit0; now repeat split.
 (*step*)
 intros n IH a b c0 Ha Hb.
 set (c1:=nextcarry a.[0] b.[0] c0).
 destruct (IH (a/2) (b/2) c1) as (c & IH1 & IH2 & Hc); clear IH.
 apply div_lt_upper_bound; trivial. order'. now rewrite <- pow_succ_r'.
 apply div_lt_upper_bound; trivial. order'. now rewrite <- pow_succ_r'.
 exists (c0 + 2*c). repeat split.
 (* - add *)
 bitwise.
 destruct (zero_or_succ m) as [EQ|[m' EQ]]; rewrite EQ; clear EQ.
 now rewrite add_b2n_double_bit0, add3_bit0, b2n_bit0.
 rewrite <- !div2_bits, <- 2 lxor_spec.
 f_equiv.
 rewrite add_b2n_double_div2, <- IH1. apply add_carry_div2.
 (* - carry *)
 rewrite add_b2n_double_div2.
 bitwise.
 destruct (zero_or_succ m) as [EQ|[m' EQ]]; rewrite EQ; clear EQ.
 now rewrite add_b2n_double_bit0.
 rewrite <- !div2_bits, IH2. autorewrite with bitwise.
 now rewrite add_b2n_double_div2.
 (* - carry0 *)
 apply add_b2n_double_bit0.
Qed.

(** Particular case : the second bit of an addition *)

Lemma add_bit1 : forall a b,
 (a+b).[1] = xor3 a.[1] b.[1] (a.[0] && b.[0]).
Proof.
 intros a b.
 destruct (add_carry_bits a b false) as (c & EQ1 & EQ2 & Hc).
 simpl in EQ1; rewrite add_0_r in EQ1. rewrite EQ1.
 autorewrite with bitwise. f_equal.
 rewrite one_succ, <- div2_bits, EQ2.
 autorewrite with bitwise.
 rewrite Hc. simpl. apply orb_false_r.
Qed.

(** In an addition, there will be no carries iff there is
  no common bits in the numbers to add *)

Lemma nocarry_equiv : forall a b c,
 c/2 == lnextcarry a b c -> c.[0] = false ->
 (c == 0 <-> land a b == 0).
Proof.
 intros a b c H H'.
 split. intros EQ; rewrite EQ in *.
 rewrite div_0_l in H by order'.
 symmetry in H. now apply lor_eq_0_l in H.
 intros EQ. rewrite EQ, lor_0_l in H.
 apply bits_inj_0.
 induct n. trivial.
 intros n IH.
 rewrite <- div2_bits, H.
 autorewrite with bitwise.
 now rewrite IH.
Qed.

(** When there is no common bits, the addition is just a xor *)

Lemma add_nocarry_lxor : forall a b, land a b == 0 ->
 a+b == lxor a b.
Proof.
 intros a b H.
 destruct (add_carry_bits a b false) as (c & EQ1 & EQ2 & Hc).
 simpl in EQ1; rewrite add_0_r in EQ1. rewrite EQ1.
 apply (nocarry_equiv a b c) in H; trivial.
 rewrite H. now rewrite lxor_0_r.
Qed.

(** A null [ldiff] implies being smaller *)

Lemma ldiff_le : forall a b, ldiff a b == 0 -> a <= b.
Proof.
 cut (forall n a b, a < 2^n -> ldiff a b == 0 -> a <= b).
 intros H a b. apply (H a), pow_gt_lin_r; order'.
 induct n.
 intros a b Ha _. rewrite pow_0_r, one_succ, lt_succ_r in Ha.
 assert (Ha' : a == 0) by (generalize (le_0_l a); order').
 rewrite Ha'. apply le_0_l.
 intros n IH a b Ha H.
 assert (NEQ : 2 ~= 0) by order'.
 rewrite (div_mod a 2 NEQ), (div_mod b 2 NEQ).
 apply add_le_mono.
 apply mul_le_mono_l.
 apply IH.
 apply div_lt_upper_bound; trivial. now rewrite <- pow_succ_r'.
 rewrite <- (pow_1_r 2), <- 2 shiftr_div_pow2.
 now rewrite <- shiftr_ldiff, H, shiftr_div_pow2, pow_1_r, div_0_l.
 rewrite <- 2 bit0_mod.
 apply bits_inj_iff in H. specialize (H 0).
 rewrite ldiff_spec, bits_0 in H.
 destruct a.[0], b.[0]; try discriminate; simpl; order'.
Qed.

(** Subtraction can be a ldiff when the opposite ldiff is null. *)

Lemma sub_nocarry_ldiff : forall a b, ldiff b a == 0 ->
 a-b == ldiff a b.
Proof.
 intros a b H.
 apply add_cancel_r with b.
 rewrite sub_add.
 symmetry.
 rewrite add_nocarry_lxor.
 bitwise.
 apply bits_inj_iff in H. specialize (H m).
 rewrite ldiff_spec, bits_0 in H.
 now destruct a.[m], b.[m].
 apply land_ldiff.
 now apply ldiff_le.
Qed.

(** We can express lnot in term of subtraction *)

Lemma add_lnot_diag_low : forall a n, log2 a < n ->
 a + lnot a n == ones n.
Proof.
 intros a n H.
 assert (H' := land_lnot_diag_low a n H).
 rewrite add_nocarry_lxor, lxor_lor by trivial.
 now apply lor_lnot_diag_low.
Qed.

Lemma lnot_sub_low : forall a n, log2 a < n ->
 lnot a n == ones n - a.
Proof.
 intros a n H.
 now rewrite <- (add_lnot_diag_low a n H), add_comm, add_sub.
Qed.

(** Adding numbers with no common bits cannot lead to a much bigger number *)

Lemma add_nocarry_lt_pow2 : forall a b n, land a b == 0 ->
 a < 2^n -> b < 2^n -> a+b < 2^n.
Proof.
 intros a b n H Ha Hb.
 rewrite add_nocarry_lxor by trivial.
 apply div_small_iff. order_nz.
 rewrite <- shiftr_div_pow2, shiftr_lxor, !shiftr_div_pow2.
 rewrite 2 div_small by trivial.
 apply lxor_0_l.
Qed.

Lemma add_nocarry_mod_lt_pow2 : forall a b n, land a b == 0 ->
 a mod 2^n + b mod 2^n < 2^n.
Proof.
 intros a b n H.
 apply add_nocarry_lt_pow2.
 bitwise.
 destruct (le_gt_cases n m).
 now rewrite mod_pow2_bits_high.
 now rewrite !mod_pow2_bits_low, <- land_spec, H, bits_0.
 apply mod_upper_bound; order_nz.
 apply mod_upper_bound; order_nz.
Qed.

End NBitsProp.
