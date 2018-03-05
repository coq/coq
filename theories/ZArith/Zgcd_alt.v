(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Zgcd_alt : an alternate version of Z.gcd, based on Euclid's algorithm *)

(**
Author: Pierre Letouzey
*)

(** The alternate [Zgcd_alt] given here used to be the main [Z.gcd]
    function (see file [Znumtheory]), but this main [Z.gcd] is now
    based on a modern binary-efficient algorithm. This earlier
    version, based on Euclid's algorithm of iterated modulo, is kept
    here due to both its intrinsic interest and its use as reference
    point when proving gcd on Int31 numbers *)

Require Import ZArith_base.
Require Import ZArithRing.
Require Import Zdiv.
Require Import Znumtheory.
Require Import Omega.

Open Scope Z_scope.

(** In Coq, we need to control the number of iteration of modulo.
   For that, we use an explicit measure in [nat], and we prove later
   that using [2*d] is enough, where [d] is the number of binary
   digits of the first argument. *)

 Fixpoint Zgcdn (n:nat) : Z -> Z -> Z := fun a b =>
   match n with
     | O => 1 (* arbitrary, since n should be big enough *)
     | S n => match a with
	        | Z0 => Z.abs b
	        | Zpos _ => Zgcdn n (Z.modulo b a) a
	        | Zneg a => Zgcdn n (Z.modulo b (Zpos a)) (Zpos a)
  	      end
   end.

 Definition Zgcd_bound (a:Z) :=
   match a with
     | Z0 => S O
     | Zpos p => let n := Pos.size_nat p in (n+n)%nat
     | Zneg p => let n := Pos.size_nat p in (n+n)%nat
   end.

 Definition Zgcd_alt a b := Zgcdn (Zgcd_bound a) a b.

 (** A first obvious fact : [Z.gcd a b] is positive. *)

 Lemma Zgcdn_pos : forall n a b,
   0 <= Zgcdn n a b.
 Proof.
   induction n.
   simpl; auto with zarith.
   destruct a; simpl; intros; auto with zarith; auto.
 Qed.

 Lemma Zgcd_alt_pos : forall a b, 0 <= Zgcd_alt a b.
 Proof.
   intros; unfold Z.gcd; apply Zgcdn_pos; auto.
 Qed.

 (** We now prove that Z.gcd is indeed a gcd. *)

 (** 1) We prove a weaker & easier bound. *)

 Lemma Zgcdn_linear_bound : forall n a b,
   Z.abs a < Z.of_nat n -> Zis_gcd a b (Zgcdn n a b).
 Proof.
   induction n.
   simpl; intros.
   exfalso; generalize (Z.abs_nonneg a); omega.
   destruct a; intros; simpl;
     [ generalize (Zis_gcd_0_abs b); intuition | | ];
   unfold Z.modulo;
   generalize (Z_div_mod b (Zpos p) (eq_refl Gt));
   destruct (Z.div_eucl b (Zpos p)) as (q,r);
   intros (H0,H1);
   rewrite Nat2Z.inj_succ in H; simpl Z.abs in H;
   (assert (H2: Z.abs r < Z.of_nat n) by
    (rewrite Z.abs_eq; auto with zarith));
    assert (IH:=IHn r (Zpos p) H2); clear IHn;
    simpl in IH |- *;
    rewrite H0.
   apply Zis_gcd_for_euclid2; auto.
   apply Zis_gcd_minus; apply Zis_gcd_sym.
   apply Zis_gcd_for_euclid2; auto.
 Qed.

 (** 2) For Euclid's algorithm, the worst-case situation corresponds
    to Fibonacci numbers. Let's define them: *)

 Fixpoint fibonacci (n:nat) : Z :=
   match n with
     | O => 1
     | S O => 1
     | S (S n as p) => fibonacci p + fibonacci n
   end.

 Lemma fibonacci_pos : forall n, 0 <= fibonacci n.
 Proof.
   enough (forall N n, (n<N)%nat -> 0<=fibonacci n) by eauto.
   induction N.
   inversion 1.
   intros.
   destruct n.
   simpl; auto with zarith.
   destruct n.
   simpl; auto with zarith.
   change (0 <= fibonacci (S n) + fibonacci n).
   generalize (IHN n) (IHN (S n)); omega.
 Qed.

 Lemma fibonacci_incr :
   forall n m, (n<=m)%nat -> fibonacci n <= fibonacci m.
 Proof.
   induction 1.
   auto with zarith.
   apply Z.le_trans with (fibonacci m); auto.
   clear.
   destruct m.
   simpl; auto with zarith.
   change (fibonacci (S m) <= fibonacci (S m)+fibonacci m).
   generalize (fibonacci_pos m); omega.
 Qed.

 (** 3) We prove that fibonacci numbers are indeed worst-case:
    for a given number [n], if we reach a conclusion about [gcd(a,b)] in
    exactly [n+1] loops, then [fibonacci (n+1)<=a /\ fibonacci(n+2)<=b] *)

 Lemma Zgcdn_worst_is_fibonacci : forall n a b,
   0 < a < b ->
   Zis_gcd a b (Zgcdn (S n) a b) ->
   Zgcdn n a b <> Zgcdn (S n) a b ->
   fibonacci (S n) <= a /\
   fibonacci (S (S n)) <= b.
 Proof.
   induction n.
   intros [|a|a]; intros; simpl; omega.
   intros [|a|a] b (Ha,Ha'); [simpl; omega | | easy ].
   remember (S n) as m.
   rewrite Heqm at 2. simpl Zgcdn.
   unfold Z.modulo; generalize (Z_div_mod b (Zpos a) eq_refl).
   destruct (Z.div_eucl b (Zpos a)) as (q,r).
   intros (EQ,(Hr,Hr')).
   Z.le_elim Hr.
   - (* r > 0 *)
     replace (fibonacci (S (S m))) with (fibonacci (S m) + fibonacci m) by auto.
     intros.
     destruct (IHn r (Zpos a) (conj Hr Hr')); auto.
     + assert (EQ' : r = Zpos a * (-q) + b) by (rewrite EQ; ring).
       rewrite EQ' at 1.
       apply Zis_gcd_sym.
       apply Zis_gcd_for_euclid2; auto.
       apply Zis_gcd_sym; auto.
     + split; auto.
       rewrite EQ.
       apply Z.add_le_mono; auto.
       apply Z.le_trans with (Zpos a * 1); auto.
       now rewrite Z.mul_1_r.
       apply Z.mul_le_mono_nonneg_l; auto with zarith.
       change 1 with (Z.succ 0). apply Z.le_succ_l.
       destruct q; auto with zarith.
       assert (Zpos a * Zneg p < 0) by now compute. omega.
   - (* r = 0 *)
     clear IHn EQ Hr'; intros _.
     subst r; simpl; rewrite Heqm.
     destruct n.
     + simpl. omega.
     + now destruct 1.
 Qed.

 (** 3b) We reformulate the previous result in a more positive way. *)

 Lemma Zgcdn_ok_before_fibonacci : forall n a b,
   0 < a < b -> a < fibonacci (S n) ->
   Zis_gcd a b (Zgcdn n a b).
 Proof.
   destruct a; [ destruct 1; exfalso; omega | | destruct 1; discriminate].
   cut (forall k n b,
     k = (S (Pos.to_nat p) - n)%nat ->
     0 < Zpos p < b -> Zpos p < fibonacci (S n) ->
     Zis_gcd (Zpos p) b (Zgcdn n (Zpos p) b)).
   destruct 2; eauto.
   clear n; induction k.
   intros.
   assert (Pos.to_nat p < n)%nat by omega.
   apply Zgcdn_linear_bound.
   simpl.
   generalize (inj_le _ _ H2).
   rewrite Nat2Z.inj_succ.
   rewrite positive_nat_Z; auto.
   omega.
   intros.
   generalize (Zgcdn_worst_is_fibonacci n (Zpos p) b H0); intros.
   assert (Zis_gcd (Zpos p) b (Zgcdn (S n) (Zpos p) b)).
   apply IHk; auto.
   omega.
   replace (fibonacci (S (S n))) with (fibonacci (S n)+fibonacci n) by auto.
   generalize (fibonacci_pos n); omega.
   replace (Zgcdn n (Zpos p) b) with (Zgcdn (S n) (Zpos p) b); auto.
   generalize (H2 H3); clear H2 H3; omega.
 Qed.

 (** 4) The proposed bound leads to a fibonacci number that is big enough. *)

 Lemma Zgcd_bound_fibonacci :
   forall a, 0 < a -> a < fibonacci (Zgcd_bound a).
 Proof.
   destruct a; [omega| | intro H; discriminate].
   intros _.
   induction p; [ | | compute; auto ];
    simpl Zgcd_bound in *;
    rewrite plus_comm; simpl plus;
    set (n:= (Pos.size_nat p+Pos.size_nat p)%nat) in *; simpl;
    assert (n <> O) by (unfold n; destruct p; simpl; auto).

   destruct n as [ |m]; [elim H; auto| ].
   generalize (fibonacci_pos m); rewrite Pos2Z.inj_xI; omega.

   destruct n as [ |m]; [elim H; auto| ].
   generalize (fibonacci_pos m); rewrite Pos2Z.inj_xO; omega.
 Qed.

 (* 5) the end: we glue everything together and take care of
    situations not corresponding to [0<a<b]. *)

 Lemma Zgcd_bound_opp a : Zgcd_bound (-a) = Zgcd_bound a.
 Proof.
  now destruct a.
 Qed.

 Lemma Zgcdn_opp n a b : Zgcdn n (-a) b = Zgcdn n a b.
 Proof.
  induction n; simpl; auto.
  destruct a; simpl; auto.
 Qed.

 Lemma Zgcdn_is_gcd_pos n a b : (Zgcd_bound (Zpos a) <= n)%nat ->
   Zis_gcd (Zpos a) b (Zgcdn n (Zpos a) b).
 Proof.
  intros.
  generalize (Zgcd_bound_fibonacci (Zpos a)).
  simpl Zgcd_bound in *.
  remember (Pos.size_nat a+Pos.size_nat a)%nat as m.
  assert (1 < m)%nat.
  { rewrite Heqm; destruct a; simpl; rewrite 1?plus_comm;
    auto with arith. }
  destruct m as [ |m]; [inversion H0; auto| ].
  destruct n as [ |n]; [inversion H; auto| ].
  simpl Zgcdn.
  unfold Z.modulo.
  generalize (Z_div_mod b (Zpos a) (eq_refl Gt)).
  destruct (Z.div_eucl b (Zpos a)) as (q,r).
  intros (->,(H1,H2)) H3.
  apply Zis_gcd_for_euclid2.
  Z.le_elim H1.
  + apply Zgcdn_ok_before_fibonacci; auto.
    apply Z.lt_le_trans with (fibonacci (S m));
    [ omega | apply fibonacci_incr; auto].
  + subst r; simpl.
    destruct m as [ |m]; [exfalso; omega| ].
    destruct n as [ |n]; [exfalso; omega| ].
    simpl; apply Zis_gcd_sym; apply Zis_gcd_0.
 Qed.

 Lemma Zgcdn_is_gcd n a b :
   (Zgcd_bound a <= n)%nat -> Zis_gcd a b (Zgcdn n a b).
 Proof.
   destruct a.
   - simpl; intros.
     destruct n; [exfalso; omega | ].
     simpl; generalize (Zis_gcd_0_abs b); intuition.
   - apply Zgcdn_is_gcd_pos.
   - rewrite <- Zgcd_bound_opp, <- Zgcdn_opp.
     intros. apply Zis_gcd_minus, Zis_gcd_sym. simpl Z.opp.
     now apply Zgcdn_is_gcd_pos.
 Qed.

 Lemma Zgcd_is_gcd :
   forall a b, Zis_gcd a b (Zgcd_alt a b).
 Proof.
  unfold Zgcd_alt; intros; apply Zgcdn_is_gcd; auto.
 Qed.


