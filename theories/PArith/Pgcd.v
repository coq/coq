(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinPos Le Plus.

Local Open Scope positive_scope.

(** * Divisibility *)

Definition Pdivide p q := exists r, p*r = q.
Notation "( p | q )" := (Pdivide p q) (at level 0) : positive_scope.

Lemma Pdivide_add_cancel_r : forall p q r, (p | q) -> (p | q + r) -> (p | r).
Proof.
 intros p q r (s,Hs) (t,Ht).
 exists (t-s).
 rewrite Pmult_minus_distr_l.
 rewrite Hs, Ht.
 rewrite Pplus_comm. apply Pplus_minus_eq.
 apply Pmult_lt_mono_l with p.
 rewrite Hs, Ht.
 apply Plt_plus_r.
Qed.

Lemma Pdivide_xO_xI : forall p q r, (p | q~0) -> (p | r~1) -> (p | q).
Proof.
 intros p q r (s,Hs) (t,Ht).
 destruct p.
  destruct s; try discriminate.
  rewrite Pmult_xO_permute_r in Hs. exists s; congruence.
 simpl in Ht. discriminate.
 exists q; auto.
Qed.

Lemma Pdivide_xO_xO : forall p q, (p~0|q~0) <-> (p|q).
Proof.
 intros p q. split; intros (r,H); simpl in *.
 injection H. exists r; auto.
 exists r; simpl; f_equal; auto.
Qed.

Lemma Pdivide_mult_l : forall p q r, (p|q) -> (p|q*r).
Proof.
 intros p q r (s,H). exists (s*r). rewrite Pmult_assoc; now f_equal.
Qed.

Lemma Pdivide_mult_r : forall p q r, (p|r) -> (p|q*r).
Proof.
 intros p q r. rewrite Pmult_comm. apply Pdivide_mult_l.
Qed.


(** * Definition of a Pgcd function for positive numbers *)

(** Instead of the Euclid algorithm, we use here the Stein binary
   algorithm, which is faster for this representation. This algorithm
   is almost structural, but in the last cases we do some recursive
   calls on subtraction, hence the need for a counter.
*)

Fixpoint Pgcdn (n: nat) (a b : positive) : positive :=
  match n with
    | O => 1
    | S n =>
      match a,b with
	| 1, _ => 1
	| _, 1 => 1
	| a~0, b~0 => (Pgcdn n a b)~0
	| _  , b~0 => Pgcdn n a b
	| a~0, _   => Pgcdn n a b
	| a'~1, b'~1 =>
          match (a' ?= b') Eq with
	    | Eq => a
	    | Lt => Pgcdn n (b'-a') a
	    | Gt => Pgcdn n (a'-b') b
          end
      end
  end.

(** We'll show later that we need at most (log2(a.b)) loops *)

Definition Pgcd (a b: positive) := Pgcdn (Psize a + Psize b)%nat a b.


(** * Generalized Gcd, also computing the division of a and b by the gcd *)

Fixpoint Pggcdn (n: nat) (a b : positive) : (positive*(positive*positive)) :=
  match n with
    | O => (1,(a,b))
    | S n =>
      match a,b with
	| 1, _ => (1,(1,b))
	| _, 1 => (1,(a,1))
	| a~0, b~0 =>
           let (g,p) := Pggcdn n a b in
           (g~0,p)
	| _, b~0 =>
           let '(g,(aa,bb)) := Pggcdn n a b in
           (g,(aa, bb~0))
	| a~0, _ =>
           let '(g,(aa,bb)) := Pggcdn n a b in
           (g,(aa~0, bb))
	| a'~1, b'~1 =>
           match Pcompare a' b' Eq with
	     | Eq => (a,(1,1))
	     | Lt =>
	        let '(g,(ba,aa)) := Pggcdn n (b'-a') a in
	        (g,(aa, aa + ba~0))
	     | Gt =>
		let '(g,(ab,bb)) := Pggcdn n (a'-b') b in
		(g,(bb + ab~0, bb))
	   end
      end
  end.

Definition Pggcd (a b: positive) := Pggcdn (Psize a + Psize b)%nat a b.

(** The first component of Pggcd is Pgcd *)

Lemma Pggcdn_gcdn : forall n a b,
  fst (Pggcdn n a b) = Pgcdn n a b.
Proof.
 induction n.
 simpl; auto.
 destruct a, b; simpl; auto; try case Pcompare_spec; simpl; trivial;
  rewrite <- IHn; destruct Pggcdn as (g,(u,v)); simpl; auto.
Qed.

Lemma Pggcd_gcd : forall a b, fst (Pggcd a b) = Pgcd a b.
Proof.
 unfold Pggcd, Pgcd. intros. apply Pggcdn_gcdn.
Qed.

(** The other components of Pggcd are indeed the correct factors. *)

Ltac destr_pggcdn IHn :=
 match goal with |- context [ Pggcdn _ ?x ?y ] =>
  generalize (IHn x y); destruct Pggcdn as (g,(u,v)); simpl
 end.

Lemma Pggcdn_correct_divisors : forall n a b,
  let '(g,(aa,bb)) := Pggcdn n a b in
  a = g*aa /\ b = g*bb.
Proof.
 induction n.
 simpl; auto.
 destruct a, b; simpl; auto; try case Pcompare_spec; try destr_pggcdn IHn.
 (* Eq *)
 intros ->. now rewrite Pmult_comm.
 (* Lt *)
 intros (H',H) LT; split; auto.
 rewrite Pmult_plus_distr_l, Pmult_xO_permute_r, <- H, <- H'.
 simpl. f_equal. symmetry.
 apply Pplus_minus; auto. rewrite ZC4; rewrite LT; auto.
 (* Gt *)
 intros (H',H) LT; split; auto.
 rewrite Pmult_plus_distr_l, Pmult_xO_permute_r, <- H, <- H'.
 simpl. f_equal. symmetry.
 apply Pplus_minus; auto. rewrite ZC4; rewrite LT; auto.
 (* Then... *)
 intros (H,H'); split; auto. rewrite Pmult_xO_permute_r, H'; auto.
 intros (H,H'); split; auto. rewrite Pmult_xO_permute_r, H; auto.
 intros (H,H'); split; subst; auto.
Qed.

Lemma Pggcd_correct_divisors : forall a b,
  let '(g,(aa,bb)) := Pggcd a b in
  a=g*aa /\ b=g*bb.
Proof.
 unfold Pggcd. intros. apply Pggcdn_correct_divisors.
Qed.

(** We can use this fact to prove a part of the Pgcd correctness *)

Lemma Pgcd_divide_l : forall a b, (Pgcd a b | a).
Proof.
 intros a b. rewrite <- Pggcd_gcd. generalize (Pggcd_correct_divisors a b).
 destruct Pggcd as (g,(aa,bb)); simpl. intros (H,_). exists aa; auto.
Qed.

Lemma Pgcd_divide_r : forall a b, (Pgcd a b | b).
Proof.
 intros a b. rewrite <- Pggcd_gcd. generalize (Pggcd_correct_divisors a b).
 destruct Pggcd as (g,(aa,bb)); simpl. intros (_,H). exists bb; auto.
Qed.

(** We now prove directly that gcd is the greatest amongst common divisors *)

Lemma Pgcdn_greatest : forall n a b, (Psize a + Psize b <= n)%nat ->
 forall p, (p|a) -> (p|b) -> (p|Pgcdn n a b).
Proof.
 induction n.
 destruct a, b; simpl; inversion 1.
 destruct a, b; simpl; try case Pcompare_spec; simpl; auto.
 (* Lt *)
 intros LT LE p Hp1 Hp2. apply IHn; clear IHn; trivial.
 apply le_S_n in LE. eapply le_trans; [|eapply LE].
 rewrite plus_comm, <- plus_n_Sm, <- plus_Sn_m.
 apply plus_le_compat; trivial.
 apply Psize_monotone, Pminus_decr, LT.
 apply Pdivide_xO_xI with a; trivial.
 apply (Pdivide_add_cancel_r p a~1); trivial.
 rewrite <- Pminus_xI_xI, Pplus_minus; trivial.
 simpl. now rewrite ZC4, LT.
 (* Gt *)
 intros LT LE p Hp1 Hp2. apply IHn; clear IHn; trivial.
 apply le_S_n in LE. eapply le_trans; [|eapply LE].
 apply plus_le_compat; trivial.
 apply Psize_monotone, Pminus_decr, LT.
 apply Pdivide_xO_xI with b; trivial.
 apply (Pdivide_add_cancel_r p b~1); trivial.
 rewrite <- Pminus_xI_xI, Pplus_minus; trivial.
 simpl. now rewrite ZC4, LT.
 (* a~1 b~0 *)
 intros LE p Hp1 Hp2. apply IHn; clear IHn; trivial.
 apply le_S_n in LE. simpl. now rewrite plus_n_Sm.
 apply Pdivide_xO_xI with a; trivial.
 (* a~0 b~1 *)
 intros LE p Hp1 Hp2. apply IHn; clear IHn; trivial.
 simpl. now apply le_S_n.
 apply Pdivide_xO_xI with b; trivial.
 (* a~0 b~0 *)
 intros LE p Hp1 Hp2.
 destruct p.
 change (Pgcdn n a b)~0 with (2*(Pgcdn n a b)).
 apply Pdivide_mult_r.
 apply IHn; clear IHn.
 apply le_S_n in LE. apply le_Sn_le. now rewrite plus_n_Sm.
 apply Pdivide_xO_xI with p; trivial. exists 1; now rewrite Pmult_1_r.
 apply Pdivide_xO_xI with p; trivial. exists 1; now rewrite Pmult_1_r.
 apply Pdivide_xO_xO.
 apply IHn; clear IHn.
 apply le_S_n in LE. apply le_Sn_le. now rewrite plus_n_Sm.
 now apply Pdivide_xO_xO.
 now apply Pdivide_xO_xO.
 exists (Pgcdn n a b)~0. auto.
Qed.

Lemma Pgcd_greatest : forall a b p, (p|a) -> (p|b) -> (p|Pgcd a b).
Proof.
 intros. apply Pgcdn_greatest; auto.
Qed.

(** As a consequence, the rests after division by gcd are relatively prime *)

Lemma Pggcd_greatest : forall a b,
 let (aa,bb) := snd (Pggcd a b) in
 forall p, (p|aa) -> (p|bb) -> p=1.
Proof.
 intros. generalize (Pgcd_greatest a b) (Pggcd_correct_divisors a b).
 rewrite <- Pggcd_gcd. destruct Pggcd as (g,(aa,bb)); simpl.
 intros H (EQa,EQb) p Hp1 Hp2; subst.
 assert (H' : (g*p | g)).
  apply H.
  destruct Hp1 as (r,Hr). exists r. now rewrite <- Hr, Pmult_assoc.
  destruct Hp2 as (r,Hr). exists r. now rewrite <- Hr, Pmult_assoc.
 destruct H' as (q,H').
 apply Pmult_1_inversion_l with q.
 apply Pmult_reg_l with g. now rewrite Pmult_assoc, Pmult_1_r.
Qed.
