(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Wf_nat.
Require Import ZArith_base.
Require Export Zpow_def.
Require Import Omega.
Require Import Zcomplements.
Open Local Scope Z_scope.

Infix "^" := Zpower : Z_scope.

(** * Definition of powers over [Z]*)

(** [Zpower_nat z n] is the n-th power of [z] when [n] is an unary
    integer (type [nat]) and [z] a signed integer (type [Z]) *)

Definition Zpower_nat (z:Z) (n:nat) := iter_nat n Z (fun x:Z => z * x) 1.

(** [Zpower_nat_is_exp] says [Zpower_nat] is a morphism for
    [plus : nat->nat] and [Zmult : Z->Z] *)

Lemma Zpower_nat_is_exp :
  forall (n m:nat) (z:Z),
    Zpower_nat z (n + m) = Zpower_nat z n * Zpower_nat z m.
Proof.
  intros; elim n;
   [ simpl in |- *; elim (Zpower_nat z m); auto with zarith
     | unfold Zpower_nat in |- *; intros; simpl in |- *; rewrite H;
       apply Zmult_assoc ].
Qed.

(** This theorem shows that powers of unary and binary integers
   are the same thing, modulo the function convert : [positive -> nat] *)

Lemma Zpower_pos_nat :
  forall (z:Z) (p:positive), Zpower_pos z p = Zpower_nat z (nat_of_P p).
Proof.
  intros; unfold Zpower_pos in |- *; unfold Zpower_nat in |- *;
    apply iter_nat_of_P.
Qed.

(** Using the theorem [Zpower_pos_nat] and the lemma [Zpower_nat_is_exp] we
   deduce that the function [[n:positive](Zpower_pos z n)] is a morphism
   for [add : positive->positive] and [Zmult : Z->Z] *)

Lemma Zpower_pos_is_exp :
  forall (n m:positive) (z:Z),
    Zpower_pos z (n + m) = Zpower_pos z n * Zpower_pos z m.
Proof.
  intros.
  rewrite (Zpower_pos_nat z n).
  rewrite (Zpower_pos_nat z m).
  rewrite (Zpower_pos_nat z (n + m)).
  rewrite (nat_of_P_plus_morphism n m).
  apply Zpower_nat_is_exp.
Qed.

Hint Immediate Zpower_nat_is_exp Zpower_pos_is_exp : zarith.
Hint Unfold Zpower_pos Zpower_nat: zarith.

Theorem Zpower_exp :
  forall x n m:Z, n >= 0 -> m >= 0 -> x ^ (n + m) = x ^ n * x ^ m.
Proof.
  destruct n; destruct m; auto with zarith.
  simpl; intros; apply Zred_factor0.
  simpl; auto with zarith.
  intros; compute in H0; elim H0; auto.
  intros; compute in H; elim H; auto.
Qed.

Section Powers_of_2.

  (** * Powers of 2 *)

  (** For the powers of two, that will be widely used, a more direct
      calculus is possible. We will also prove some properties such
      as [(x:positive) x < 2^x] that are true for all integers bigger
      than 2 but more difficult to prove and useless. *)

  (** [shift n m] computes [2^n * m], or [m] shifted by [n] positions *)

  Definition shift_nat (n:nat) (z:positive) := iter_nat n positive xO z.
  Definition shift_pos (n z:positive) := iter_pos n positive xO z.
  Definition shift (n:Z) (z:positive) :=
    match n with
      | Z0 => z
      | Zpos p => iter_pos p positive xO z
      | Zneg p => z
    end.

  Definition two_power_nat (n:nat) := Zpos (shift_nat n 1).
  Definition two_power_pos (x:positive) := Zpos (shift_pos x 1).

  Lemma two_power_nat_S :
    forall n:nat, two_power_nat (S n) = 2 * two_power_nat n.
  Proof.
    intro; simpl in |- *; apply refl_equal.
  Qed.

  Lemma shift_nat_plus :
    forall (n m:nat) (x:positive),
      shift_nat (n + m) x = shift_nat n (shift_nat m x).
  Proof.
    intros; unfold shift_nat in |- *; apply iter_nat_plus.
  Qed.

  Theorem shift_nat_correct :
    forall (n:nat) (x:positive), Zpos (shift_nat n x) = Zpower_nat 2 n * Zpos x.
  Proof.
    unfold shift_nat in |- *; simple induction n;
      [ simpl in |- *; trivial with zarith
	| intros; replace (Zpower_nat 2 (S n0)) with (2 * Zpower_nat 2 n0);
	  [ rewrite <- Zmult_assoc; rewrite <- (H x); simpl in |- *; reflexivity
	    | auto with zarith ] ].
  Qed.

  Theorem two_power_nat_correct :
    forall n:nat, two_power_nat n = Zpower_nat 2 n.
  Proof.
    intro n.
    unfold two_power_nat in |- *.
    rewrite (shift_nat_correct n).
    omega.
  Qed.

  (** Second we show that [two_power_pos] and [two_power_nat] are the same *)
  Lemma shift_pos_nat :
    forall p x:positive, shift_pos p x = shift_nat (nat_of_P p) x.
  Proof.
    unfold shift_pos in |- *.
    unfold shift_nat in |- *.
    intros; apply iter_nat_of_P.
  Qed.

  Lemma two_power_pos_nat :
    forall p:positive, two_power_pos p = two_power_nat (nat_of_P p).
  Proof.
    intro; unfold two_power_pos in |- *; unfold two_power_nat in |- *.
    apply f_equal with (f := Zpos).
    apply shift_pos_nat.
  Qed.

  (** Then we deduce that [two_power_pos] is also correct *)

  Theorem shift_pos_correct :
    forall p x:positive, Zpos (shift_pos p x) = Zpower_pos 2 p * Zpos x.
  Proof.
    intros.
    rewrite (shift_pos_nat p x).
    rewrite (Zpower_pos_nat 2 p).
    apply shift_nat_correct.
  Qed.

  Theorem two_power_pos_correct :
    forall x:positive, two_power_pos x = Zpower_pos 2 x.
  Proof.
    intro.
    rewrite two_power_pos_nat.
    rewrite Zpower_pos_nat.
    apply two_power_nat_correct.
  Qed.

  (** Some consequences *)

  Theorem two_power_pos_is_exp :
    forall x y:positive,
      two_power_pos (x + y) = two_power_pos x * two_power_pos y.
  Proof.
    intros.
    rewrite (two_power_pos_correct (x + y)).
    rewrite (two_power_pos_correct x).
    rewrite (two_power_pos_correct y).
    apply Zpower_pos_is_exp.
  Qed.

  (** The exponentiation [z -> 2^z] for [z] a signed integer.
      For convenience, we assume that [2^z = 0] for all [z < 0]
      We could also define a inductive type [Log_result] with
      3 contructors [ Zero | Pos positive -> | minus_infty]
      but it's more complexe and not so useful. *)

  Definition two_p (x:Z) :=
    match x with
      | Z0 => 1
      | Zpos y => two_power_pos y
      | Zneg y => 0
    end.

  Theorem two_p_is_exp :
    forall x y:Z, 0 <= x -> 0 <= y -> two_p (x + y) = two_p x * two_p y.
  Proof.
    simple induction x;
      [ simple induction y; simpl in |- *; auto with zarith
	| simple induction y;
	  [ unfold two_p in |- *; rewrite (Zmult_comm (two_power_pos p) 1);
	    rewrite (Zmult_1_l (two_power_pos p)); auto with zarith
	    | unfold Zplus in |- *; unfold two_p in |- *; intros;
	      apply two_power_pos_is_exp
	    | intros; unfold Zle in H0; unfold Zcompare in H0;
	      absurd (Datatypes.Gt = Datatypes.Gt); trivial with zarith ]
	| simple induction y;
	  [ simpl in |- *; auto with zarith
	    | intros; unfold Zle in H; unfold Zcompare in H;
	      absurd (Datatypes.Gt = Datatypes.Gt); trivial with zarith
	    | intros; unfold Zle in H; unfold Zcompare in H;
	      absurd (Datatypes.Gt = Datatypes.Gt); trivial with zarith ] ].
  Qed.

  Lemma two_p_gt_ZERO : forall x:Z, 0 <= x -> two_p x > 0.
  Proof.
    simple induction x; intros;
      [ simpl in |- *; omega
	| simpl in |- *; unfold two_power_pos in |- *; apply Zorder.Zgt_pos_0
	| absurd (0 <= Zneg p);
	  [ simpl in |- *; unfold Zle in |- *; unfold Zcompare in |- *;
	    do 2 unfold not in |- *; auto with zarith
	    | assumption ] ].
  Qed.

  Lemma two_p_S : forall x:Z, 0 <= x -> two_p (Zsucc x) = 2 * two_p x.
  Proof.
    intros; unfold Zsucc in |- *.
    rewrite (two_p_is_exp x 1 H (Zorder.Zle_0_pos 1)).
    apply Zmult_comm.
  Qed.

  Lemma two_p_pred : forall x:Z, 0 <= x -> two_p (Zpred x) < two_p x.
  Proof.
    intros; apply natlike_ind with (P := fun x:Z => two_p (Zpred x) < two_p x);
      [ simpl in |- *; unfold Zlt in |- *; auto with zarith
	| intros; elim (Zle_lt_or_eq 0 x0 H0);
	  [ intros;
	    replace (two_p (Zpred (Zsucc x0))) with (two_p (Zsucc (Zpred x0)));
	      [ rewrite (two_p_S (Zpred x0));
		[ rewrite (two_p_S x0); [ omega | assumption ]
		  | apply Zorder.Zlt_0_le_0_pred; assumption ]
		| rewrite <- (Zsucc_pred x0); rewrite <- (Zpred_succ x0);
		  trivial with zarith ]
	    | intro Hx0; rewrite <- Hx0; simpl in |- *; unfold Zlt in |- *;
	      auto with zarith ]
	| assumption ].
  Qed.

  Lemma Zlt_lt_double : forall x y:Z, 0 <= x < y -> x < 2 * y.
    intros; omega. Qed.

  End Powers_of_2.

Hint Resolve two_p_gt_ZERO: zarith.
Hint Immediate two_p_pred two_p_S: zarith.

Section power_div_with_rest.

  (** * Division by a power of two. *)

  (** To [n:Z] and [p:positive], [q],[r] are associated such that
      [n = 2^p.q + r] and [0 <= r < 2^p] *)

  (** Invariant: [d*q + r = d'*q + r /\ d' = 2*d /\ 0<= r < d /\ 0 <= r' < d'] *)
  Definition Zdiv_rest_aux (qrd:Z * Z * Z) :=
    let (qr, d) := qrd in
      let (q, r) := qr in
	(match q with
	   | Z0 => (0, r)
	   | Zpos xH => (0, d + r)
	   | Zpos (xI n) => (Zpos n, d + r)
	   | Zpos (xO n) => (Zpos n, r)
	   | Zneg xH => (-1, d + r)
	   | Zneg (xI n) => (Zneg n - 1, d + r)
	   | Zneg (xO n) => (Zneg n, r)
	 end, 2 * d).

  Definition Zdiv_rest (x:Z) (p:positive) :=
    let (qr, d) := iter_pos p _ Zdiv_rest_aux (x, 0, 1) in qr.

  Lemma Zdiv_rest_correct1 :
    forall (x:Z) (p:positive),
      let (qr, d) := iter_pos p _ Zdiv_rest_aux (x, 0, 1) in d = two_power_pos p.
  Proof.
    intros x p; rewrite (iter_nat_of_P p _ Zdiv_rest_aux (x, 0, 1));
      rewrite (two_power_pos_nat p); elim (nat_of_P p);
	simpl in |- *;
	  [ trivial with zarith
	    | intro n; rewrite (two_power_nat_S n); unfold Zdiv_rest_aux at 2 in |- *;
	      elim (iter_nat n (Z * Z * Z) Zdiv_rest_aux (x, 0, 1));
		destruct a; intros; apply f_equal with (f := fun z:Z => 2 * z);
		  assumption ].
  Qed.

  Lemma Zdiv_rest_correct2 :
    forall (x:Z) (p:positive),
      let (qr, d) := iter_pos p _ Zdiv_rest_aux (x, 0, 1) in
	let (q, r) := qr in x = q * d + r /\ 0 <= r < d.
  Proof.
    intros;
      apply iter_pos_invariant with
	(f := Zdiv_rest_aux)
	(Inv := fun qrd:Z * Z * Z =>
          let (qr, d) := qrd in
            let (q, r) := qr in x = q * d + r /\ 0 <= r < d);
	[ intro x0; elim x0; intro y0; elim y0; intros q r d;
	  unfold Zdiv_rest_aux in |- *; elim q;
	    [ omega
	      | destruct p0;
		[ rewrite BinInt.Zpos_xI; intro; elim H; intros; split;
		  [ rewrite H0; rewrite Zplus_assoc; rewrite Zmult_plus_distr_l;
		    rewrite Zmult_1_l; rewrite Zmult_assoc;
		      rewrite (Zmult_comm (Zpos p0) 2); apply refl_equal
		    | omega ]
		  | rewrite BinInt.Zpos_xO; intro; elim H; intros; split;
		    [ rewrite H0; rewrite Zmult_assoc; rewrite (Zmult_comm (Zpos p0) 2);
		      apply refl_equal
		      | omega ]
		  | omega ]
	      | destruct p0;
		[ rewrite BinInt.Zneg_xI; unfold Zminus in |- *; intro; elim H; intros;
		  split;
		    [ rewrite H0; rewrite Zplus_assoc;
		      apply f_equal with (f := fun z:Z => z + r);
			do 2 rewrite Zmult_plus_distr_l; rewrite Zmult_assoc;
			  rewrite (Zmult_comm (Zneg p0) 2); rewrite <- Zplus_assoc;
			    apply f_equal with (f := fun z:Z => 2 * Zneg p0 * d + z);
			      omega
		      | omega ]
		  | rewrite BinInt.Zneg_xO; unfold Zminus in |- *; intro; elim H; intros;
		    split;
		      [ rewrite H0; rewrite Zmult_assoc; rewrite (Zmult_comm (Zneg p0) 2);
			apply refl_equal
			| omega ]
		  | omega ] ]
	  | omega ].
  Qed.

  Inductive Zdiv_rest_proofs (x:Z) (p:positive) : Set :=
    Zdiv_rest_proof :
    forall q r:Z,
      x = q * two_power_pos p + r ->
      0 <= r -> r < two_power_pos p -> Zdiv_rest_proofs x p.

  Lemma Zdiv_rest_correct : forall (x:Z) (p:positive), Zdiv_rest_proofs x p.
  Proof.
    intros x p.
    generalize (Zdiv_rest_correct1 x p); generalize (Zdiv_rest_correct2 x p).
    elim (iter_pos p (Z * Z * Z) Zdiv_rest_aux (x, 0, 1)).
    simple induction a.
    intros.
    elim H; intros H1 H2; clear H.
    rewrite H0 in H1; rewrite H0 in H2; elim H2; intros;
      apply Zdiv_rest_proof with (q := a0) (r := b); assumption.
  Qed.

End power_div_with_rest.
