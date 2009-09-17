(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(**********************************************************************)
(** The integer logarithms with base 2.

    There are three logarithms,
    depending on the rounding of the real 2-based logarithm:
    - [Log_inf]: [y = (Log_inf x) iff 2^y <= x < 2^(y+1)]
      i.e. [Log_inf x] is the biggest integer that is smaller than [Log x]
    - [Log_sup]: [y = (Log_sup x) iff 2^(y-1) < x <= 2^y]
      i.e. [Log_inf x] is the smallest integer that is bigger than [Log x]
    - [Log_nearest]: [y= (Log_nearest x) iff 2^(y-1/2) < x <= 2^(y+1/2)]
      i.e. [Log_nearest x] is the integer nearest from [Log x] *)

Require Import ZArith_base.
Require Import Omega.
Require Import Zcomplements.
Require Import Zpower.
Open Local Scope Z_scope.

Section Log_pos. (* Log of positive integers *)

  (** First we build [log_inf] and [log_sup] *)

  Fixpoint log_inf (p:positive) : Z :=
    match p with
      | xH => 0	(* 1 *)
      | xO q => Zsucc (log_inf q)	(* 2n *)
      | xI q => Zsucc (log_inf q)	(* 2n+1 *)
    end.

  Fixpoint log_sup (p:positive) : Z :=
    match p with
      | xH => 0	(* 1 *)
      | xO n => Zsucc (log_sup n) (* 2n *)
      | xI n => Zsucc (Zsucc (log_inf n))	(* 2n+1 *)
    end.

  Hint Unfold log_inf log_sup.

  (** Then we give the specifications of [log_inf] and [log_sup]
    and prove their validity *)

  Hint Resolve Zle_trans: zarith.

  Theorem log_inf_correct :
    forall x:positive,
      0 <= log_inf x /\ two_p (log_inf x) <= Zpos x < two_p (Zsucc (log_inf x)).
  Proof.
    simple induction x; intros; simpl in |- *;
      [ elim H; intros Hp HR; clear H; split;
	[ auto with zarith
	  | rewrite two_p_S with (x := Zsucc (log_inf p)) by (apply Zle_le_succ; trivial);
	    rewrite two_p_S by trivial;
	    rewrite two_p_S in HR by trivial; rewrite (BinInt.Zpos_xI p);
		omega ]
	| elim H; intros Hp HR; clear H; split;
	  [ auto with zarith
	    | rewrite two_p_S with (x := Zsucc (log_inf p)) by (apply Zle_le_succ; trivial);
	      rewrite two_p_S by trivial;
	      rewrite two_p_S in HR by trivial; rewrite (BinInt.Zpos_xO p);
		  omega ]
	| unfold two_power_pos in |- *; unfold shift_pos in |- *; simpl in |- *;
	  omega ].
  Qed.

  Definition log_inf_correct1 (p:positive) := proj1 (log_inf_correct p).
  Definition log_inf_correct2 (p:positive) := proj2 (log_inf_correct p).

  Opaque log_inf_correct1 log_inf_correct2.

  Hint Resolve log_inf_correct1 log_inf_correct2: zarith.

  Lemma log_sup_correct1 : forall p:positive, 0 <= log_sup p.
  Proof.
    simple induction p; intros; simpl in |- *; auto with zarith.
  Qed.

  (** For every [p], either [p] is a power of two and [(log_inf p)=(log_sup p)]
      either [(log_sup p)=(log_inf p)+1] *)

  Theorem log_sup_log_inf :
    forall p:positive,
      IF Zpos p = two_p (log_inf p) then Zpos p = two_p (log_sup p)
    else log_sup p = Zsucc (log_inf p).
  Proof.
    simple induction p; intros;
      [ elim H; right; simpl in |- *;
	rewrite (two_p_S (log_inf p0) (log_inf_correct1 p0));
	  rewrite BinInt.Zpos_xI; unfold Zsucc in |- *; omega
	| elim H; clear H; intro Hif;
	  [ left; simpl in |- *;
	    rewrite (two_p_S (log_inf p0) (log_inf_correct1 p0));
	      rewrite (two_p_S (log_sup p0) (log_sup_correct1 p0));
		rewrite <- (proj1 Hif); rewrite <- (proj2 Hif);
		  auto
	    | right; simpl in |- *;
	      rewrite (two_p_S (log_inf p0) (log_inf_correct1 p0));
		rewrite BinInt.Zpos_xO; unfold Zsucc in |- *;
		  omega ]
	| left; auto ].
  Qed.

  Theorem log_sup_correct2 :
    forall x:positive, two_p (Zpred (log_sup x)) < Zpos x <= two_p (log_sup x).
  Proof.
    intro.
    elim (log_sup_log_inf x).
    (* x is a power of two and [log_sup = log_inf] *)
    intros [E1 E2]; rewrite E2.
    split; [ apply two_p_pred; apply log_sup_correct1 | apply Zle_refl ].
    intros [E1 E2]; rewrite E2.
    rewrite <- (Zpred_succ (log_inf x)).
    generalize (log_inf_correct2 x); omega.
  Qed.

  Lemma log_inf_le_log_sup : forall p:positive, log_inf p <= log_sup p.
  Proof.
    simple induction p; simpl in |- *; intros; omega.
  Qed.

  Lemma log_sup_le_Slog_inf : forall p:positive, log_sup p <= Zsucc (log_inf p).
  Proof.
    simple induction p; simpl in |- *; intros; omega.
  Qed.

  (** Now it's possible to specify and build the [Log] rounded to the nearest *)

  Fixpoint log_near (x:positive) : Z :=
    match x with
      | xH => 0
      | xO xH => 1
      | xI xH => 2
      | xO y => Zsucc (log_near y)
      | xI y => Zsucc (log_near y)
    end.

  Theorem log_near_correct1 : forall p:positive, 0 <= log_near p.
  Proof.
    simple induction p; simpl in |- *; intros;
      [ elim p0; auto with zarith
	| elim p0; auto with zarith
	| trivial with zarith ].
    intros; apply Zle_le_succ.
    generalize H0; elim p1; intros; simpl in |- *;
      [ assumption | assumption | apply Zorder.Zle_0_pos ].
    intros; apply Zle_le_succ.
    generalize H0; elim p1; intros; simpl in |- *;
      [ assumption | assumption | apply Zorder.Zle_0_pos ].
  Qed.

  Theorem log_near_correct2 :
    forall p:positive, log_near p = log_inf p \/ log_near p = log_sup p.
  Proof.
    simple induction p.
    intros p0 [Einf| Esup].
    simpl in |- *. rewrite Einf.
    case p0; [ left | left | right ]; reflexivity.
    simpl in |- *; rewrite Esup.
    elim (log_sup_log_inf p0).
    generalize (log_inf_le_log_sup p0).
    generalize (log_sup_le_Slog_inf p0).
    case p0; auto with zarith.
    intros; omega.
    case p0; intros; auto with zarith.
    intros p0 [Einf| Esup].
    simpl in |- *.
    repeat rewrite Einf.
    case p0; intros; auto with zarith.
    simpl in |- *.
    repeat rewrite Esup.
    case p0; intros; auto with zarith.
    auto.
  Qed.

End Log_pos.

Section divers.

  (** Number of significative digits. *)

  Definition N_digits (x:Z) :=
    match x with
      | Zpos p => log_inf p
      | Zneg p => log_inf p
      | Z0 => 0
    end.

  Lemma ZERO_le_N_digits : forall x:Z, 0 <= N_digits x.
  Proof.
    simple induction x; simpl in |- *;
      [ apply Zle_refl | exact log_inf_correct1 | exact log_inf_correct1 ].
  Qed.

  Lemma log_inf_shift_nat : forall n:nat, log_inf (shift_nat n 1) = Z_of_nat n.
  Proof.
    simple induction n; intros;
      [ try trivial | rewrite Znat.inj_S; rewrite <- H; reflexivity ].
  Qed.

  Lemma log_sup_shift_nat : forall n:nat, log_sup (shift_nat n 1) = Z_of_nat n.
  Proof.
    simple induction n; intros;
      [ try trivial | rewrite Znat.inj_S; rewrite <- H; reflexivity ].
  Qed.

  (** [Is_power p] means that p is a power of two *)
  Fixpoint Is_power (p:positive) : Prop :=
    match p with
      | xH => True
      | xO q => Is_power q
      | xI q => False
    end.

  Lemma Is_power_correct :
    forall p:positive, Is_power p <-> (exists y : nat, p = shift_nat y 1).
  Proof.
    split;
      [ elim p;
	[ simpl in |- *; tauto
	  | simpl in |- *; intros; generalize (H H0); intro H1; elim H1;
	    intros y0 Hy0; exists (S y0); rewrite Hy0; reflexivity
	  | intro; exists 0%nat; reflexivity ]
	| intros; elim H; intros; rewrite H0; elim x; intros; simpl in |- *; trivial ].
  Qed.

  Lemma Is_power_or : forall p:positive, Is_power p \/ ~ Is_power p.
  Proof.
    simple induction p;
      [ intros; right; simpl in |- *; tauto
	| intros; elim H;
	  [ intros; left; simpl in |- *; exact H0
	    | intros; right; simpl in |- *; exact H0 ]
	| left; simpl in |- *; trivial ].
  Qed.

End divers.






