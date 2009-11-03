(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $$ i*)

(**********************************************************************)
(** Binary Integers (Pierre Crégut, CNET, Lannion, France)            *)
(**********************************************************************)

Require Export BinPos.
Require Export BinInt.
Require Import Lt.
Require Import Gt.
Require Import Plus.
Require Import Mult.

Open Local Scope Z_scope.

(***************************)
(** * Comparison on integers *)

Lemma Zcompare_refl : forall n:Z, (n ?= n) = Eq.
Proof.
  intro x; destruct x as [| p| p]; simpl in |- *;
    [ reflexivity | apply Pcompare_refl | rewrite Pcompare_refl; reflexivity ].
Qed.

Lemma Zcompare_Eq_eq : forall n m:Z, (n ?= m) = Eq -> n = m.
Proof.
  intros x y; destruct x as [| x'| x']; destruct y as [| y'| y']; simpl in |- *;
    intro H; reflexivity || (try discriminate H);
      [ rewrite (Pcompare_Eq_eq x' y' H); reflexivity
	| rewrite (Pcompare_Eq_eq x' y');
	  [ reflexivity
	    | destruct ((x' ?= y')%positive Eq); reflexivity || discriminate ] ].
Qed.

Ltac destr_zcompare :=
 match goal with |- context [Zcompare ?x ?y] =>
  let H := fresh "H" in
  case_eq (Zcompare x y); intro H;
   [generalize (Zcompare_Eq_eq _ _ H); clear H; intro H |
    change (x<y)%Z in H |
    change (x>y)%Z in H ]
 end.

Lemma Zcompare_Eq_iff_eq : forall n m:Z, (n ?= m) = Eq <-> n = m.
Proof.
  intros x y; split; intro E;
    [ apply Zcompare_Eq_eq; assumption | rewrite E; apply Zcompare_refl ].
Qed.

Lemma Zcompare_antisym : forall n m:Z, CompOpp (n ?= m) = (m ?= n).
Proof.
  intros x y; destruct x; destruct y; simpl in |- *;
    reflexivity || discriminate H || rewrite Pcompare_antisym;
      reflexivity.
Qed.

Lemma Zcompare_Gt_Lt_antisym : forall n m:Z, (n ?= m) = Gt <-> (m ?= n) = Lt.
Proof.
  intros x y.
  rewrite <- Zcompare_antisym. change Gt with (CompOpp Lt).
  split.
  auto using CompOpp_inj.
  intros; f_equal; auto.
Qed.

Lemma Zcompare_spec : forall n m, CompSpec eq Zlt n m (n ?= m).
Proof.
  intros.
  destruct (n?=m) as [ ]_eqn:H; constructor; auto.
  apply Zcompare_Eq_eq; auto.
  red; rewrite <- Zcompare_antisym, H; auto.
Qed.


(** * Transitivity of comparison *)

Lemma Zcompare_Lt_trans :
  forall n m p:Z, (n ?= m) = Lt -> (m ?= p) = Lt -> (n ?= p) = Lt.
Proof.
  intros x y z; case x; case y; case z; simpl;
    try discriminate; auto with arith.
  intros; eapply Plt_trans; eauto.
  intros p q r; rewrite 3 Pcompare_antisym; simpl.
  intros; eapply Plt_trans; eauto.
Qed.

Lemma Zcompare_Gt_trans :
  forall n m p:Z, (n ?= m) = Gt -> (m ?= p) = Gt -> (n ?= p) = Gt.
Proof.
  intros n m p Hnm Hmp.
  apply <- Zcompare_Gt_Lt_antisym.
  apply -> Zcompare_Gt_Lt_antisym in Hnm.
  apply -> Zcompare_Gt_Lt_antisym in Hmp.
  eapply Zcompare_Lt_trans; eauto.
Qed.

(** * Comparison and opposite *)

Lemma Zcompare_opp : forall n m:Z, (n ?= m) = (- m ?= - n).
Proof.
  intros x y; case x; case y; simpl in |- *; auto with arith; intros;
    rewrite <- ZC4; trivial with arith.
Qed.

Hint Local Resolve Pcompare_refl.

(** * Comparison first-order specification *)

Lemma Zcompare_Gt_spec :
  forall n m:Z, (n ?= m) = Gt ->  exists h : positive, n + - m = Zpos h.
Proof.
  intros x y; case x; case y;
    [ simpl in |- *; intros H; discriminate H
      | simpl in |- *; intros p H; discriminate H
      | intros p H; exists p; simpl in |- *; auto with arith
      | intros p H; exists p; simpl in |- *; auto with arith
      | intros q p H; exists (p - q)%positive; unfold Zplus, Zopp in |- *;
	unfold Zcompare in H; rewrite H; trivial with arith
      | intros q p H; exists (p + q)%positive; simpl in |- *; trivial with arith
      | simpl in |- *; intros p H; discriminate H
      | simpl in |- *; intros q p H; discriminate H
      | unfold Zcompare in |- *; intros q p; rewrite <- ZC4; intros H;
	exists (q - p)%positive; simpl in |- *; rewrite (ZC1 q p H);
	  trivial with arith ].
Qed.

(** * Comparison and addition *)

Lemma weaken_Zcompare_Zplus_compatible :
  (forall (n m:Z) (p:positive), (Zpos p + n ?= Zpos p + m) = (n ?= m)) ->
  forall n m p:Z, (p + n ?= p + m) = (n ?= m).
Proof.
  intros H x y z; destruct z;
    [ reflexivity
      | apply H
      | rewrite (Zcompare_opp x y); rewrite Zcompare_opp;
	do 2 rewrite Zopp_plus_distr; rewrite Zopp_neg;
	  apply H ].
Qed.

Hint Local Resolve ZC4.

Lemma weak_Zcompare_Zplus_compatible :
  forall (n m:Z) (p:positive), (Zpos p + n ?= Zpos p + m) = (n ?= m).
Proof.
  intros x y z; case x; case y; simpl in |- *; auto with arith;
    [ intros p; apply nat_of_P_lt_Lt_compare_complement_morphism; apply ZL17
      | intros p; ElimPcompare z p; intros E; rewrite E; auto with arith;
	apply nat_of_P_gt_Gt_compare_complement_morphism;
	  rewrite nat_of_P_minus_morphism;
	    [ unfold gt in |- *; apply ZL16 | assumption ]
      | intros p; ElimPcompare z p; intros E; auto with arith;
	apply nat_of_P_gt_Gt_compare_complement_morphism;
	  unfold gt in |- *; apply ZL17
      | intros p q; ElimPcompare q p; intros E; rewrite E;
	[ rewrite (Pcompare_Eq_eq q p E); apply Pcompare_refl
	  | apply nat_of_P_lt_Lt_compare_complement_morphism;
	    do 2 rewrite nat_of_P_plus_morphism; apply plus_lt_compat_l;
	      apply nat_of_P_lt_Lt_compare_morphism with (1 := E)
	  | apply nat_of_P_gt_Gt_compare_complement_morphism; unfold gt in |- *;
	    do 2 rewrite nat_of_P_plus_morphism; apply plus_lt_compat_l;
	      exact (nat_of_P_gt_Gt_compare_morphism q p E) ]
      | intros p q; ElimPcompare z p; intros E; rewrite E; auto with arith;
	apply nat_of_P_gt_Gt_compare_complement_morphism;
	  rewrite nat_of_P_minus_morphism;
	    [ unfold gt in |- *; apply lt_trans with (m := nat_of_P z);
	      [ apply ZL16 | apply ZL17 ]
	      | assumption ]
      | intros p; ElimPcompare z p; intros E; rewrite E; auto with arith;
	simpl in |- *; apply nat_of_P_lt_Lt_compare_complement_morphism;
	  rewrite nat_of_P_minus_morphism; [ apply ZL16 | assumption ]
      | intros p q; ElimPcompare z q; intros E; rewrite E; auto with arith;
	simpl in |- *; apply nat_of_P_lt_Lt_compare_complement_morphism;
	  rewrite nat_of_P_minus_morphism;
	    [ apply lt_trans with (m := nat_of_P z); [ apply ZL16 | apply ZL17 ]
	      | assumption ]
      | intros p q; ElimPcompare z q; intros E0; rewrite E0; ElimPcompare z p;
	intros E1; rewrite E1; ElimPcompare q p; intros E2;
	  rewrite E2; auto with arith;
	    [ absurd ((q ?= p)%positive Eq = Lt);
	      [ rewrite <- (Pcompare_Eq_eq z q E0);
		rewrite <- (Pcompare_Eq_eq z p E1); rewrite (Pcompare_refl z);
		  discriminate
		| assumption ]
	      | absurd ((q ?= p)%positive Eq = Gt);
		[ rewrite <- (Pcompare_Eq_eq z q E0);
		  rewrite <- (Pcompare_Eq_eq z p E1); rewrite (Pcompare_refl z);
		    discriminate
		  | assumption ]
	      | absurd ((z ?= p)%positive Eq = Lt);
		[ rewrite (Pcompare_Eq_eq z q E0); rewrite <- (Pcompare_Eq_eq q p E2);
		  rewrite (Pcompare_refl q); discriminate
		  | assumption ]
	      | absurd ((z ?= p)%positive Eq = Lt);
		[ rewrite (Pcompare_Eq_eq z q E0); rewrite E2; discriminate
		  | assumption ]
	      | absurd ((z ?= p)%positive Eq = Gt);
		[ rewrite (Pcompare_Eq_eq z q E0); rewrite <- (Pcompare_Eq_eq q p E2);
		  rewrite (Pcompare_refl q); discriminate
		  | assumption ]
	      | absurd ((z ?= p)%positive Eq = Gt);
		[ rewrite (Pcompare_Eq_eq z q E0); rewrite E2; discriminate
		  | assumption ]
	      | absurd ((z ?= q)%positive Eq = Lt);
		[ rewrite (Pcompare_Eq_eq z p E1); rewrite (Pcompare_Eq_eq q p E2);
		  rewrite (Pcompare_refl p); discriminate
		  | assumption ]
	      | absurd ((p ?= q)%positive Eq = Gt);
		[ rewrite <- (Pcompare_Eq_eq z p E1); rewrite E0; discriminate
		  | apply ZC2; assumption ]
	      | simpl in |- *; rewrite (Pcompare_Eq_eq q p E2);
		rewrite (Pcompare_refl (p - z)); auto with arith
	      | simpl in |- *; rewrite <- ZC4;
		apply nat_of_P_gt_Gt_compare_complement_morphism;
		  rewrite nat_of_P_minus_morphism;
		    [ rewrite nat_of_P_minus_morphism;
		      [ unfold gt in |- *; apply plus_lt_reg_l with (p := nat_of_P z);
			rewrite le_plus_minus_r;
			  [ rewrite le_plus_minus_r;
			    [ apply nat_of_P_lt_Lt_compare_morphism; assumption
			      | apply lt_le_weak; apply nat_of_P_lt_Lt_compare_morphism;
				assumption ]
			    | apply lt_le_weak; apply nat_of_P_lt_Lt_compare_morphism;
			      assumption ]
			| apply ZC2; assumption ]
		      | apply ZC2; assumption ]
	      | simpl in |- *; rewrite <- ZC4;
		apply nat_of_P_lt_Lt_compare_complement_morphism;
		  rewrite nat_of_P_minus_morphism;
		    [ rewrite nat_of_P_minus_morphism;
		      [ apply plus_lt_reg_l with (p := nat_of_P z);
			rewrite le_plus_minus_r;
			  [ rewrite le_plus_minus_r;
			    [ apply nat_of_P_lt_Lt_compare_morphism; apply ZC1;
			      assumption
			      | apply lt_le_weak; apply nat_of_P_lt_Lt_compare_morphism;
				assumption ]
			    | apply lt_le_weak; apply nat_of_P_lt_Lt_compare_morphism;
			      assumption ]
			| apply ZC2; assumption ]
		      | apply ZC2; assumption ]
	      | absurd ((z ?= q)%positive Eq = Lt);
		[ rewrite (Pcompare_Eq_eq q p E2); rewrite E1; discriminate
		  | assumption ]
	      | absurd ((q ?= p)%positive Eq = Lt);
		[ cut ((q ?= p)%positive Eq = Gt);
		  [ intros E; rewrite E; discriminate
		    | apply nat_of_P_gt_Gt_compare_complement_morphism;
		      unfold gt in |- *; apply lt_trans with (m := nat_of_P z);
			[ apply nat_of_P_lt_Lt_compare_morphism; apply ZC1; assumption
			  | apply nat_of_P_lt_Lt_compare_morphism; assumption ] ]
		  | assumption ]
	      | absurd ((z ?= q)%positive Eq = Gt);
		[ rewrite (Pcompare_Eq_eq z p E1); rewrite (Pcompare_Eq_eq q p E2);
		  rewrite (Pcompare_refl p); discriminate
		  | assumption ]
	      | absurd ((z ?= q)%positive Eq = Gt);
		[ rewrite (Pcompare_Eq_eq z p E1); rewrite ZC1;
		  [ discriminate | assumption ]
		  | assumption ]
	      | absurd ((z ?= q)%positive Eq = Gt);
		[ rewrite (Pcompare_Eq_eq q p E2); rewrite E1; discriminate
		  | assumption ]
	      | absurd ((q ?= p)%positive Eq = Gt);
		[ rewrite ZC1;
		  [ discriminate
		    | apply nat_of_P_gt_Gt_compare_complement_morphism;
		      unfold gt in |- *; apply lt_trans with (m := nat_of_P z);
			[ apply nat_of_P_lt_Lt_compare_morphism; apply ZC1; assumption
			  | apply nat_of_P_lt_Lt_compare_morphism; assumption ] ]
		  | assumption ]
	      | simpl in |- *; rewrite (Pcompare_Eq_eq q p E2); apply Pcompare_refl
	      | simpl in |- *; apply nat_of_P_gt_Gt_compare_complement_morphism;
		unfold gt in |- *; rewrite nat_of_P_minus_morphism;
		  [ rewrite nat_of_P_minus_morphism;
		    [ apply plus_lt_reg_l with (p := nat_of_P p);
		      rewrite le_plus_minus_r;
			[ rewrite plus_comm; apply plus_lt_reg_l with (p := nat_of_P q);
			  rewrite plus_assoc; rewrite le_plus_minus_r;
			    [ rewrite (plus_comm (nat_of_P q)); apply plus_lt_compat_l;
			      apply nat_of_P_lt_Lt_compare_morphism;
				assumption
			      | apply lt_le_weak; apply nat_of_P_lt_Lt_compare_morphism;
				apply ZC1; assumption ]
			  | apply lt_le_weak; apply nat_of_P_lt_Lt_compare_morphism;
			    apply ZC1; assumption ]
		      | assumption ]
		    | assumption ]
	      | simpl in |- *; apply nat_of_P_lt_Lt_compare_complement_morphism;
		rewrite nat_of_P_minus_morphism;
		  [ rewrite nat_of_P_minus_morphism;
		    [ apply plus_lt_reg_l with (p := nat_of_P q);
		      rewrite le_plus_minus_r;
			[ rewrite plus_comm; apply plus_lt_reg_l with (p := nat_of_P p);
			  rewrite plus_assoc; rewrite le_plus_minus_r;
			    [ rewrite (plus_comm (nat_of_P p)); apply plus_lt_compat_l;
			      apply nat_of_P_lt_Lt_compare_morphism;
				apply ZC1; assumption
			      | apply lt_le_weak; apply nat_of_P_lt_Lt_compare_morphism;
				apply ZC1; assumption ]
			  | apply lt_le_weak; apply nat_of_P_lt_Lt_compare_morphism;
			    apply ZC1; assumption ]
		      | assumption ]
		    | assumption ] ] ].
Qed.

Lemma Zcompare_plus_compat : forall n m p:Z, (p + n ?= p + m) = (n ?= m).
Proof.
  exact (weaken_Zcompare_Zplus_compatible weak_Zcompare_Zplus_compatible).
Qed.

Lemma Zplus_compare_compat :
  forall (r:comparison) (n m p q:Z),
    (n ?= m) = r -> (p ?= q) = r -> (n + p ?= m + q) = r.
Proof.
  intros r x y z t; case r;
    [ intros H1 H2; elim (Zcompare_Eq_iff_eq x y); elim (Zcompare_Eq_iff_eq z t);
      intros H3 H4 H5 H6; rewrite H3;
	[ rewrite H5;
	  [ elim (Zcompare_Eq_iff_eq (y + t) (y + t)); auto with arith
	    | auto with arith ]
	  | auto with arith ]
      | intros H1 H2; elim (Zcompare_Gt_Lt_antisym (y + t) (x + z)); intros H3 H4;
	apply H3; apply Zcompare_Gt_trans with (m := y + z);
	  [ rewrite Zcompare_plus_compat; elim (Zcompare_Gt_Lt_antisym t z);
	    auto with arith
	    | do 2 rewrite <- (Zplus_comm z); rewrite Zcompare_plus_compat;
	      elim (Zcompare_Gt_Lt_antisym y x); auto with arith ]
      | intros H1 H2; apply Zcompare_Gt_trans with (m := x + t);
	[ rewrite Zcompare_plus_compat; assumption
	  | do 2 rewrite <- (Zplus_comm t); rewrite Zcompare_plus_compat;
	    assumption ] ].
Qed.

Lemma Zcompare_succ_Gt : forall n:Z, (Zsucc n ?= n) = Gt.
Proof.
  intro x; unfold Zsucc in |- *; pattern x at 2 in |- *;
    rewrite <- (Zplus_0_r x); rewrite Zcompare_plus_compat;
      reflexivity.
Qed.

Lemma Zcompare_Gt_not_Lt : forall n m:Z, (n ?= m) = Gt <-> (n ?= m + 1) <> Lt.
Proof.
  intros x y; split;
    [ intro H; elim_compare x (y + 1);
      [ intro H1; rewrite H1; discriminate
	| intros H1; elim Zcompare_Gt_spec with (1 := H); intros h H2;
	  absurd ((nat_of_P h > 0)%nat /\ (nat_of_P h < 1)%nat);
	    [ unfold not in |- *; intros H3; elim H3; intros H4 H5;
              absurd (nat_of_P h > 0)%nat;
		[ unfold gt in |- *; apply le_not_lt; apply le_S_n; exact H5
		  | assumption ]
	      | split;
		[ elim (ZL4 h); intros i H3; rewrite H3; apply gt_Sn_O
		  | change (nat_of_P h < nat_of_P 1)%nat in |- *;
		    apply nat_of_P_lt_Lt_compare_morphism;
		      change ((Zpos h ?= 1) = Lt) in |- *; rewrite <- H2;
			rewrite <- (fun m n:Z => Zcompare_plus_compat m n y);
			  rewrite (Zplus_comm x); rewrite Zplus_assoc;
			    rewrite Zplus_opp_r; simpl in |- *; exact H1 ] ]
	| intros H1; rewrite H1; discriminate ]
      | intros H; elim_compare x (y + 1);
	[ intros H1; elim (Zcompare_Eq_iff_eq x (y + 1)); intros H2 H3;
	  rewrite (H2 H1); exact (Zcompare_succ_Gt y)
	  | intros H1; absurd ((x ?= y + 1) = Lt); assumption
	  | intros H1; apply Zcompare_Gt_trans with (m := Zsucc y);
	    [ exact H1 | exact (Zcompare_succ_Gt y) ] ] ].
Qed.

(** * Successor and comparison *)

Lemma Zcompare_succ_compat : forall n m:Z, (Zsucc n ?= Zsucc m) = (n ?= m).
Proof.
  intros n m; unfold Zsucc in |- *; do 2 rewrite (fun t:Z => Zplus_comm t 1);
    rewrite Zcompare_plus_compat; auto with arith.
Qed.

(** * Multiplication and comparison *)

Lemma Zcompare_mult_compat :
  forall (p:positive) (n m:Z), (Zpos p * n ?= Zpos p * m) = (n ?= m).
Proof.
  intros x; induction x as [p H| p H| ];
    [ intros y z; cut (Zpos (xI p) = Zpos p + Zpos p + 1);
      [ intros E; rewrite E; do 4 rewrite Zmult_plus_distr_l;
	do 2 rewrite Zmult_1_l; apply Zplus_compare_compat;
	  [ apply Zplus_compare_compat; apply H | trivial with arith ]
	| simpl in |- *; rewrite (Pplus_diag p); trivial with arith ]
      | intros y z; cut (Zpos (xO p) = Zpos p + Zpos p);
	[ intros E; rewrite E; do 2 rewrite Zmult_plus_distr_l;
	  apply Zplus_compare_compat; apply H
	  | simpl in |- *; rewrite (Pplus_diag p); trivial with arith ]
      | intros y z; do 2 rewrite Zmult_1_l; trivial with arith ].
Qed.


(** * Reverting [x ?= y] to trichotomy *)

Lemma rename :
  forall (A:Type) (P:A -> Prop) (x:A), (forall y:A, x = y -> P y) -> P x.
Proof.
  auto with arith.
Qed.

Lemma Zcompare_elim :
  forall (c1 c2 c3:Prop) (n m:Z),
    (n = m -> c1) ->
    (n < m -> c2) ->
    (n > m -> c3) -> match n ?= m with
                       | Eq => c1
                       | Lt => c2
                       | Gt => c3
                     end.
Proof.
  intros c1 c2 c3 x y; intros.
  apply rename with (x := x ?= y); intro r; elim r;
    [ intro; apply H; apply (Zcompare_Eq_eq x y); assumption
      | unfold Zlt in H0; assumption
      | unfold Zgt in H1; assumption ].
Qed.

Lemma Zcompare_eq_case :
  forall (c1 c2 c3:Prop) (n m:Z),
    c1 -> n = m -> match n ?= m with
                     | Eq => c1
                     | Lt => c2
                     | Gt => c3
                   end.
Proof.
  intros c1 c2 c3 x y; intros.
  rewrite H0; rewrite Zcompare_refl.
  assumption.
Qed.

(** * Decompose an egality between two [?=] relations into 3 implications *)

Lemma Zcompare_egal_dec :
  forall n m p q:Z,
    (n < m -> p < q) ->
    ((n ?= m) = Eq -> (p ?= q) = Eq) ->
    (n > m -> p > q) -> (n ?= m) = (p ?= q).
Proof.
  intros x1 y1 x2 y2.
  unfold Zgt in |- *; unfold Zlt in |- *; case (x1 ?= y1); case (x2 ?= y2);
    auto with arith; symmetry  in |- *; auto with arith.
Qed.

(** * Relating [x ?= y] to [Zle], [Zlt], [Zge] or [Zgt] *)

Lemma Zle_compare :
  forall n m:Z,
    n <= m -> match n ?= m with
		| Eq => True
		| Lt => True
		| Gt => False
              end.
Proof.
  intros x y; unfold Zle in |- *; elim (x ?= y); auto with arith.
Qed.

Lemma Zlt_compare :
  forall n m:Z,
   n < m -> match n ?= m with
              | Eq => False
              | Lt => True
              | Gt => False
            end.
Proof.
  intros x y; unfold Zlt in |- *; elim (x ?= y); intros;
    discriminate || trivial with arith.
Qed.

Lemma Zge_compare :
  forall n m:Z,
    n >= m -> match n ?= m with
		| Eq => True
		| Lt => False
		| Gt => True
              end.
Proof.
  intros x y; unfold Zge in |- *; elim (x ?= y); auto with arith.
Qed.

Lemma Zgt_compare :
  forall n m:Z,
    n > m -> match n ?= m with
               | Eq => False
               | Lt => False
               | Gt => True
             end.
Proof.
  intros x y; unfold Zgt in |- *; elim (x ?= y); intros;
    discriminate || trivial with arith.
Qed.

(*********************)
(** * Other properties *)

Lemma Zmult_compare_compat_l :
  forall n m p:Z, p > 0 -> (n ?= m) = (p * n ?= p * m).
Proof.
  intros x y z H; destruct z.
  discriminate H.
  rewrite Zcompare_mult_compat; reflexivity.
  discriminate H.
Qed.

Lemma Zmult_compare_compat_r :
  forall n m p:Z, p > 0 -> (n ?= m) = (n * p ?= m * p).
Proof.
  intros x y z H; rewrite (Zmult_comm x z); rewrite (Zmult_comm y z);
    apply Zmult_compare_compat_l; assumption.
Qed.

