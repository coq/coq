(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(***********************************************************)
(** Binary Integers (Pierre Crégut, CNET, Lannion, France) *)
(***********************************************************)

Require Export BinPos.
Require Export Pnat.
Require Import BinNat.
Require Import Plus.
Require Import Mult.

Unset Boxed Definitions.

(*****************************)
(** * Binary integer numbers *)

Inductive Z : Set :=
  | Z0 : Z
  | Zpos : positive -> Z
  | Zneg : positive -> Z.


(** Automatically open scope positive_scope for the constructors of Z *)
Delimit Scope Z_scope with Z.
Bind Scope Z_scope with Z.
Arguments Scope Zpos [positive_scope].
Arguments Scope Zneg [positive_scope].

(** ** Subtraction of positive into Z *)

Definition Zdouble_plus_one (x:Z) :=
  match x with
    | Z0 => Zpos 1
    | Zpos p => Zpos (xI p)
    | Zneg p => Zneg (Pdouble_minus_one p)
  end.

Definition Zdouble_minus_one (x:Z) :=
  match x with
    | Z0 => Zneg 1
    | Zneg p => Zneg (xI p)
    | Zpos p => Zpos (Pdouble_minus_one p)
  end.

Definition Zdouble (x:Z) :=
  match x with
    | Z0 => Z0
    | Zpos p => Zpos (xO p)
    | Zneg p => Zneg (xO p)
  end.

Fixpoint ZPminus (x y:positive) {struct y} : Z :=
  match x, y with
    | xI x', xI y' => Zdouble (ZPminus x' y')
    | xI x', xO y' => Zdouble_plus_one (ZPminus x' y')
    | xI x', xH => Zpos (xO x')
    | xO x', xI y' => Zdouble_minus_one (ZPminus x' y')
    | xO x', xO y' => Zdouble (ZPminus x' y')
    | xO x', xH => Zpos (Pdouble_minus_one x')
    | xH, xI y' => Zneg (xO y')
    | xH, xO y' => Zneg (Pdouble_minus_one y')
    | xH, xH => Z0
  end.

(** ** Addition on integers *)

Definition Zplus (x y:Z) :=
  match x, y with
    | Z0, y => y
    | x, Z0 => x
    | Zpos x', Zpos y' => Zpos (x' + y')
    | Zpos x', Zneg y' =>
      match (x' ?= y')%positive Eq with
	| Eq => Z0
	| Lt => Zneg (y' - x')
	| Gt => Zpos (x' - y')
      end
    | Zneg x', Zpos y' =>
      match (x' ?= y')%positive Eq with
	| Eq => Z0
	| Lt => Zpos (y' - x')
	| Gt => Zneg (x' - y')
      end
    | Zneg x', Zneg y' => Zneg (x' + y')
  end.

Infix "+" := Zplus : Z_scope.

(** ** Opposite *)

Definition Zopp (x:Z) :=
  match x with
    | Z0 => Z0
    | Zpos x => Zneg x
    | Zneg x => Zpos x
  end.

Notation "- x" := (Zopp x) : Z_scope.

(** ** Successor on integers *)

Definition Zsucc (x:Z) := (x + Zpos 1)%Z.

(** ** Predecessor on integers *)

Definition Zpred (x:Z) := (x + Zneg 1)%Z.

(** ** Subtraction on integers *)

Definition Zminus (m n:Z) := (m + - n)%Z.

Infix "-" := Zminus : Z_scope.

(** ** Multiplication on integers *)

Definition Zmult (x y:Z) :=
  match x, y with
    | Z0, _ => Z0
    | _, Z0 => Z0
    | Zpos x', Zpos y' => Zpos (x' * y')
    | Zpos x', Zneg y' => Zneg (x' * y')
    | Zneg x', Zpos y' => Zneg (x' * y')
    | Zneg x', Zneg y' => Zpos (x' * y')
  end.

Infix "*" := Zmult : Z_scope.

(** ** Comparison of integers *)

Definition Zcompare (x y:Z) :=
  match x, y with
    | Z0, Z0 => Eq
    | Z0, Zpos y' => Lt
    | Z0, Zneg y' => Gt
    | Zpos x', Z0 => Gt
    | Zpos x', Zpos y' => (x' ?= y')%positive Eq
    | Zpos x', Zneg y' => Gt
    | Zneg x', Z0 => Lt
    | Zneg x', Zpos y' => Lt
    | Zneg x', Zneg y' => CompOpp ((x' ?= y')%positive Eq)
  end.

Infix "?=" := Zcompare (at level 70, no associativity) : Z_scope.

Ltac elim_compare com1 com2 :=
  case (Dcompare (com1 ?= com2)%Z);
    [ idtac | let x := fresh "H" in
      (intro x; case x; clear x) ].

(** ** Sign function *)

Definition Zsgn (z:Z) : Z :=
  match z with
    | Z0 => Z0
    | Zpos p => Zpos 1
    | Zneg p => Zneg 1
  end.

(** ** Direct, easier to handle variants of successor and addition *)

Definition Zsucc' (x:Z) :=
  match x with
    | Z0 => Zpos 1
    | Zpos x' => Zpos (Psucc x')
    | Zneg x' => ZPminus 1 x'
  end.

Definition Zpred' (x:Z) :=
  match x with
    | Z0 => Zneg 1
    | Zpos x' => ZPminus x' 1
    | Zneg x' => Zneg (Psucc x')
  end.

Definition Zplus' (x y:Z) :=
  match x, y with
    | Z0, y => y
    | x, Z0 => x
    | Zpos x', Zpos y' => Zpos (x' + y')
    | Zpos x', Zneg y' => ZPminus x' y'
    | Zneg x', Zpos y' => ZPminus y' x'
    | Zneg x', Zneg y' => Zneg (x' + y')
  end.

Open Local Scope Z_scope.

(**********************************************************************)
(** ** Inductive specification of Z *)

Theorem Zind :
  forall P:Z -> Prop,
    P Z0 ->
    (forall x:Z, P x -> P (Zsucc' x)) ->
    (forall x:Z, P x -> P (Zpred' x)) -> forall n:Z, P n.
Proof.
  intros P H0 Hs Hp z; destruct z.
  assumption.
  apply Pind with (P := fun p => P (Zpos p)).
    change (P (Zsucc' Z0)) in |- *; apply Hs; apply H0.
    intro n; exact (Hs (Zpos n)).
  apply Pind with (P := fun p => P (Zneg p)).
    change (P (Zpred' Z0)) in |- *; apply Hp; apply H0.
    intro n; exact (Hp (Zneg n)).
Qed.

(**********************************************************************)
(** * Misc properties about binary integer operations *)


(**********************************************************************)
(** ** Properties of opposite on binary integer numbers *)

Theorem Zopp_neg : forall p:positive, - Zneg p = Zpos p.
Proof.
  reflexivity.
Qed.

(** [opp] is involutive *)

Theorem Zopp_involutive : forall n:Z, - - n = n.
Proof.
  intro x; destruct x; reflexivity.
Qed.

(** Injectivity of the opposite *)

Theorem Zopp_inj : forall n m:Z, - n = - m -> n = m.
Proof.
  intros x y; case x; case y; simpl in |- *; intros;
    [ trivial
      | discriminate H
      | discriminate H
      | discriminate H
      | simplify_eq H; intro E; rewrite E; trivial
      | discriminate H
      | discriminate H
      | discriminate H
      | simplify_eq H; intro E; rewrite E; trivial ].
Qed.

(*************************************************************************)
(** **  Properties of the direct definition of successor and predecessor *)

Lemma Zpred'_succ' : forall n:Z, Zpred' (Zsucc' n) = n.
Proof.
  intro x; destruct x; simpl in |- *.
    reflexivity.
  destruct p; simpl in |- *; try rewrite Pdouble_minus_one_o_succ_eq_xI;
    reflexivity.
  destruct p; simpl in |- *; try rewrite Psucc_o_double_minus_one_eq_xO;
    reflexivity.
Qed.

Lemma Zsucc'_discr : forall n:Z, n <> Zsucc' n.
Proof.
  intro x; destruct x; simpl in |- *.
  discriminate.
  injection; apply Psucc_discr.
  destruct p; simpl in |- *.
    discriminate.
    intro H; symmetry  in H; injection H; apply double_moins_un_xO_discr.
    discriminate.
Qed.

(**********************************************************************)
(** ** Other properties of binary integer numbers *)

Lemma ZL0 : 2%nat = (1 + 1)%nat.
Proof.
  reflexivity.
Qed.

(**********************************************************************)
(** * Properties of the addition on integers *)

(** ** zero is left neutral for addition *)

Theorem Zplus_0_l : forall n:Z, Z0 + n = n.
Proof.
  intro x; destruct x; reflexivity.
Qed.

(** *** zero is right neutral for addition *)

Theorem Zplus_0_r : forall n:Z, n + Z0 = n.
Proof.
  intro x; destruct x; reflexivity.
Qed.

(** ** addition is commutative *)

Theorem Zplus_comm : forall n m:Z, n + m = m + n.
Proof.
  intro x; induction x as [| p| p]; intro y; destruct y as [| q| q];
    simpl in |- *; try reflexivity.
  rewrite Pplus_comm; reflexivity.
  rewrite ZC4; destruct ((q ?= p)%positive Eq); reflexivity.
  rewrite ZC4; destruct ((q ?= p)%positive Eq); reflexivity.
  rewrite Pplus_comm; reflexivity.
Qed.

(** ** opposite distributes over addition *)

Theorem Zopp_plus_distr : forall n m:Z, - (n + m) = - n + - m.
Proof.
  intro x; destruct x as [| p| p]; intro y; destruct y as [| q| q];
    simpl in |- *; reflexivity || destruct ((p ?= q)%positive Eq); 
      reflexivity.
Qed.

(** ** opposite is inverse for addition *)

Theorem Zplus_opp_r : forall n:Z, n + - n = Z0.
Proof.
  intro x; destruct x as [| p| p]; simpl in |- *;
    [ reflexivity
      | rewrite (Pcompare_refl p); reflexivity
      | rewrite (Pcompare_refl p); reflexivity ].
Qed.

Theorem Zplus_opp_l : forall n:Z, - n + n = Z0.
Proof.
  intro; rewrite Zplus_comm; apply Zplus_opp_r.
Qed.

Hint Local Resolve Zplus_0_l Zplus_0_r.

(** ** addition is associative *)

Lemma weak_assoc :
  forall (p q:positive) (n:Z), Zpos p + (Zpos q + n) = Zpos p + Zpos q + n.
Proof.
  intros x y z'; case z';
    [ auto with arith
      | intros z; simpl in |- *; rewrite Pplus_assoc; auto with arith
      | intros z; simpl in |- *; ElimPcompare y z; intros E0; rewrite E0;
	ElimPcompare (x + y)%positive z; intros E1; rewrite E1;
	  [ absurd ((x + y ?= z)%positive Eq = Eq);
	    [  (* Case 1 *)
              rewrite nat_of_P_gt_Gt_compare_complement_morphism;
		[ discriminate
		  | rewrite nat_of_P_plus_morphism; rewrite (Pcompare_Eq_eq y z E0);
		    elim (ZL4 x); intros k E2; rewrite E2; 
		      simpl in |- *; unfold gt, lt in |- *; 
			apply le_n_S; apply le_plus_r ]
	      | assumption ]
	    | absurd ((x + y ?= z)%positive Eq = Lt);
	      [  (* Case 2 *)
		rewrite nat_of_P_gt_Gt_compare_complement_morphism;
		  [ discriminate
		    | rewrite nat_of_P_plus_morphism; rewrite (Pcompare_Eq_eq y z E0);
		      elim (ZL4 x); intros k E2; rewrite E2; 
			simpl in |- *; unfold gt, lt in |- *; 
			  apply le_n_S; apply le_plus_r ]
		| assumption ]
	    | rewrite (Pcompare_Eq_eq y z E0);
          (* Case 3 *)
	      elim (Pminus_mask_Gt (x + z) z);
		[ intros t H; elim H; intros H1 H2; elim H2; intros H3 H4;
		  unfold Pminus in |- *; rewrite H1; cut (x = t);
		    [ intros E; rewrite E; auto with arith
		      | apply Pplus_reg_r with (r := z); rewrite <- H3;
			rewrite Pplus_comm; trivial with arith ]
		  | pattern z at 1 in |- *; rewrite <- (Pcompare_Eq_eq y z E0);
		    assumption ]
	    | elim (Pminus_mask_Gt z y);
	      [  (* Case 4 *)
		intros k H; elim H; intros H1 H2; elim H2; intros H3 H4;
		  unfold Pminus at 1 in |- *; rewrite H1; cut (x = k);
		    [ intros E; rewrite E; rewrite (Pcompare_refl k);
		      trivial with arith
		      | apply Pplus_reg_r with (r := y); rewrite (Pplus_comm k y);
			rewrite H3; apply Pcompare_Eq_eq; assumption ]
		| apply ZC2; assumption ]
	    | elim (Pminus_mask_Gt z y);
	      [  (* Case 5 *)
		intros k H; elim H; intros H1 H2; elim H2; intros H3 H4;
		  unfold Pminus at 1 3 5 in |- *; rewrite H1;
		    cut ((x ?= k)%positive Eq = Lt);
		      [ intros E2; rewrite E2; elim (Pminus_mask_Gt k x);
			[ intros i H5; elim H5; intros H6 H7; elim H7; intros H8 H9;
			  elim (Pminus_mask_Gt z (x + y));
			    [ intros j H10; elim H10; intros H11 H12; elim H12;
			      intros H13 H14; unfold Pminus in |- *; 
				rewrite H6; rewrite H11; cut (i = j);
				  [ intros E; rewrite E; auto with arith
				    | apply (Pplus_reg_l (x + y)); rewrite H13;
				      rewrite (Pplus_comm x y); rewrite <- Pplus_assoc;
					rewrite H8; assumption ]
			      | apply ZC2; assumption ]
			  | apply ZC2; assumption ]
			| apply nat_of_P_lt_Lt_compare_complement_morphism;
			  apply plus_lt_reg_l with (p := nat_of_P y);
			    do 2 rewrite <- nat_of_P_plus_morphism;
			      apply nat_of_P_lt_Lt_compare_morphism; 
				rewrite H3; rewrite Pplus_comm; assumption ]
		| apply ZC2; assumption ]
	    | elim (Pminus_mask_Gt z y);
	      [  (* Case 6 *)
		intros k H; elim H; intros H1 H2; elim H2; intros H3 H4;
		  elim (Pminus_mask_Gt (x + y) z);
		    [ intros i H5; elim H5; intros H6 H7; elim H7; intros H8 H9;
		      unfold Pminus in |- *; rewrite H1; rewrite H6;
			cut ((x ?= k)%positive Eq = Gt);
			  [ intros H10; elim (Pminus_mask_Gt x k H10); intros j H11;
			    elim H11; intros H12 H13; elim H13; 
			      intros H14 H15; rewrite H10; rewrite H12; 
				cut (i = j);
				  [ intros H16; rewrite H16; auto with arith
				    | apply (Pplus_reg_l (z + k)); rewrite <- (Pplus_assoc z k j);
				      rewrite H14; rewrite (Pplus_comm z k);
					rewrite <- Pplus_assoc; rewrite H8;
					  rewrite (Pplus_comm x y); rewrite Pplus_assoc;
					    rewrite (Pplus_comm k y); rewrite H3; 
					      trivial with arith ]
			    | apply nat_of_P_gt_Gt_compare_complement_morphism;
			      unfold lt, gt in |- *;
				apply plus_lt_reg_l with (p := nat_of_P y);
				  do 2 rewrite <- nat_of_P_plus_morphism;
				    apply nat_of_P_lt_Lt_compare_morphism; 
				      rewrite H3; rewrite Pplus_comm; apply ZC1; 
					assumption ]
		      | assumption ]
		| apply ZC2; assumption ]
	    | absurd ((x + y ?= z)%positive Eq = Eq);
	      [  (* Case 7 *)
		rewrite nat_of_P_gt_Gt_compare_complement_morphism;
		  [ discriminate
		    | rewrite nat_of_P_plus_morphism; unfold gt in |- *;
		      apply lt_le_trans with (m := nat_of_P y);
			[ apply nat_of_P_lt_Lt_compare_morphism; apply ZC1; assumption
			  | apply le_plus_r ] ]
		| assumption ]
	    | absurd ((x + y ?= z)%positive Eq = Lt);
	      [  (* Case 8 *)
		rewrite nat_of_P_gt_Gt_compare_complement_morphism;
		  [ discriminate
		    | unfold gt in |- *; apply lt_le_trans with (m := nat_of_P y);
		      [ exact (nat_of_P_gt_Gt_compare_morphism y z E0)
			| rewrite nat_of_P_plus_morphism; apply le_plus_r ] ]
		| assumption ]
	    | elim Pminus_mask_Gt with (1 := E0); intros k H1;
          (* Case 9 *)
	      elim Pminus_mask_Gt with (1 := E1); intros i H2; 
		elim H1; intros H3 H4; elim H4; intros H5 H6; 
		  elim H2; intros H7 H8; elim H8; intros H9 H10; 
		    unfold Pminus in |- *; rewrite H3; rewrite H7;
		      cut ((x + k)%positive = i);
			[ intros E; rewrite E; auto with arith
			  | apply (Pplus_reg_l z); rewrite (Pplus_comm x k); rewrite Pplus_assoc;
			    rewrite H5; rewrite H9; rewrite Pplus_comm; 
			      trivial with arith ] ] ].
Qed.

Hint Local Resolve weak_assoc.

Theorem Zplus_assoc : forall n m p:Z, n + (m + p) = n + m + p.
Proof.
  intros x y z; case x; case y; case z; auto with arith; intros;
    [ rewrite (Zplus_comm (Zneg p0)); rewrite weak_assoc;
      rewrite (Zplus_comm (Zpos p1 + Zneg p0)); rewrite weak_assoc;
	rewrite (Zplus_comm (Zpos p1)); trivial with arith
      | apply Zopp_inj; do 4 rewrite Zopp_plus_distr; do 2 rewrite Zopp_neg;
	rewrite Zplus_comm; rewrite <- weak_assoc;
	  rewrite (Zplus_comm (- Zpos p1));
	    rewrite (Zplus_comm (Zpos p0 + - Zpos p1)); rewrite (weak_assoc p);
	      rewrite weak_assoc; rewrite (Zplus_comm (Zpos p0)); 
		trivial with arith
      | rewrite Zplus_comm; rewrite (Zplus_comm (Zpos p0) (Zpos p));
	rewrite <- weak_assoc; rewrite Zplus_comm; rewrite (Zplus_comm (Zpos p0));
	  trivial with arith
      | apply Zopp_inj; do 4 rewrite Zopp_plus_distr; do 2 rewrite Zopp_neg;
	rewrite (Zplus_comm (- Zpos p0)); rewrite weak_assoc;
	  rewrite (Zplus_comm (Zpos p1 + - Zpos p0)); rewrite weak_assoc;
	    rewrite (Zplus_comm (Zpos p)); trivial with arith
      | apply Zopp_inj; do 4 rewrite Zopp_plus_distr; do 2 rewrite Zopp_neg;
	apply weak_assoc
      | apply Zopp_inj; do 4 rewrite Zopp_plus_distr; do 2 rewrite Zopp_neg;
	apply weak_assoc ].
Qed.


Lemma Zplus_assoc_reverse : forall n m p:Z, n + m + p = n + (m + p).
Proof.
  intros; symmetry  in |- *; apply Zplus_assoc.
Qed.

(** ** Associativity mixed with commutativity *)

Theorem Zplus_permute : forall n m p:Z, n + (m + p) = m + (n + p).
Proof.
  intros n m p; rewrite Zplus_comm; rewrite <- Zplus_assoc;
    rewrite (Zplus_comm p n); trivial with arith.
Qed.

(** ** addition simplifies *)

Theorem Zplus_reg_l : forall n m p:Z, n + m = n + p -> m = p.
  intros n m p H; cut (- n + (n + m) = - n + (n + p));
    [ do 2 rewrite Zplus_assoc; rewrite (Zplus_comm (- n) n);
      rewrite Zplus_opp_r; simpl in |- *; trivial with arith
      | rewrite H; trivial with arith ].
Qed.

(** ** addition and successor permutes *)

Lemma Zplus_succ_l : forall n m:Z, Zsucc n + m = Zsucc (n + m).
Proof.
  intros x y; unfold Zsucc in |- *; rewrite (Zplus_comm (x + y));
    rewrite Zplus_assoc; rewrite (Zplus_comm (Zpos 1)); 
      trivial with arith.
Qed.

Lemma Zplus_succ_r : forall n m:Z, Zsucc (n + m) = n + Zsucc m.
Proof.
  intros n m; unfold Zsucc in |- *; rewrite Zplus_assoc; trivial with arith.
Qed.

Lemma Zplus_succ_comm : forall n m:Z, Zsucc n + m = n + Zsucc m.
Proof.
  unfold Zsucc in |- *; intros n m; rewrite <- Zplus_assoc;
    rewrite (Zplus_comm (Zpos 1)); trivial with arith.
Qed.

(** ** Misc properties, usually redundant or non natural *)

Lemma Zplus_0_r_reverse : forall n:Z, n = n + Z0.
Proof.
  symmetry  in |- *; apply Zplus_0_r.
Qed.

Lemma Zplus_0_simpl_l : forall n m:Z, n + Z0 = m -> n = m.
Proof.
  intros n m; rewrite Zplus_0_r; intro; assumption.
Qed.

Lemma Zplus_0_simpl_l_reverse : forall n m:Z, n = m + Z0 -> n = m.
Proof.
  intros n m; rewrite Zplus_0_r; intro; assumption.
Qed.

Lemma Zplus_eq_compat : forall n m p q:Z, n = m -> p = q -> n + p = m + q.
Proof.
  intros; rewrite H; rewrite H0; reflexivity.
Qed.

Lemma Zplus_opp_expand : forall n m p:Z, n + - m = n + - p + (p + - m).
Proof.
  intros x y z.
  rewrite <- (Zplus_assoc x).
  rewrite (Zplus_assoc (- z)).
  rewrite Zplus_opp_l.
  reflexivity.
Qed.

(************************************************************************)
(** * Properties of successor and predecessor on binary integer numbers *)

Theorem Zsucc_discr : forall n:Z, n <> Zsucc n.
Proof.
  intros n; cut (Z0 <> Zpos 1);
    [ unfold not in |- *; intros H1 H2; apply H1; apply (Zplus_reg_l n);
      rewrite Zplus_0_r; exact H2
      | discriminate ].
Qed.

Theorem Zpos_succ_morphism :
  forall p:positive, Zpos (Psucc p) = Zsucc (Zpos p).
Proof.
  intro; rewrite Pplus_one_succ_r; unfold Zsucc in |- *; simpl in |- *;
    trivial with arith.
Qed.

(** successor and predecessor are inverse functions *)

Theorem Zsucc_pred : forall n:Z, n = Zsucc (Zpred n).
Proof.
  intros n; unfold Zsucc, Zpred in |- *; rewrite <- Zplus_assoc; simpl in |- *;
    rewrite Zplus_0_r; trivial with arith.
Qed. 

Hint Immediate Zsucc_pred: zarith.
 
Theorem Zpred_succ : forall n:Z, n = Zpred (Zsucc n).
Proof.
  intros m; unfold Zpred, Zsucc in |- *; rewrite <- Zplus_assoc; simpl in |- *;
    rewrite Zplus_comm; auto with arith.
Qed.

Theorem Zsucc_inj : forall n m:Z, Zsucc n = Zsucc m -> n = m.
Proof.
  intros n m H.
  change (Zneg 1 + Zpos 1 + n = Zneg 1 + Zpos 1 + m) in |- *;
    do 2 rewrite <- Zplus_assoc; do 2 rewrite (Zplus_comm (Zpos 1));
      unfold Zsucc in H; rewrite H; trivial with arith.
Qed.
 
(** Misc properties, usually redundant or non natural *)

Lemma Zsucc_eq_compat : forall n m:Z, n = m -> Zsucc n = Zsucc m.
Proof.
  intros n m H; rewrite H; reflexivity.
Qed.

Lemma Zsucc_inj_contrapositive : forall n m:Z, n <> m -> Zsucc n <> Zsucc m.
Proof.
  unfold not in |- *; intros n m H1 H2; apply H1; apply Zsucc_inj; assumption.
Qed.

(**********************************************************************)
(** * Properties of subtraction on binary integer numbers *)

(** ** [minus] and [Z0] *)

Lemma Zminus_0_r : forall n:Z, n - Z0 = n.
Proof.
  intro; unfold Zminus in |- *; simpl in |- *; rewrite Zplus_0_r;
    trivial with arith.
Qed.

Lemma Zminus_0_l_reverse : forall n:Z, n = n - Z0.
Proof.
  intro; symmetry  in |- *; apply Zminus_0_r.
Qed.

Lemma Zminus_diag : forall n:Z, n - n = Z0.
Proof.
  intro; unfold Zminus in |- *; rewrite Zplus_opp_r; trivial with arith.
Qed.

Lemma Zminus_diag_reverse : forall n:Z, Z0 = n - n.
Proof.
  intro; symmetry  in |- *; apply Zminus_diag.
Qed.


(** ** Relating [minus] with [plus] and [Zsucc] *)

Lemma Zplus_minus_eq : forall n m p:Z, n = m + p -> p = n - m.
Proof.
  intros n m p H; unfold Zminus in |- *; apply (Zplus_reg_l m);
    rewrite (Zplus_comm m (n + - m)); rewrite <- Zplus_assoc;
      rewrite Zplus_opp_l; rewrite Zplus_0_r; rewrite H; 
	trivial with arith.
Qed.

Lemma Zminus_plus : forall n m:Z, n + m - n = m.
Proof.
  intros n m; unfold Zminus in |- *; rewrite (Zplus_comm n m);
    rewrite <- Zplus_assoc; rewrite Zplus_opp_r; apply Zplus_0_r.
Qed.

Lemma Zplus_minus : forall n m:Z, n + (m - n) = m.
Proof.
  unfold Zminus in |- *; intros n m; rewrite Zplus_permute; rewrite Zplus_opp_r;
    apply Zplus_0_r.
Qed.

Lemma Zminus_succ_l : forall n m:Z, Zsucc (n - m) = Zsucc n - m.
Proof.
  intros n m; unfold Zminus, Zsucc in |- *; rewrite (Zplus_comm n (- m));
    rewrite <- Zplus_assoc; apply Zplus_comm.
Qed.

Lemma Zminus_plus_simpl_l : forall n m p:Z, p + n - (p + m) = n - m.
Proof.
  intros n m p; unfold Zminus in |- *; rewrite Zopp_plus_distr;
    rewrite Zplus_assoc; rewrite (Zplus_comm p); rewrite <- (Zplus_assoc n p);
      rewrite Zplus_opp_r; rewrite Zplus_0_r; trivial with arith.
Qed.

Lemma Zminus_plus_simpl_l_reverse : forall n m p:Z, n - m = p + n - (p + m).
Proof.
  intros; symmetry  in |- *; apply Zminus_plus_simpl_l.
Qed.

Lemma Zminus_plus_simpl_r : forall n m p:Z, n + p - (m + p) = n - m.
Proof.
  intros x y n.
  unfold Zminus in |- *.
  rewrite Zopp_plus_distr.
  rewrite (Zplus_comm (- y) (- n)).
  rewrite Zplus_assoc.
  rewrite <- (Zplus_assoc x n (- n)).
  rewrite (Zplus_opp_r n).
  rewrite <- Zplus_0_r_reverse.
  reflexivity.
Qed.

(** ** Misc redundant properties *)

Lemma Zeq_minus : forall n m:Z, n = m -> n - m = Z0.
Proof.
  intros x y H; rewrite H; symmetry  in |- *; apply Zminus_diag_reverse.
Qed.

Lemma Zminus_eq : forall n m:Z, n - m = Z0 -> n = m.
Proof.
  intros x y H; rewrite <- (Zplus_minus y x); rewrite H; apply Zplus_0_r.
Qed.


(**********************************************************************)
(** * Properties of multiplication on binary integer numbers *)

Theorem Zpos_mult_morphism : 
  forall p q:positive, Zpos (p*q) = Zpos p * Zpos q.
Proof.
  auto.
Qed.

(** ** One is neutral for multiplication *)

Theorem Zmult_1_l : forall n:Z, Zpos 1 * n = n.
Proof.
  intro x; destruct x; reflexivity.
Qed.

Theorem Zmult_1_r : forall n:Z, n * Zpos 1 = n.
Proof.
  intro x; destruct x; simpl in |- *; try rewrite Pmult_1_r; reflexivity.
Qed.

(** ** Zero property of multiplication *)

Theorem Zmult_0_l : forall n:Z, Z0 * n = Z0.
Proof.
  intro x; destruct x; reflexivity.
Qed.

Theorem Zmult_0_r : forall n:Z, n * Z0 = Z0.
Proof.
  intro x; destruct x; reflexivity.
Qed.

Hint Local Resolve Zmult_0_l Zmult_0_r.

Lemma Zmult_0_r_reverse : forall n:Z, Z0 = n * Z0.
Proof.
  intro x; destruct x; reflexivity.
Qed.

(** ** Commutativity of multiplication *)

Theorem Zmult_comm : forall n m:Z, n * m = m * n.
Proof.
  intros x y; destruct x as [| p| p]; destruct y as [| q| q]; simpl in |- *;
    try rewrite (Pmult_comm p q); reflexivity.
Qed.

(** ** Associativity of multiplication *)

Theorem Zmult_assoc : forall n m p:Z, n * (m * p) = n * m * p.
Proof.
  intros x y z; destruct x; destruct y; destruct z; simpl in |- *;
    try rewrite Pmult_assoc; reflexivity.
Qed.

Lemma Zmult_assoc_reverse : forall n m p:Z, n * m * p = n * (m * p).
Proof.
  intros n m p; rewrite Zmult_assoc; trivial with arith.
Qed.

(** ** Associativity mixed with commutativity *)

Theorem Zmult_permute : forall n m p:Z, n * (m * p) = m * (n * p).
Proof.
  intros x y z; rewrite (Zmult_assoc y x z); rewrite (Zmult_comm y x).
  apply Zmult_assoc.
Qed.

(** ** Z is integral *)

Theorem Zmult_integral_l : forall n m:Z, n <> Z0 -> m * n = Z0 -> m = Z0.
Proof.
  intros x y; destruct x as [| p| p].
  intro H; absurd (Z0 = Z0); trivial.
  intros _ H; destruct y as [| q| q]; reflexivity || discriminate.
  intros _ H; destruct y as [| q| q]; reflexivity || discriminate.
Qed.


Theorem Zmult_integral : forall n m:Z, n * m = Z0 -> n = Z0 \/ m = Z0.
Proof.
  intros x y; destruct x; destruct y; auto; simpl in |- *; intro H;
    discriminate H.
Qed.


Lemma Zmult_1_inversion_l :
  forall n m:Z, n * m = Zpos 1 -> n = Zpos 1 \/ n = Zneg 1.
Proof.
  intros x y; destruct x as [| p| p]; intro; [ discriminate | left | right ];
    (destruct y as [| q| q]; try discriminate; simpl in H; injection H; clear H;
      intro H; rewrite Pmult_1_inversion_l with (1 := H); 
	reflexivity).
Qed.

(** ** Multiplication and Opposite *)

Theorem Zopp_mult_distr_l : forall n m:Z, - (n * m) = - n * m.
Proof.
  intros x y; destruct x; destruct y; reflexivity.
Qed.

Theorem Zopp_mult_distr_r : forall n m:Z, - (n * m) = n * - m.
Proof.
  intros x y; rewrite (Zmult_comm x y); rewrite Zopp_mult_distr_l;
    apply Zmult_comm.
Qed.

Lemma Zopp_mult_distr_l_reverse : forall n m:Z, - n * m = - (n * m).
Proof.
  intros x y; symmetry  in |- *; apply Zopp_mult_distr_l.
Qed.

Theorem Zmult_opp_comm : forall n m:Z, - n * m = n * - m.
Proof.
  intros x y; rewrite Zopp_mult_distr_l_reverse; rewrite Zopp_mult_distr_r;
    trivial with arith.
Qed.

Theorem Zmult_opp_opp : forall n m:Z, - n * - m = n * m.
Proof.
  intros x y; destruct x; destruct y; reflexivity.
Qed.

Theorem Zopp_eq_mult_neg_1 : forall n:Z, - n = n * Zneg 1.
Proof.
  intro x; induction x; intros; rewrite Zmult_comm; auto with arith.
Qed.

(** ** Distributivity of multiplication over addition *)

Lemma weak_Zmult_plus_distr_r :
  forall (p:positive) (n m:Z), Zpos p * (n + m) = Zpos p * n + Zpos p * m.
Proof.
  intros x y' z'; case y'; case z'; auto with arith; intros y z;
    (simpl in |- *; rewrite Pmult_plus_distr_l; trivial with arith) ||
      (simpl in |- *; ElimPcompare z y; intros E0; rewrite E0;
	[ rewrite (Pcompare_Eq_eq z y E0); rewrite (Pcompare_refl (x * y));
          trivial with arith
	  | cut ((x * z ?= x * y)%positive Eq = Lt);
            [ intros E; rewrite E; rewrite Pmult_minus_distr_l;
              [ trivial with arith | apply ZC2; assumption ]
              | apply nat_of_P_lt_Lt_compare_complement_morphism;
		do 2 rewrite nat_of_P_mult_morphism; elim (ZL4 x); 
		  intros h H1; rewrite H1; apply mult_S_lt_compat_l;
		    exact (nat_of_P_lt_Lt_compare_morphism z y E0) ]
	  | cut ((x * z ?= x * y)%positive Eq = Gt);
            [ intros E; rewrite E; rewrite Pmult_minus_distr_l; auto with arith
              | apply nat_of_P_gt_Gt_compare_complement_morphism; unfold gt in |- *;
		do 2 rewrite nat_of_P_mult_morphism; elim (ZL4 x); 
		  intros h H1; rewrite H1; apply mult_S_lt_compat_l;
		    exact (nat_of_P_gt_Gt_compare_morphism z y E0) ] ]).
Qed.

Theorem Zmult_plus_distr_r : forall n m p:Z, n * (m + p) = n * m + n * p.
Proof.
  intros x y z; case x;
    [ auto with arith
      | intros x'; apply weak_Zmult_plus_distr_r
      | intros p; apply Zopp_inj; rewrite Zopp_plus_distr;
	do 3 rewrite <- Zopp_mult_distr_l_reverse; rewrite Zopp_neg;
	  apply weak_Zmult_plus_distr_r ].
Qed.

Theorem Zmult_plus_distr_l : forall n m p:Z, (n + m) * p = n * p + m * p.
Proof.
  intros n m p; rewrite Zmult_comm; rewrite Zmult_plus_distr_r;
    do 2 rewrite (Zmult_comm p); trivial with arith.
Qed.

(** ** Distributivity of multiplication over subtraction *)

Lemma Zmult_minus_distr_r : forall n m p:Z, (n - m) * p = n * p - m * p.
Proof.
  intros x y z; unfold Zminus in |- *.
  rewrite <- Zopp_mult_distr_l_reverse.
  apply Zmult_plus_distr_l.
Qed.

 
Lemma Zmult_minus_distr_l : forall n m p:Z, p * (n - m) = p * n - p * m.
Proof.
  intros x y z; rewrite (Zmult_comm z (x - y)).
  rewrite (Zmult_comm z x).
  rewrite (Zmult_comm z y).
  apply Zmult_minus_distr_r.
Qed.

(** ** Simplification of multiplication for non-zero integers *)

Lemma Zmult_reg_l : forall n m p:Z, p <> Z0 -> p * n = p * m -> n = m.
Proof.
  intros x y z H H0.
  generalize (Zeq_minus _ _ H0).
  intro.
  apply Zminus_eq.
  rewrite <- Zmult_minus_distr_l in H1.
  clear H0; destruct (Zmult_integral _ _ H1).
  contradiction.
  trivial.
Qed.

Lemma Zmult_reg_r : forall n m p:Z, p <> Z0 -> n * p = m * p -> n = m.
Proof.
  intros x y z Hz.
  rewrite (Zmult_comm x z).
  rewrite (Zmult_comm y z).
  intro; apply Zmult_reg_l with z; assumption.
Qed.

(** ** Addition and multiplication by 2 *)

Lemma Zplus_diag_eq_mult_2 : forall n:Z, n + n = n * Zpos 2.
Proof.
  intros x; pattern x at 1 2 in |- *; rewrite <- (Zmult_1_r x);
    rewrite <- Zmult_plus_distr_r; reflexivity.
Qed.

(** ** Multiplication and successor *)

Lemma Zmult_succ_r : forall n m:Z, n * Zsucc m = n * m + n.
Proof.
  intros n m; unfold Zsucc in |- *; rewrite Zmult_plus_distr_r;
    rewrite (Zmult_comm n (Zpos 1)); rewrite Zmult_1_l; 
      trivial with arith.
Qed.

Lemma Zmult_succ_r_reverse : forall n m:Z, n * m + n = n * Zsucc m.
Proof.
  intros; symmetry  in |- *; apply Zmult_succ_r.
Qed.

Lemma Zmult_succ_l : forall n m:Z, Zsucc n * m = n * m + m.
Proof.
  intros n m; unfold Zsucc in |- *; rewrite Zmult_plus_distr_l;
    rewrite Zmult_1_l; trivial with arith.
Qed.

Lemma Zmult_succ_l_reverse : forall n m:Z, n * m + m = Zsucc n * m.
Proof.
  intros; symmetry  in |- *; apply Zmult_succ_l.
Qed.



(** ** Misc redundant properties *)

Lemma Z_eq_mult : forall n m:Z, m = Z0 -> m * n = Z0.
Proof.
  intros x y H; rewrite H; auto with arith.
Qed.



(**********************************************************************)
(** * Relating binary positive numbers and binary integers *)

Lemma Zpos_eq : forall p q, p = q -> Zpos p = Zpos q.
Proof.
  intros; f_equal; auto.
Qed.

Lemma Zpos_eq_rev : forall p q, Zpos p = Zpos q -> p = q.
Proof.
  inversion 1; auto.
Qed.

Lemma Zpos_eq_iff : forall p q, p = q <-> Zpos p = Zpos q.
Proof.
  split; [apply Zpos_eq|apply Zpos_eq_rev].
Qed.

Lemma Zpos_xI : forall p:positive, Zpos (xI p) = Zpos 2 * Zpos p + Zpos 1.
Proof.
  intro; apply refl_equal.
Qed.

Lemma Zpos_xO : forall p:positive, Zpos (xO p) = Zpos 2 * Zpos p.
Proof.
  intro; apply refl_equal.
Qed.

Lemma Zneg_xI : forall p:positive, Zneg (xI p) = Zpos 2 * Zneg p - Zpos 1.
Proof.
  intro; apply refl_equal.
Qed.

Lemma Zneg_xO : forall p:positive, Zneg (xO p) = Zpos 2 * Zneg p.
Proof.
  reflexivity.
Qed.

Lemma Zpos_plus_distr : forall p q:positive, Zpos (p + q) = Zpos p + Zpos q.
Proof.
  intros p p'; destruct p;
    [ destruct p' as [p0| p0| ]
      | destruct p' as [p0| p0| ]
      | destruct p' as [p| p| ] ]; reflexivity.
Qed.

Lemma Zneg_plus_distr : forall p q:positive, Zneg (p + q) = Zneg p + Zneg q.
Proof.
  intros p p'; destruct p;
    [ destruct p' as [p0| p0| ]
      | destruct p' as [p0| p0| ]
      | destruct p' as [p| p| ] ]; reflexivity.
Qed.

(**********************************************************************)
(** * Order relations *)

Definition Zlt (x y:Z) := (x ?= y) = Lt.
Definition Zgt (x y:Z) := (x ?= y) = Gt.
Definition Zle (x y:Z) := (x ?= y) <> Gt.
Definition Zge (x y:Z) := (x ?= y) <> Lt.
Definition Zne (x y:Z) := x <> y.

Infix "<=" := Zle : Z_scope.
Infix "<" := Zlt : Z_scope.
Infix ">=" := Zge : Z_scope.
Infix ">" := Zgt : Z_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : Z_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : Z_scope.
Notation "x < y < z" := (x < y /\ y < z) : Z_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : Z_scope.

(**********************************************************************)
(** * Absolute value on integers *)

Definition Zabs_nat (x:Z) : nat :=
  match x with
    | Z0 => 0%nat
    | Zpos p => nat_of_P p
    | Zneg p => nat_of_P p
  end.

Definition Zabs (z:Z) : Z :=
  match z with
    | Z0 => Z0
    | Zpos p => Zpos p
    | Zneg p => Zpos p
  end.

(**********************************************************************)
(** * From [nat] to [Z] *)

Definition Z_of_nat (x:nat) :=
  match x with
    | O => Z0
    | S y => Zpos (P_of_succ_nat y)
  end.

Require Import BinNat.

Definition Zabs_N (z:Z) :=
  match z with
    | Z0 => 0%N
    | Zpos p => Npos p
    | Zneg p => Npos p
  end.

Definition Z_of_N (x:N) := match x with
                             | N0 => Z0
                             | Npos p => Zpos p
                           end.

