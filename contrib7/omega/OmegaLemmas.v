(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require ZArith_base.

(** These are specific variants of theorems dedicated for the Omega tactic *)

Lemma new_var: (x:Z) (EX y:Z |(x=y)).
Intros x; Exists x; Trivial with arith. 
Qed.

Lemma OMEGA1 : (x,y:Z) (x=y) -> (Zle ZERO x) -> (Zle ZERO y).
Intros x y H; Rewrite H; Auto with arith.
Qed.

Lemma OMEGA2 : (x,y:Z) (Zle ZERO x) -> (Zle ZERO y) -> (Zle ZERO (Zplus x y)).
Exact Zle_0_plus.
Qed. 

Lemma OMEGA3 : 
  (x,y,k:Z)(Zgt k ZERO)-> (x=(Zmult y k)) -> (x=ZERO) -> (y=ZERO).

Intros x y k H1 H2 H3; Apply (Zmult_eq k); [
  Unfold not ; Intros H4; Absurd (Zgt k ZERO); [
    Rewrite H4; Unfold Zgt ; Simpl; Discriminate | Assumption]
  | Rewrite <- H2; Assumption].
Qed.

Lemma OMEGA4 :
  (x,y,z:Z)(Zgt x ZERO) -> (Zgt y x) -> ~(Zplus (Zmult z y) x) = ZERO.

Unfold not ; Intros x y z H1 H2 H3; Cut (Zgt y ZERO); [
  Intros H4; Cut (Zle ZERO (Zplus (Zmult z y) x)); [
    Intros H5; Generalize (Zmult_le_approx y z x H4 H2 H5) ; Intros H6;
    Absurd (Zgt (Zplus (Zmult z y) x) ZERO); [
      Rewrite -> H3; Unfold Zgt ; Simpl; Discriminate
    | Apply Zle_gt_trans with x ; [
        Pattern 1 x ; Rewrite <- (Zero_left x); Apply Zle_reg_r;
        Rewrite -> Zmult_sym; Generalize H4 ; Unfold Zgt;
        Case y; [
          Simpl; Intros H7; Discriminate H7
        | Intros p H7; Rewrite <- (Zero_mult_right (POS p));
          Unfold Zle ; Rewrite -> Zcompare_Zmult_compatible; Exact H6
        | Simpl; Intros p H7; Discriminate H7]
      | Assumption]]
    | Rewrite -> H3; Unfold Zle ; Simpl; Discriminate]
  | Apply Zgt_trans with x ; [ Assumption | Assumption]].
Qed.

Lemma OMEGA5: (x,y,z:Z)(x=ZERO) -> (y=ZERO) -> (Zplus x (Zmult y z)) = ZERO.

Intros x y z H1 H2; Rewrite H1; Rewrite H2; Simpl; Trivial with arith.
Qed.

Lemma OMEGA6:
  (x,y,z:Z)(Zle ZERO x) -> (y=ZERO) -> (Zle ZERO (Zplus x (Zmult y z))).

Intros x y z H1 H2; Rewrite H2; Simpl; Rewrite Zero_right; Assumption.
Qed.

Lemma OMEGA7:
  (x,y,z,t:Z)(Zgt z ZERO) -> (Zgt t ZERO) -> (Zle ZERO x) -> (Zle ZERO y) -> 
    (Zle ZERO (Zplus (Zmult x z) (Zmult y t))).

Intros x y z t H1 H2 H3 H4; Rewrite <- (Zero_left ZERO);
Apply Zle_plus_plus; Apply Zle_mult; Assumption.
Qed.

Lemma OMEGA8: 
  (x,y:Z) (Zle ZERO x) -> (Zle ZERO y) -> x = (Zopp y) -> x = ZERO.

Intros x y H1 H2 H3; Elim (Zle_lt_or_eq ZERO x H1); [
  Intros H4; Absurd (Zlt ZERO x); [
    Change (Zge ZERO x); Apply Zle_ge; Apply Zsimpl_le_plus_l with y;
    Rewrite -> H3; Rewrite Zplus_inverse_r; Rewrite Zero_right; Assumption
  | Assumption]
| Intros H4; Rewrite -> H4; Trivial with arith].
Qed.

Lemma OMEGA9:(x,y,z,t:Z) y=ZERO -> x = z -> 
  (Zplus y (Zmult (Zplus (Zopp x) z) t)) = ZERO.

Intros x y z t H1 H2; Rewrite H2; Rewrite Zplus_inverse_l; 
Rewrite Zero_mult_left;  Rewrite Zero_right; Assumption.
Qed.

Lemma OMEGA10:(v,c1,c2,l1,l2,k1,k2:Z)
  (Zplus (Zmult (Zplus (Zmult v c1) l1) k1) (Zmult (Zplus (Zmult v c2) l2) k2))
  = (Zplus (Zmult v (Zplus (Zmult c1 k1) (Zmult c2 k2)))
           (Zplus (Zmult l1 k1) (Zmult l2 k2))).

Intros; Repeat (Rewrite Zmult_plus_distr_l Orelse Rewrite Zmult_plus_distr_r);
Repeat Rewrite Zmult_assoc; Repeat Elim Zplus_assoc; 
Rewrite (Zplus_permute (Zmult l1 k1) (Zmult (Zmult v c2) k2)); Trivial with arith.
Qed.

Lemma OMEGA11:(v1,c1,l1,l2,k1:Z)
  (Zplus (Zmult (Zplus (Zmult v1 c1) l1) k1) l2)
  = (Zplus (Zmult v1 (Zmult c1 k1)) (Zplus (Zmult l1 k1) l2)).

Intros; Repeat (Rewrite Zmult_plus_distr_l Orelse Rewrite Zmult_plus_distr_r);
Repeat Rewrite Zmult_assoc; Repeat Elim Zplus_assoc; Trivial with arith.
Qed.

Lemma OMEGA12:(v2,c2,l1,l2,k2:Z)
  (Zplus l1 (Zmult (Zplus (Zmult v2 c2) l2) k2))
  = (Zplus (Zmult v2 (Zmult c2 k2)) (Zplus l1 (Zmult l2 k2))).

Intros; Repeat (Rewrite Zmult_plus_distr_l Orelse Rewrite Zmult_plus_distr_r);
Repeat Rewrite Zmult_assoc; Repeat Elim Zplus_assoc; Rewrite Zplus_permute;
Trivial with arith.
Qed.

Lemma OMEGA13:(v,l1,l2:Z)(x:positive)
  (Zplus (Zplus (Zmult v (POS x)) l1) (Zplus (Zmult v (NEG x)) l2))
  = (Zplus l1 l2).

Intros; Rewrite  Zplus_assoc; Rewrite (Zplus_sym (Zmult v (POS x)) l1);
Rewrite (Zplus_assoc_r l1); Rewrite <- Zmult_plus_distr_r;
Rewrite <- Zopp_NEG; Rewrite (Zplus_sym (Zopp (NEG x)) (NEG x));
Rewrite Zplus_inverse_r; Rewrite  Zero_mult_right; Rewrite Zero_right; Trivial with arith.
Qed.
 
Lemma OMEGA14:(v,l1,l2:Z)(x:positive)
  (Zplus (Zplus (Zmult v (NEG x)) l1) (Zplus (Zmult v (POS x)) l2))
  = (Zplus l1 l2).

Intros; Rewrite  Zplus_assoc; Rewrite (Zplus_sym (Zmult v (NEG x)) l1);
Rewrite (Zplus_assoc_r l1); Rewrite <- Zmult_plus_distr_r;
Rewrite <- Zopp_NEG; Rewrite  Zplus_inverse_r; Rewrite  Zero_mult_right;
Rewrite Zero_right; Trivial with arith.
Qed.
Lemma OMEGA15:(v,c1,c2,l1,l2,k2:Z)
  (Zplus (Zplus (Zmult v c1) l1) (Zmult (Zplus (Zmult v c2) l2) k2))
  = (Zplus (Zmult v (Zplus c1  (Zmult c2 k2)))
           (Zplus l1 (Zmult l2 k2))).

Intros; Repeat (Rewrite Zmult_plus_distr_l Orelse Rewrite Zmult_plus_distr_r);
Repeat Rewrite Zmult_assoc; Repeat Elim Zplus_assoc; 
Rewrite (Zplus_permute l1 (Zmult (Zmult v c2) k2)); Trivial with arith.
Qed.

Lemma OMEGA16:
  (v,c,l,k:Z)
   (Zmult (Zplus (Zmult v c) l) k) = (Zplus (Zmult v (Zmult c k)) (Zmult l k)).

Intros; Repeat (Rewrite Zmult_plus_distr_l Orelse Rewrite Zmult_plus_distr_r);
Repeat Rewrite Zmult_assoc; Repeat Elim Zplus_assoc; Trivial with arith.
Qed.

Lemma OMEGA17: 
  (x,y,z:Z)(Zne x ZERO) -> (y=ZERO) -> (Zne (Zplus x (Zmult y z)) ZERO).

Unfold Zne not; Intros x y z H1 H2 H3; Apply H1; 
Apply Zsimpl_plus_l with (Zmult y z); Rewrite Zplus_sym; Rewrite H3; 
Rewrite H2; Auto with arith.
Qed.

Lemma OMEGA18:
  (x,y,k:Z) x=(Zmult y k) -> (Zne x ZERO) -> (Zne y ZERO).

Unfold Zne not; Intros x y k H1 H2 H3; Apply H2; Rewrite H1; Rewrite H3; Auto with arith.
Qed.

Lemma OMEGA19:
  (x:Z) (Zne x ZERO) -> 
    (Zle ZERO (Zplus x (NEG xH))) \/ (Zle ZERO (Zplus (Zmult x (NEG xH)) (NEG xH))).

Unfold Zne ; Intros x H; Elim (Zle_or_lt ZERO x); [
  Intros H1; Elim Zle_lt_or_eq with 1:=H1; [
    Intros H2; Left;  Change (Zle ZERO (Zpred x)); Apply Zle_S_n;
    Rewrite <- Zs_pred; Apply Zlt_le_S; Assumption
  | Intros H2; Absurd x=ZERO; Auto with arith]
| Intros H1; Right; Rewrite <- Zopp_one; Rewrite Zplus_sym;
  Apply Zle_left; Apply Zle_S_n; Simpl; Apply Zlt_le_S; Auto with arith].
Qed.

Lemma OMEGA20:
  (x,y,z:Z)(Zne x  ZERO) -> (y=ZERO) -> (Zne (Zplus x (Zmult y z)) ZERO).

Unfold Zne not; Intros x y z H1 H2 H3; Apply H1; Rewrite H2 in H3;
Simpl in H3; Rewrite Zero_right in H3; Trivial with arith.
Qed.

Definition fast_Zplus_sym := 
[x,y:Z][P:Z -> Prop][H: (P (Zplus y x))]
  (eq_ind_r Z (Zplus y x) P H (Zplus x y) (Zplus_sym x y)).

Definition fast_Zplus_assoc_r :=
[n,m,p:Z][P:Z -> Prop][H : (P (Zplus n (Zplus m p)))]
 (eq_ind_r Z (Zplus n (Zplus m p)) P H (Zplus (Zplus n m) p) (Zplus_assoc_r n m p)).

Definition fast_Zplus_assoc_l :=
[n,m,p:Z][P:Z -> Prop][H : (P (Zplus (Zplus n m) p))]
 (eq_ind_r Z (Zplus (Zplus n m) p) P H (Zplus n (Zplus m p)) 
           (Zplus_assoc_l n m p)).

Definition fast_Zplus_permute :=
[n,m,p:Z][P:Z -> Prop][H : (P (Zplus m (Zplus n p)))]
 (eq_ind_r Z (Zplus m (Zplus n p)) P H (Zplus n (Zplus m p))
           (Zplus_permute n m p)).

Definition fast_OMEGA10 := 
[v,c1,c2,l1,l2,k1,k2:Z][P:Z -> Prop]
[H : (P (Zplus (Zmult v (Zplus (Zmult c1 k1) (Zmult c2 k2)))
               (Zplus (Zmult l1 k1) (Zmult l2 k2))))]
 (eq_ind_r Z 
           (Zplus (Zmult v (Zplus (Zmult c1 k1) (Zmult c2 k2)))
            (Zplus (Zmult l1 k1) (Zmult l2 k2)))
           P H 
          (Zplus (Zmult (Zplus (Zmult v c1) l1) k1)
                 (Zmult (Zplus (Zmult v c2) l2) k2))
        (OMEGA10 v c1 c2 l1 l2 k1 k2)).

Definition fast_OMEGA11 := 
[v1,c1,l1,l2,k1:Z][P:Z -> Prop]
[H : (P (Zplus (Zmult v1 (Zmult c1 k1)) (Zplus (Zmult l1 k1) l2)))]
 (eq_ind_r Z 
   (Zplus (Zmult v1 (Zmult c1 k1)) (Zplus (Zmult l1 k1) l2))
   P H 
   (Zplus (Zmult (Zplus (Zmult v1 c1) l1) k1) l2)
   (OMEGA11 v1 c1 l1 l2 k1)).
Definition fast_OMEGA12 := 
[v2,c2,l1,l2,k2:Z][P:Z -> Prop]
[H : (P (Zplus (Zmult v2 (Zmult c2 k2)) (Zplus l1 (Zmult l2 k2))))]
 (eq_ind_r Z 
   (Zplus (Zmult v2 (Zmult c2 k2)) (Zplus l1 (Zmult l2 k2)))
   P H 
   (Zplus l1 (Zmult (Zplus (Zmult v2 c2) l2) k2))
   (OMEGA12 v2 c2 l1 l2 k2)).

Definition fast_OMEGA15 :=
[v,c1,c2,l1,l2,k2 :Z][P:Z -> Prop]
[H : (P (Zplus (Zmult v (Zplus c1 (Zmult c2 k2))) (Zplus l1 (Zmult l2 k2))))]
 (eq_ind_r Z 
   (Zplus (Zmult v (Zplus c1 (Zmult c2 k2))) (Zplus l1 (Zmult l2 k2)))
   P H 
   (Zplus (Zplus (Zmult v c1) l1) (Zmult (Zplus (Zmult v c2) l2) k2))
   (OMEGA15 v c1 c2 l1 l2 k2)).
Definition fast_OMEGA16 :=
[v,c,l,k :Z][P:Z -> Prop]
[H : (P (Zplus (Zmult v (Zmult c k)) (Zmult l k)))]
 (eq_ind_r Z 
   (Zplus (Zmult v (Zmult c k)) (Zmult l k))
   P H 
   (Zmult (Zplus (Zmult v c) l) k)
   (OMEGA16 v c l k)).

Definition fast_OMEGA13 :=
[v,l1,l2 :Z][x:positive][P:Z -> Prop]
[H : (P (Zplus l1 l2))]
 (eq_ind_r Z 
   (Zplus l1 l2)
   P H 
   (Zplus (Zplus (Zmult v (POS x)) l1) (Zplus (Zmult v (NEG x)) l2))
   (OMEGA13 v l1 l2 x )).

Definition fast_OMEGA14 :=
[v,l1,l2 :Z][x:positive][P:Z -> Prop]
[H : (P (Zplus l1 l2))]
 (eq_ind_r Z 
   (Zplus l1 l2)
   P H 
   (Zplus (Zplus (Zmult v (NEG x)) l1) (Zplus (Zmult v (POS x)) l2))
   (OMEGA14 v l1 l2 x )).
Definition fast_Zred_factor0:=
[x:Z][P:Z -> Prop]
[H : (P (Zmult x (POS xH)) )]
 (eq_ind_r Z 
   (Zmult x (POS xH))
   P H 
   x
   (Zred_factor0 x)).

Definition fast_Zopp_one :=
[x:Z][P:Z -> Prop]
[H : (P (Zmult x (NEG xH)))]
 (eq_ind_r Z 
   (Zmult x (NEG xH))
   P H 
   (Zopp x)
   (Zopp_one x)).

Definition fast_Zmult_sym :=
[x,y :Z][P:Z -> Prop]
[H : (P (Zmult y x))]
 (eq_ind_r Z 
(Zmult y x)
   P H 
(Zmult x y)
   (Zmult_sym x y )).

Definition fast_Zopp_Zplus :=
[x,y :Z][P:Z -> Prop]
[H : (P (Zplus (Zopp x) (Zopp y)) )]
 (eq_ind_r Z 
   (Zplus (Zopp x) (Zopp y))
   P H 
   (Zopp (Zplus x y))
   (Zopp_Zplus x y )).

Definition fast_Zopp_Zopp :=
[x:Z][P:Z -> Prop]
[H : (P x )] (eq_ind_r Z x P H (Zopp (Zopp x)) (Zopp_Zopp x)).

Definition fast_Zopp_Zmult_r :=
[x,y:Z][P:Z -> Prop]
[H : (P (Zmult x (Zopp y)))]
 (eq_ind_r Z 
   (Zmult x (Zopp y))
   P H 
   (Zopp (Zmult x y))
   (Zopp_Zmult_r x y )).

Definition fast_Zmult_plus_distr :=
[n,m,p:Z][P:Z -> Prop]
[H : (P (Zplus (Zmult n p) (Zmult m p)))]
 (eq_ind_r Z 
   (Zplus (Zmult n p) (Zmult m p))
   P H 
   (Zmult (Zplus n m) p)
   (Zmult_plus_distr_l n m p)).
Definition fast_Zmult_Zopp_left:=
[x,y:Z][P:Z -> Prop]
[H : (P (Zmult x (Zopp y)))]
 (eq_ind_r Z 
   (Zmult x (Zopp y))
   P H 
   (Zmult (Zopp x) y)
   (Zmult_Zopp_left x y)).

Definition fast_Zmult_assoc_r :=
[n,m,p :Z][P:Z -> Prop]
[H : (P (Zmult n (Zmult m p)))]
 (eq_ind_r Z 
   (Zmult n (Zmult m p))
   P H 
   (Zmult (Zmult n m) p)
   (Zmult_assoc_r n m p)).

Definition fast_Zred_factor1 :=
[x:Z][P:Z -> Prop]
[H : (P (Zmult x (POS (xO xH))) )]
 (eq_ind_r Z 
   (Zmult x (POS (xO xH)))
   P H 
   (Zplus x x)
   (Zred_factor1 x)).

Definition fast_Zred_factor2 :=
[x,y:Z][P:Z -> Prop]
[H : (P (Zmult x (Zplus (POS xH) y)))]
 (eq_ind_r Z 
   (Zmult x (Zplus (POS xH) y))
   P H 
   (Zplus x (Zmult x y))
   (Zred_factor2 x y)).
Definition fast_Zred_factor3 :=
[x,y:Z][P:Z -> Prop]
[H : (P (Zmult x (Zplus (POS xH) y)))]
 (eq_ind_r Z 
   (Zmult x (Zplus (POS xH) y))
   P H 
   (Zplus (Zmult x y) x)
   (Zred_factor3 x y)).

Definition fast_Zred_factor4 :=
[x,y,z:Z][P:Z -> Prop]
[H : (P (Zmult x (Zplus y z)))]
 (eq_ind_r Z 
   (Zmult x (Zplus y z))
   P H 
   (Zplus (Zmult x y) (Zmult x z))
   (Zred_factor4 x y z)).

Definition fast_Zred_factor5 :=
[x,y:Z][P:Z -> Prop]
[H : (P y)]
 (eq_ind_r Z 
   y
   P H 
   (Zplus (Zmult x ZERO) y)
   (Zred_factor5 x y)).

Definition fast_Zred_factor6 :=
[x :Z][P:Z -> Prop]
[H : (P(Zplus x ZERO) )]
 (eq_ind_r Z 
   (Zplus x ZERO)
   P H 
   x
   (Zred_factor6 x )).
