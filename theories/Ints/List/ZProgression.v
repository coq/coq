
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

Require Export Iterator.
Require Import ZArith.
Require Export UList.
Open Scope Z_scope.
 
Theorem next_n_Z: forall n m,  next_n Zsucc n m = n + Z_of_nat m.
intros n m; generalize n; elim m; clear n m.
intros n; simpl; auto with zarith.
intros m H n.
replace (n + Z_of_nat (S m)) with (Zsucc n + Z_of_nat m); auto with zarith.
rewrite <- H; auto with zarith.
rewrite inj_S; auto with zarith.
Qed.
 
Theorem Zprogression_end:
 forall n m,
  progression Zsucc n (S m) =
  app (progression Zsucc n m) (cons (n + Z_of_nat m) nil).
intros n m; generalize n; elim m; clear n m.
simpl; intros; apply f_equal2 with ( f := @cons Z ); auto with zarith.
intros m1 Hm1 n1.
apply trans_equal with (cons n1 (progression Zsucc (Zsucc n1) (S m1))); auto.
rewrite Hm1.
replace (Zsucc n1 + Z_of_nat m1) with (n1 + Z_of_nat (S m1)); auto with zarith.
replace (Z_of_nat (S m1)) with (1 + Z_of_nat m1); auto with zarith.
rewrite inj_S; auto with zarith.
Qed.
 
Theorem Zprogression_pred_end:
 forall n m,
  progression Zpred n (S m) =
  app (progression Zpred n m) (cons (n - Z_of_nat m) nil).
intros n m; generalize n; elim m; clear n m.
simpl; intros; apply f_equal2 with ( f := @cons Z ); auto with zarith.
intros m1 Hm1 n1.
apply trans_equal with (cons n1 (progression Zpred (Zpred n1) (S m1))); auto.
rewrite Hm1.
replace (Zpred n1 - Z_of_nat m1) with (n1 - Z_of_nat (S m1)); auto with zarith.
replace (Z_of_nat (S m1)) with (1 + Z_of_nat m1); auto with zarith.
unfold Zpred; ring.
rewrite inj_S; auto with zarith.
Qed.
 
Theorem Zprogression_opp:
 forall n m,
  rev (progression Zsucc n m) = progression Zpred (n + Z_of_nat (pred m)) m.
intros n m; generalize n; elim m; clear n m.
simpl; auto.
intros m Hm n.
rewrite (Zprogression_end n); auto.
rewrite distr_rev.
rewrite Hm; simpl; auto.
case m.
simpl; auto.
intros m1;
 replace (n + Z_of_nat (pred (S m1))) with (Zpred (n + Z_of_nat (S m1))); auto.
rewrite inj_S; simpl; (unfold Zpred; unfold Zsucc); auto with zarith.
Qed.
 
Theorem Zprogression_le_init:
 forall n m p, In p (progression Zsucc n m) ->  (n <= p).
intros n m; generalize n; elim m; clear n m; simpl; auto.
intros; contradiction.
intros m H n p [H1|H1]; auto with zarith.
generalize (H _ _ H1); auto with zarith.
Qed.
 
Theorem Zprogression_le_end:
 forall n m p, In p (progression Zsucc n m) ->  (p < n + Z_of_nat m).
intros n m; generalize n; elim m; clear n m; auto.
intros; contradiction.
intros m H n p H1; simpl in H1 |-; case H1; clear H1; intros H1;
 auto with zarith.
subst n; auto with zarith.
apply Zle_lt_trans with (p + 0); auto with zarith.
apply Zplus_lt_compat_l; red; simpl; auto with zarith.
apply Zlt_le_trans with (Zsucc n + Z_of_nat m); auto with zarith.
rewrite inj_S; rewrite Zplus_succ_comm; auto with zarith.
Qed.
 
Theorem ulist_Zprogression: forall a n,  ulist (progression Zsucc a n).
intros a n; generalize a; elim n; clear a n; simpl; auto with zarith.
intros n H1 a; apply ulist_cons; auto.
intros H2; absurd (Zsucc a <= a); auto with zarith.
apply Zprogression_le_init with ( 1 := H2 ).
Qed.
 
Theorem in_Zprogression:
 forall a b n, ( a <= b < a + Z_of_nat n ) ->  In b (progression Zsucc a n).
intros a b n; generalize a b; elim n; clear a b n; auto with zarith.
simpl; auto with zarith.
intros n H a b.
replace (a + Z_of_nat (S n)) with (Zsucc a + Z_of_nat n); auto with zarith.
intros [H1 H2]; simpl; auto with zarith.
case (Zle_lt_or_eq _ _ H1); auto with zarith.
rewrite inj_S; auto with zarith.
Qed.
