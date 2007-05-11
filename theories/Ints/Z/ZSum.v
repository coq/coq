
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

(***********************************************************************
    Summation.v from Z to Z
 *********************************************************************)
Require Import Arith.
Require Import ArithRing.
Require Import ListAux.
Require Import ZArith.
Require Import ZAux.
Require Import Iterator.
Require Import ZProgression.


Open Scope Z_scope.
(* Iterated Sum *)
 
Definition Zsum :=
   fun n m f =>
   if Zle_bool n m
     then iter 0 f Zplus (progression Zsucc n (Zabs_nat ((1 + m) - n)))
     else iter 0 f Zplus (progression Zpred n (Zabs_nat ((1 + n) - m))).
Hint Unfold Zsum .
 
Lemma Zsum_nn: forall n f,  Zsum n n f = f n.
intros n f; unfold Zsum; rewrite Zle_bool_refl.
replace ((1 + n) - n) with 1; auto with zarith.
simpl; ring.
Qed.

Theorem permutation_rev: forall (A:Set) (l : list A),  permutation (rev l) l.
intros a l; elim l; simpl; auto.
intros a1 l1 Hl1.
apply permutation_trans with (cons a1 (rev l1)); auto.
change (permutation (rev l1 ++ (a1 :: nil)) (app (cons a1 nil) (rev l1))); auto.
Qed.
 
Lemma Zsum_swap: forall (n m : Z) (f : Z ->  Z),  Zsum n m f = Zsum m n f.
intros n m f; unfold Zsum.
generalize (Zle_cases n m) (Zle_cases m n); case (Zle_bool n m);
 case (Zle_bool m n); auto with arith.
intros; replace n with m; auto with zarith.
3:intros H1 H2; contradict H2; auto with zarith.
intros H1 H2; apply iter_permutation; auto with zarith.
apply permutation_trans
     with (rev (progression Zsucc n (Zabs_nat ((1 + m) - n)))).
apply permutation_sym; apply permutation_rev.
rewrite Zprogression_opp; auto with zarith.
replace (n + Z_of_nat (pred (Zabs_nat ((1 + m) - n)))) with m; auto.
replace (Zabs_nat ((1 + m) - n)) with (S (Zabs_nat (m - n))); auto with zarith.
simpl.
rewrite Z_of_nat_Zabs_nat; auto with zarith.
replace ((1 + m) - n) with (1 + (m - n)); auto with zarith.
cut (0 <= m - n); auto with zarith; unfold Zabs_nat.
case (m - n); auto with zarith.
intros p; case p; simpl; auto with zarith.
intros p1 Hp1; rewrite nat_of_P_xO; rewrite nat_of_P_xI;
 rewrite nat_of_P_succ_morphism.
simpl; repeat rewrite plus_0_r.
repeat rewrite <- plus_n_Sm; simpl; auto.
intros p H3; contradict H3; auto with zarith.
intros H1 H2; apply iter_permutation; auto with zarith.
apply permutation_trans
     with (rev (progression Zsucc m (Zabs_nat ((1 + n) - m)))).
rewrite Zprogression_opp; auto with zarith.
replace (m + Z_of_nat (pred (Zabs_nat ((1 + n) - m)))) with n; auto.
replace (Zabs_nat ((1 + n) - m)) with (S (Zabs_nat (n - m))); auto with zarith.
simpl.
rewrite Z_of_nat_Zabs_nat; auto with zarith.
replace ((1 + n) - m) with (1 + (n - m)); auto with zarith.
cut (0 <= n - m); auto with zarith; unfold Zabs_nat.
case (n - m); auto with zarith.
intros p; case p; simpl; auto with zarith.
intros p1 Hp1; rewrite nat_of_P_xO; rewrite nat_of_P_xI;
 rewrite nat_of_P_succ_morphism.
simpl; repeat rewrite plus_0_r.
repeat rewrite <- plus_n_Sm; simpl; auto.
intros p H3; contradict H3; auto with zarith.
apply permutation_rev.
Qed.
 
Lemma Zsum_split_up:
 forall (n m p : Z) (f : Z ->  Z),
 ( n <= m < p ) ->  Zsum n p f = Zsum n m f + Zsum (m + 1) p f.
intros n m p f [H H0].
case (Zle_lt_or_eq _ _ H); clear H; intros H.
unfold Zsum; (repeat rewrite Zle_imp_le_bool); auto with zarith.
assert (H1: n < p).
apply Zlt_trans with ( 1 := H ); auto with zarith.
assert (H2: m < 1 + p).
apply Zlt_trans with ( 1 := H0 ); auto with zarith.
assert (H3: n < 1 + m).
apply Zlt_trans with ( 1 := H ); auto with zarith.
assert (H4: n < 1 + p).
apply Zlt_trans with ( 1 := H1 ); auto with zarith.
replace (Zabs_nat ((1 + p) - (m + 1)))
     with (minus (Zabs_nat ((1 + p) - n)) (Zabs_nat ((1 + m) - n))).
apply iter_progression_app; auto with zarith.
apply inj_le_inv.
(repeat rewrite Z_of_nat_Zabs_nat); auto with zarith.
rewrite next_n_Z; auto with zarith.
rewrite Z_of_nat_Zabs_nat; auto with zarith.
apply inj_eq_inv; auto with zarith.
rewrite inj_minus1; auto with zarith.
(repeat rewrite Z_of_nat_Zabs_nat); auto with zarith.
apply inj_le_inv.
(repeat rewrite Z_of_nat_Zabs_nat); auto with zarith.
subst m.
rewrite Zsum_nn; auto with zarith.
unfold Zsum; generalize (Zle_cases n p); generalize (Zle_cases (n + 1) p);
 case (Zle_bool n p); case (Zle_bool (n + 1) p); auto with zarith.
intros H1 H2.
replace (Zabs_nat ((1 + p) - n)) with (S (Zabs_nat (p - n))); auto with zarith.
replace (n + 1) with (Zsucc n); auto with zarith.
replace ((1 + p) - Zsucc n) with (p - n); auto with zarith.
apply inj_eq_inv; auto with zarith.
rewrite inj_S; (repeat rewrite Z_of_nat_Zabs_nat); auto with zarith.
Qed.
 
Lemma Zsum_S_left:
 forall (n m : Z) (f : Z ->  Z), n < m ->  Zsum n m f = f n + Zsum (n + 1) m f.
intros n m f H; rewrite (Zsum_split_up n n m f); auto with zarith.
rewrite Zsum_nn; auto with zarith.
Qed.
 
Lemma Zsum_S_right:
 forall (n m : Z) (f : Z ->  Z),
 n <= m ->  Zsum n (m + 1) f = Zsum n m f  + f (m + 1).
intros n m f H; rewrite (Zsum_split_up n m (m + 1) f); auto with zarith.
rewrite Zsum_nn; auto with zarith.
Qed.
  
Lemma Zsum_split_down:
 forall (n m p : Z) (f : Z ->  Z),
 ( p < m <= n ) ->  Zsum n p f = Zsum n m f  + Zsum (m - 1) p f.
intros n m p f [H H0].
case (Zle_lt_or_eq p (m - 1)); auto with zarith; intros H1.
pattern m at 1; replace m with ((m - 1) + 1); auto with zarith.
repeat rewrite (Zsum_swap n).
rewrite (Zsum_swap (m - 1)).
rewrite Zplus_comm.
apply Zsum_split_up; auto with zarith.
subst p.
repeat rewrite (Zsum_swap n).
rewrite Zsum_nn.
unfold Zsum; (repeat rewrite Zle_imp_le_bool); auto with zarith.
replace (Zabs_nat ((1 + n) - (m - 1))) with (S (Zabs_nat (n - (m - 1)))).
rewrite Zplus_comm.
replace (Zabs_nat ((1 + n) - m)) with (Zabs_nat (n - (m - 1))); auto with zarith.
pattern m at 4; replace m with (Zsucc (m - 1)); auto with zarith.
apply f_equal with ( f := Zabs_nat ); auto with zarith.
apply inj_eq_inv; auto with zarith.
rewrite inj_S.
(repeat rewrite Z_of_nat_Zabs_nat); auto with zarith.
Qed.


Lemma Zsum_ext:
 forall (n m : Z) (f g : Z ->  Z),
 n <= m ->
 (forall (x : Z), ( n <= x <= m ) ->  f x = g x) ->  Zsum n m f = Zsum n m g.
intros n m f g HH H.
unfold Zsum; auto.
unfold Zsum; (repeat rewrite Zle_imp_le_bool); auto with zarith.
apply iter_ext; auto with zarith.
intros a H1; apply H; auto; split.
apply Zprogression_le_init with ( 1 := H1 ).
cut (a < Zsucc m); auto with zarith.
replace (Zsucc m) with (n + Z_of_nat (Zabs_nat ((1 + m) - n))); auto with zarith.
apply Zprogression_le_end; auto with zarith.
rewrite Z_of_nat_Zabs_nat; auto with zarith.
Qed.

Lemma Zsum_add:
 forall (n m : Z) (f g : Z ->  Z),
  Zsum n m f  + Zsum n m g = Zsum n m (fun (i : Z) => f i + g i).
intros n m f g; unfold Zsum; case (Zle_bool n m); apply iter_comp;
 auto with zarith.
Qed.
 
Lemma Zsum_times:
 forall n m x f,  x * Zsum n m f = Zsum n m (fun i=> x * f i).
intros n m x f.
unfold Zsum. case (Zle_bool n m); intros; apply iter_comp_const with (k := (fun y : Z => x * y)); auto with zarith.
Qed.
 
Lemma inv_Zsum:
 forall (P : Z ->  Prop) (n m : Z) (f : Z ->  Z),
 n <= m ->
 P 0 ->
 (forall (a b : Z), P a -> P b ->  P (a + b)) ->
 (forall (x : Z), ( n <= x <= m ) ->  P (f x)) ->  P (Zsum n m f).
intros P n m f HH H H0 H1.
unfold Zsum; rewrite Zle_imp_le_bool; auto with zarith; apply iter_inv; auto.
intros x H3; apply H1; auto; split.
apply Zprogression_le_init with ( 1 := H3 ).
cut (x < Zsucc m); auto with zarith.
replace (Zsucc m) with (n + Z_of_nat (Zabs_nat ((1 + m) - n))); auto with zarith.
apply Zprogression_le_end; auto with zarith.
rewrite Z_of_nat_Zabs_nat; auto with zarith.
Qed.


Lemma Zsum_pred:
 forall (n m : Z) (f : Z ->  Z),
  Zsum n m f = Zsum (n + 1) (m + 1) (fun (i : Z) => f (Zpred i)).
intros n m f.
unfold Zsum.
generalize (Zle_cases n m); generalize (Zle_cases (n + 1) (m + 1));
 case (Zle_bool n m); case (Zle_bool (n + 1) (m + 1)); auto with zarith.
replace ((1 + (m + 1)) - (n + 1)) with ((1 + m) - n); auto with zarith.
intros H1 H2; cut (exists c , c = Zabs_nat ((1 + m) - n) ).
intros [c H3]; rewrite <- H3.
generalize n; elim c; auto with zarith; clear H1 H2 H3 c n.
intros c H n; simpl; eq_tac; auto with zarith.
eq_tac; unfold Zpred; auto with zarith.
replace (Zsucc (n + 1)) with (Zsucc n + 1); auto with zarith.
exists (Zabs_nat ((1 + m) - n)); auto.
replace ((1 + (n + 1)) - (m + 1)) with ((1 + n) - m); auto with zarith.
intros H1 H2; cut (exists c , c = Zabs_nat ((1 + n) - m) ).
intros [c H3]; rewrite <- H3.
generalize n; elim c; auto with zarith; clear H1 H2 H3 c n.
intros c H n; simpl; (eq_tac; auto with zarith).
eq_tac; unfold Zpred; auto with zarith.
replace (Zpred (n + 1)) with (Zpred n + 1); auto with zarith.
unfold Zpred; auto with zarith.
exists (Zabs_nat ((1 + n) - m)); auto.
Qed.
 
Theorem Zsum_c:
 forall (c p q : Z), p <= q ->  Zsum p q (fun x => c) = ((1 + q) - p) * c.
intros c p q Hq; unfold Zsum.
rewrite Zle_imp_le_bool; auto with zarith.
pattern ((1 + q) - p) at 2; rewrite <- Z_of_nat_Zabs_nat; auto with zarith.
cut (exists r , r = Zabs_nat ((1 + q) - p) );
 [intros [r H1]; rewrite <- H1 | exists (Zabs_nat ((1 + q) - p))]; auto.
generalize p; elim r; auto with zarith.
intros n H p0; replace (Z_of_nat (S n)) with (Z_of_nat n + 1); auto with zarith.
simpl; rewrite H; ring.
rewrite inj_S; auto with zarith.
Qed.
 
Theorem Zsum_Zsum_f:
 forall (i j k l : Z) (f : Z -> Z ->  Z),
 i <= j ->
 k < l ->
  Zsum i j (fun x => Zsum k (l + 1) (fun y => f x y)) =
  Zsum i j (fun x => Zsum k l (fun y => f x y) + f x (l + 1)).
intros; apply Zsum_ext; intros; auto with zarith.
rewrite Zsum_S_right; auto with zarith.
Qed.
 
Theorem Zsum_com:
 forall (i j k l : Z) (f : Z -> Z ->  Z),
  Zsum i j (fun x => Zsum k l (fun y => f x y)) =
  Zsum k l (fun y => Zsum i j (fun x => f x y)).
intros; unfold Zsum; case (Zle_bool i j); case (Zle_bool k l); apply iter_com;
 auto with zarith.
Qed.
 
Theorem Zsum_le:
 forall (n m : Z) (f g : Z ->  Z),
 n <= m ->
 (forall (x : Z), ( n <= x <= m ) ->  (f x <= g x )) ->
  (Zsum n m f <= Zsum n m g ).
intros n m f g Hl H.
unfold Zsum; rewrite Zle_imp_le_bool; auto with zarith.
unfold Zsum;
 cut
  (forall x,
   In x (progression Zsucc n (Zabs_nat ((1 + m) - n))) ->  ( f x <= g x )).
elim (progression Zsucc n (Zabs_nat ((1 + m) - n))); simpl; auto with zarith.
intros x H1; apply H; split.
apply Zprogression_le_init with ( 1 := H1 ); auto.
cut (x < m + 1); auto with zarith.
replace (m + 1) with (n + Z_of_nat (Zabs_nat ((1 + m) - n))); auto with zarith.
apply Zprogression_le_end; auto with zarith.
rewrite Z_of_nat_Zabs_nat; auto with zarith.
Qed.

Theorem iter_le:
forall (f g: Z -> Z)  l, (forall a, In a l -> f a <= g a) ->
  iter 0 f Zplus l <= iter 0 g Zplus l.
intros f g l; elim l; simpl; auto with zarith.
Qed.
 
Theorem Zsum_lt:
 forall n m f g,
 (forall x, n <= x -> x <= m ->  f x <= g x) ->
 (exists x, n <= x /\ x <= m /\  f x < g x) ->
  Zsum n m f < Zsum n m g.
intros n m f g H (d, (Hd1, (Hd2, Hd3))); unfold Zsum; rewrite Zle_imp_le_bool; auto with zarith.
cut (In d (progression  Zsucc n (Zabs_nat (1 + m - n)))).
cut (forall x, In x (progression Zsucc n (Zabs_nat (1 + m - n)))->  f x <= g x).
elim (progression  Zsucc n (Zabs_nat (1 + m - n))); simpl; auto with zarith.
intros a l Rec  H0 [H1 | H1]; subst; auto.
apply Zle_lt_trans with (f d + iter 0 g Zplus l); auto with zarith.
apply Zplus_le_compat_l.
apply iter_le; auto.
apply Zlt_le_trans with (f a + iter 0 g Zplus l); auto with zarith.
intros x H1; apply H.
apply Zprogression_le_init with ( 1 := H1 ); auto.
cut (x < m + 1); auto with zarith.
replace (m + 1) with (n + Z_of_nat (Zabs_nat ((1 + m) - n))); auto with zarith.
apply Zprogression_le_end with ( 1 := H1 ); auto with arith.
rewrite Z_of_nat_Zabs_nat; auto with zarith.
apply in_Zprogression.
rewrite Z_of_nat_Zabs_nat; auto with zarith.
Qed.
 
Theorem Zsum_minus:
 forall n m f g,  Zsum n m f - Zsum n m g = Zsum n m (fun x => f x - g x).
intros n m f g; apply trans_equal with (Zsum n m f + (-1) * Zsum n m g); auto with zarith.
rewrite Zsum_times; rewrite Zsum_add; auto with zarith.
Qed.
