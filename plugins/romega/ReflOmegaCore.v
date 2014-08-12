(* -*- coding: utf-8 -*- *)
(*************************************************************************

   PROJET RNRT Calife - 2001
   Author: Pierre Crégut - France Télécom R&D
   Licence du projet : LGPL version 2.1

 *************************************************************************)

Require Import List Bool Sumbool EqNat Setoid Ring_theory Decidable ZArith_base.
Delimit Scope Int_scope with I.

(* Abstract Integers. *)

Module Type Int.

  Parameter t : Set.

  Parameter zero : t.
  Parameter one : t.
  Parameter plus : t -> t -> t.
  Parameter opp : t -> t.
  Parameter minus : t -> t -> t.
  Parameter mult : t -> t -> t.

  Notation "0" := zero : Int_scope.
  Notation "1" := one : Int_scope.
  Infix "+" := plus : Int_scope.
  Infix "-" := minus : Int_scope.
  Infix "*" := mult : Int_scope.
  Notation "- x" := (opp x) : Int_scope.

  Open Scope Int_scope.

  (* First, int is a ring: *)
  Axiom ring : @ring_theory t 0 1 plus mult minus opp (@eq t).

  (* int should also be ordered: *)

  Parameter le : t -> t -> Prop.
  Parameter lt : t -> t -> Prop.
  Parameter ge : t -> t -> Prop.
  Parameter gt : t -> t -> Prop.
  Notation "x <= y" := (le x y): Int_scope.
  Notation "x < y" := (lt x y) : Int_scope.
  Notation "x >= y" := (ge x y) : Int_scope.
  Notation "x > y" := (gt x y): Int_scope.
  Axiom le_lt_iff : forall i j, (i<=j) <-> ~(j<i).
  Axiom ge_le_iff : forall i j, (i>=j) <-> (j<=i).
  Axiom gt_lt_iff : forall i j, (i>j) <-> (j<i).

  (* Basic properties of this order *)
  Axiom lt_trans : forall i j k, i<j -> j<k -> i<k.
  Axiom lt_not_eq : forall i j, i<j -> i<>j.

  (* Compatibilities *)
  Axiom lt_0_1 : 0<1.
  Axiom plus_le_compat : forall i j k l, i<=j -> k<=l -> i+k<=j+l.
  Axiom opp_le_compat : forall i j, i<=j -> (-j)<=(-i).
  Axiom mult_lt_compat_l :
   forall i j k, 0 < k -> i < j -> k*i<k*j.

  (* We should have a way to decide the equality and the order*)
  Parameter compare : t -> t -> comparison.
  Infix "?=" := compare (at level 70, no associativity) : Int_scope.
  Axiom compare_Eq : forall i j, compare i j = Eq <-> i=j.
  Axiom compare_Lt : forall i j, compare i j = Lt <-> i<j.
  Axiom compare_Gt : forall i j, compare i j = Gt <-> i>j.

  (* Up to here, these requirements could be fulfilled
     by any totally ordered ring. Let's now be int-specific: *)
  Axiom le_lt_int : forall x y, x<y <-> x<=y+-(1).

  (* Btw, lt_0_1 could be deduced from this last axiom *)

End Int.



(* Of course, Z is a model for our abstract int *)

Module Z_as_Int <: Int.

  Open Scope Z_scope.

  Definition t := Z.
  Definition zero := 0.
  Definition one := 1.
  Definition plus := Z.add.
  Definition opp := Z.opp.
  Definition minus := Z.sub.
  Definition mult := Z.mul.

  Lemma ring : @ring_theory t zero one plus mult minus opp (@eq t).
  Proof.
  constructor.
  exact Z.add_0_l.
  exact Z.add_comm.
  exact Z.add_assoc.
  exact Z.mul_1_l.
  exact Z.mul_comm.
  exact Z.mul_assoc.
  exact Z.mul_add_distr_r.
  unfold minus, Z.sub; auto.
  exact Z.add_opp_diag_r.
  Qed.

  Definition le := Z.le.
  Definition lt := Z.lt.
  Definition ge := Z.ge.
  Definition gt := Z.gt.
  Definition le_lt_iff := Z.le_ngt.
  Definition ge_le_iff := Z.ge_le_iff.
  Definition gt_lt_iff := Z.gt_lt_iff.

  Definition lt_trans := Z.lt_trans.
  Definition lt_not_eq := Z.lt_neq.

  Definition lt_0_1 := Z.lt_0_1.
  Definition plus_le_compat := Z.add_le_mono.
  Definition mult_lt_compat_l := Zmult_lt_compat_l.
  Lemma opp_le_compat i j : i<=j -> (-j)<=(-i).
  Proof. apply -> Z.opp_le_mono. Qed.

  Definition compare := Z.compare.
  Definition compare_Eq := Z.compare_eq_iff.
  Lemma compare_Lt i j : compare i j = Lt <-> i<j.
  Proof. reflexivity. Qed.
  Lemma compare_Gt i j : compare i j = Gt <-> i>j.
  Proof. reflexivity. Qed.

  Definition le_lt_int := Z.lt_le_pred.

End Z_as_Int.




Module IntProperties (I:Int).
 Import I.
 Local Notation int := I.t.

 (* Primo, some consequences of being a ring theory... *)

 Definition two := 1+1.
 Notation "2" := two : Int_scope.

 (* Aliases for properties packed in the ring record. *)

 Definition plus_assoc := ring.(Radd_assoc).
 Definition plus_comm := ring.(Radd_comm).
 Definition plus_0_l := ring.(Radd_0_l).
 Definition mult_assoc := ring.(Rmul_assoc).
 Definition mult_comm := ring.(Rmul_comm).
 Definition mult_1_l := ring.(Rmul_1_l).
 Definition mult_plus_distr_r := ring.(Rdistr_l).
 Definition opp_def := ring.(Ropp_def).
 Definition minus_def := ring.(Rsub_def).

 Opaque plus_assoc plus_comm plus_0_l mult_assoc mult_comm mult_1_l
  mult_plus_distr_r opp_def minus_def.

 (* More facts about plus *)

 Lemma plus_0_r : forall x, x+0 = x.
 Proof. intros; rewrite plus_comm; apply plus_0_l. Qed.

 Lemma plus_0_r_reverse : forall x, x = x+0.
 Proof. intros; symmetry; apply plus_0_r. Qed.

 Lemma plus_assoc_reverse : forall x y z, x+y+z = x+(y+z).
 Proof. intros; symmetry; apply plus_assoc. Qed.

 Lemma plus_permute : forall x y z, x+(y+z) = y+(x+z).
 Proof. intros; do 2 rewrite plus_assoc; f_equal; apply plus_comm. Qed.

 Lemma plus_reg_l : forall x y z, x+y = x+z -> y = z.
 Proof.
  intros.
  rewrite (plus_0_r_reverse y), (plus_0_r_reverse z), <-(opp_def x).
  now rewrite plus_permute, plus_assoc, H, <- plus_assoc, plus_permute.
 Qed.

 (* More facts about mult *)

 Lemma mult_assoc_reverse : forall x y z, x*y*z = x*(y*z).
 Proof. intros; symmetry; apply mult_assoc. Qed.

 Lemma mult_plus_distr_l : forall x y z, x*(y+z)=x*y+x*z.
 Proof.
  intros.
  rewrite (mult_comm x (y+z)), (mult_comm x y), (mult_comm x z).
  apply mult_plus_distr_r.
 Qed.

 Lemma mult_0_l : forall x, 0*x = 0.
 Proof.
  intros.
  generalize (mult_plus_distr_r 0 1 x).
  rewrite plus_0_l, mult_1_l, plus_comm; intros.
  apply plus_reg_l with x.
  rewrite <- H.
  apply plus_0_r_reverse.
 Qed.


 (* More facts about opp *)

 Definition plus_opp_r := opp_def.

 Lemma plus_opp_l : forall x, -x + x = 0.
 Proof. intros; now rewrite plus_comm, opp_def. Qed.

 Lemma mult_opp_comm : forall x y, - x * y = x * - y.
 Proof.
  intros.
  apply plus_reg_l with (x*y).
  rewrite <- mult_plus_distr_l, <- mult_plus_distr_r.
  now rewrite opp_def, opp_def, mult_0_l, mult_comm, mult_0_l.
 Qed.

 Lemma opp_eq_mult_neg_1 : forall x, -x = x * -(1).
 Proof.
  intros; now rewrite mult_comm, mult_opp_comm, mult_1_l.
 Qed.

 Lemma opp_involutive : forall x, -(-x) = x.
 Proof.
  intros.
  apply plus_reg_l with (-x).
  now rewrite opp_def, plus_comm, opp_def.
 Qed.

 Lemma opp_plus_distr : forall x y, -(x+y) = -x + -y.
 Proof.
  intros.
  apply plus_reg_l with (x+y).
  rewrite opp_def.
  rewrite plus_permute.
  do 2 rewrite plus_assoc.
  now rewrite (plus_comm (-x)), opp_def, plus_0_l, opp_def.
 Qed.

 Lemma opp_mult_distr_r : forall x y, -(x*y) = x * -y.
 Proof.
  intros.
  rewrite <- mult_opp_comm.
  apply plus_reg_l with (x*y).
  now rewrite opp_def, <-mult_plus_distr_r, opp_def, mult_0_l.
 Qed.

 Lemma egal_left : forall n m, n=m -> n+-m = 0.
 Proof. intros; subst; apply opp_def. Qed.

 Lemma ne_left_2 : forall x y : int, x<>y -> 0<>(x + - y).
 Proof.
 intros; contradict H.
 apply (plus_reg_l (-y)).
 now rewrite plus_opp_l, plus_comm, H.
 Qed.

 (* Special lemmas for factorisation. *)

 Lemma red_factor0 : forall n, n = n*1.
 Proof. symmetry; rewrite mult_comm; apply mult_1_l. Qed.

 Lemma red_factor1 : forall n, n+n = n*2.
 Proof.
  intros; unfold two.
  now rewrite mult_comm, mult_plus_distr_r, mult_1_l.
 Qed.

 Lemma red_factor2 : forall n m, n + n*m = n * (1+m).
 Proof.
  intros; rewrite mult_plus_distr_l.
  f_equal; now rewrite mult_comm, mult_1_l.
 Qed.

 Lemma red_factor3 : forall n m, n*m + n = n*(1+m).
 Proof. intros; now rewrite plus_comm, red_factor2. Qed.

 Lemma red_factor4 : forall n m p, n*m + n*p = n*(m+p).
 Proof.
  intros; now rewrite mult_plus_distr_l.
 Qed.

 Lemma red_factor5 : forall n m , n * 0 + m = m.
 Proof. intros; now rewrite mult_comm, mult_0_l, plus_0_l. Qed.

 Definition red_factor6 := plus_0_r_reverse.


 (* Specialized distributivities *)

 Hint Rewrite mult_plus_distr_l mult_plus_distr_r mult_assoc : int.
 Hint Rewrite <- plus_assoc : int.

 Lemma OMEGA10 :
  forall v c1 c2 l1 l2 k1 k2 : int,
  (v * c1 + l1) * k1 + (v * c2 + l2) * k2 =
  v * (c1 * k1 + c2 * k2) + (l1 * k1 + l2 * k2).
 Proof.
  intros; autorewrite with int; f_equal; now rewrite plus_permute.
 Qed.

 Lemma OMEGA11 :
  forall v1 c1 l1 l2 k1 : int,
  (v1 * c1 + l1) * k1 + l2 = v1 * (c1 * k1) + (l1 * k1 + l2).
 Proof.
  intros; now autorewrite with int.
 Qed.

 Lemma OMEGA12 :
  forall v2 c2 l1 l2 k2 : int,
  l1 + (v2 * c2 + l2) * k2 = v2 * (c2 * k2) + (l1 + l2 * k2).
 Proof.
  intros; autorewrite with int; now rewrite plus_permute.
 Qed.

 Lemma OMEGA13 :
  forall v l1 l2 x : int,
  v * -x + l1 + (v * x + l2) = l1 + l2.
 Proof.
 intros; autorewrite with int.
 rewrite plus_permute; f_equal.
 rewrite plus_assoc.
 now rewrite <- mult_plus_distr_l, plus_opp_l, mult_comm, mult_0_l, plus_0_l.
 Qed.

 Lemma OMEGA15 :
  forall v c1 c2 l1 l2 k2 : int,
  v * c1 + l1 + (v * c2 + l2) * k2 = v * (c1 + c2 * k2) + (l1 + l2 * k2).
 Proof.
  intros; autorewrite with int; f_equal; now rewrite plus_permute.
 Qed.

 Lemma OMEGA16 : forall v c l k : int, (v * c + l) * k = v * (c * k) + l * k.
 Proof.
  intros; now autorewrite with int.
 Qed.

 Lemma sum1 : forall a b c d : int, 0 = a -> 0 = b -> 0 = a * c + b * d.
 Proof.
 intros; elim H; elim H0; simpl; auto.
 now rewrite mult_0_l, mult_0_l, plus_0_l.
 Qed.


 (* Secondo, some results about order (and equality) *)

 Lemma lt_irrefl : forall n, ~ n<n.
 Proof.
 intros n H.
 elim (lt_not_eq _ _ H); auto.
 Qed.

 Lemma lt_antisym : forall n m, n<m -> m<n -> False.
 Proof.
 intros; elim (lt_irrefl _ (lt_trans _ _ _ H H0)); auto.
 Qed.

 Lemma lt_le_weak : forall n m, n<m -> n<=m.
 Proof.
  intros; rewrite le_lt_iff; intro H'; eapply lt_antisym; eauto.
 Qed.

 Lemma le_refl : forall n, n<=n.
 Proof.
 intros; rewrite le_lt_iff; apply lt_irrefl; auto.
 Qed.

 Lemma le_antisym : forall n m, n<=m -> m<=n -> n=m.
 Proof.
 intros n m; do 2 rewrite le_lt_iff; intros.
 rewrite <- compare_Lt in H0.
 rewrite <- gt_lt_iff, <- compare_Gt in H.
 rewrite <- compare_Eq.
 destruct compare; intuition.
 Qed.

 Lemma lt_eq_lt_dec : forall n m, { n<m }+{ n=m }+{ m<n }.
 Proof.
  intros.
  generalize (compare_Lt n m)(compare_Eq n m)(compare_Gt n m).
  destruct compare; [ left; right | left; left | right ]; intuition.
  rewrite gt_lt_iff in H1; intuition.
 Qed.

 Lemma lt_dec : forall n m: int, { n<m } + { ~n<m }.
 Proof.
  intros.
  generalize (compare_Lt n m)(compare_Eq n m)(compare_Gt n m).
  destruct compare; [ right | left | right ]; intuition discriminate.
 Qed.

 Lemma lt_le_iff : forall n m, (n<m) <-> ~(m<=n).
 Proof.
  intros.
  rewrite le_lt_iff.
  destruct (lt_dec n m); intuition.
 Qed.

 Lemma le_dec : forall n m: int, { n<=m } + { ~n<=m }.
 Proof.
  intros; destruct (lt_dec m n); [right|left]; rewrite le_lt_iff; intuition.
 Qed.

 Lemma le_lt_dec : forall n m, { n<=m } + { m<n }.
 Proof.
  intros; destruct (le_dec n m); [left|right]; auto; now rewrite lt_le_iff.
 Qed.


 Definition beq i j := match compare i j with Eq => true | _ => false end.

 Lemma beq_iff : forall i j, beq i j = true <-> i=j.
 Proof.
 intros; unfold beq; generalize (compare_Eq i j).
 destruct compare; intuition discriminate.
 Qed.

 Lemma beq_true : forall i j, beq i j = true -> i=j.
 Proof.
 intros.
 rewrite <- beq_iff; auto.
 Qed.

 Lemma beq_false : forall i j, beq i j = false -> i<>j.
 Proof.
 intros.
 intro H'.
 rewrite <- beq_iff in H'; rewrite H' in H; discriminate.
 Qed.

 Lemma eq_dec : forall n m:int, { n=m } + { n<>m }.
 Proof.
  intros; generalize (beq_iff n m); destruct beq; [left|right]; intuition.
 Qed.

 Definition bgt i j := match compare i j with Gt => true | _ => false end.

 Lemma bgt_iff : forall i j, bgt i j = true <-> i>j.
 Proof.
 intros; unfold bgt; generalize (compare_Gt i j).
 destruct compare; intuition discriminate.
 Qed.

 Lemma bgt_true : forall i j, bgt i j = true -> i>j.
 Proof. intros; now rewrite <- bgt_iff. Qed.

 Lemma bgt_false : forall i j, bgt i j = false -> i<=j.
 Proof.
  intros.
  rewrite le_lt_iff, <-gt_lt_iff, <-bgt_iff; intro H'; now rewrite H' in H.
 Qed.

 Lemma le_is_lt_or_eq : forall n m, n<=m -> { n<m } + { n=m }.
 Proof.
  intros.
  destruct (eq_dec n m) as [H'|H'].
  right; intuition.
  left; rewrite lt_le_iff.
  contradict H'.
  apply le_antisym; auto.
 Qed.

 Lemma le_neq_lt : forall n m, n<=m -> n<>m -> n<m.
 Proof.
  intros.
  destruct (le_is_lt_or_eq _ _ H); intuition.
 Qed.

 Lemma le_trans : forall n m p, n<=m -> m<=p -> n<=p.
 Proof.
  intros n m p; do 3 rewrite le_lt_iff; intros A B C.
  destruct (lt_eq_lt_dec p m) as [[H|H]|H]; subst; auto.
  generalize (lt_trans _ _ _ H C); intuition.
 Qed.

 (* order and operations *)

 Lemma le_0_neg : forall n, 0 <= n <-> -n <= 0.
 Proof.
 intros.
 pattern 0 at 2; rewrite <- (mult_0_l (-(1))).
 rewrite <- opp_eq_mult_neg_1.
 split; intros.
 apply opp_le_compat; auto.
 rewrite <-(opp_involutive 0), <-(opp_involutive n).
 apply opp_le_compat; auto.
 Qed.

 Lemma le_0_neg' : forall n, n <= 0 <-> 0 <= -n.
 Proof.
 intros; rewrite le_0_neg, opp_involutive; intuition.
 Qed.

 Lemma plus_le_reg_r : forall n m p, n + p <= m + p -> n <= m.
 Proof.
 intros.
 replace n with ((n+p)+-p).
 replace m with ((m+p)+-p).
 apply plus_le_compat; auto.
 apply le_refl.
 now rewrite <- plus_assoc, opp_def, plus_0_r.
 now rewrite <- plus_assoc, opp_def, plus_0_r.
 Qed.

 Lemma plus_le_lt_compat : forall n m p q, n<=m -> p<q -> n+p<m+q.
 Proof.
 intros.
 apply le_neq_lt.
 apply plus_le_compat; auto.
 apply lt_le_weak; auto.
 rewrite lt_le_iff in H0.
 contradict H0.
 apply plus_le_reg_r with m.
 rewrite (plus_comm q m), <-H0, (plus_comm p m).
 apply plus_le_compat; auto.
 apply le_refl; auto.
 Qed.

 Lemma plus_lt_compat : forall n m p q, n<m -> p<q -> n+p<m+q.
 Proof.
 intros.
 apply plus_le_lt_compat; auto.
 apply lt_le_weak; auto.
 Qed.

 Lemma opp_lt_compat : forall n m, n<m -> -m < -n.
 Proof.
 intros n m; do 2 rewrite lt_le_iff; intros H; contradict H.
 rewrite <-(opp_involutive m), <-(opp_involutive n).
 apply opp_le_compat; auto.
 Qed.

 Lemma lt_0_neg : forall n, 0 < n <-> -n < 0.
 Proof.
 intros.
 pattern 0 at 2; rewrite <- (mult_0_l (-(1))).
 rewrite <- opp_eq_mult_neg_1.
 split; intros.
 apply opp_lt_compat; auto.
 rewrite <-(opp_involutive 0), <-(opp_involutive n).
 apply opp_lt_compat; auto.
 Qed.

 Lemma lt_0_neg' : forall n, n < 0 <-> 0 < -n.
 Proof.
 intros; rewrite lt_0_neg, opp_involutive; intuition.
 Qed.

 Lemma mult_lt_0_compat : forall n m, 0 < n -> 0 < m -> 0 < n*m.
 Proof.
 intros.
 rewrite <- (mult_0_l n), mult_comm.
 apply mult_lt_compat_l; auto.
 Qed.

 Lemma mult_integral : forall n m, n * m = 0 -> n = 0 \/ m = 0.
 Proof.
 intros.
 destruct (lt_eq_lt_dec n 0) as [[Hn|Hn]|Hn]; auto;
  destruct (lt_eq_lt_dec m 0) as [[Hm|Hm]|Hm]; auto; exfalso.

 rewrite lt_0_neg' in Hn.
 rewrite lt_0_neg' in Hm.
 generalize (mult_lt_0_compat _ _ Hn Hm).
 rewrite <- opp_mult_distr_r, mult_comm, <- opp_mult_distr_r, opp_involutive.
 rewrite mult_comm, H.
 exact (lt_irrefl 0).

 rewrite lt_0_neg' in Hn.
 generalize (mult_lt_0_compat _ _ Hn Hm).
 rewrite mult_comm, <- opp_mult_distr_r, mult_comm.
 rewrite H.
 rewrite opp_eq_mult_neg_1, mult_0_l.
 exact (lt_irrefl 0).

 rewrite lt_0_neg' in Hm.
 generalize (mult_lt_0_compat _ _ Hn Hm).
 rewrite <- opp_mult_distr_r.
 rewrite H.
 rewrite opp_eq_mult_neg_1, mult_0_l.
 exact (lt_irrefl 0).

 generalize (mult_lt_0_compat _ _ Hn Hm).
 rewrite H.
 exact (lt_irrefl 0).
 Qed.

 Lemma mult_le_compat :
   forall i j k l, i<=j -> k<=l -> 0<=i -> 0<=k -> i*k<=j*l.
 Proof.
 intros.
 destruct (le_is_lt_or_eq _ _ H1).

 apply le_trans with (i*l).
 destruct (le_is_lt_or_eq _ _ H0); [ | subst; apply le_refl].
 apply lt_le_weak.
 apply mult_lt_compat_l; auto.

 generalize (le_trans _ _ _ H2 H0); clear H0 H1 H2; intros.
 rewrite (mult_comm i), (mult_comm j).
 destruct (le_is_lt_or_eq _ _ H0);
  [ | subst; do 2 rewrite mult_0_l; apply le_refl].
 destruct (le_is_lt_or_eq _ _ H);
  [ | subst; apply le_refl].
 apply lt_le_weak.
 apply mult_lt_compat_l; auto.

 subst i.
 rewrite mult_0_l.
 generalize (le_trans _ _ _ H2 H0); clear H0 H1 H2; intros.
 destruct (le_is_lt_or_eq _ _ H);
  [ | subst; rewrite mult_0_l; apply le_refl].
 destruct (le_is_lt_or_eq _ _ H0);
  [ | subst; rewrite mult_comm, mult_0_l; apply le_refl].
 apply lt_le_weak.
 apply mult_lt_0_compat; auto.
 Qed.

 Lemma sum5 :
 forall a b c d : int, c <> 0 -> 0 <> a -> 0 = b -> 0 <> a * c + b * d.
 Proof.
 intros.
 subst b; rewrite mult_0_l, plus_0_r.
 contradict H.
 symmetry in H; destruct (mult_integral _ _ H); congruence.
 Qed.

 Lemma one_neq_zero : 1 <> 0.
 Proof.
 red; intro.
 symmetry in H.
 apply (lt_not_eq 0 1); auto.
 apply lt_0_1.
 Qed.

 Lemma minus_one_neq_zero : -(1) <> 0.
 Proof.
 apply lt_not_eq.
 rewrite <- lt_0_neg.
 apply lt_0_1.
 Qed.

 Lemma le_left : forall n m, n <= m -> 0 <= m + - n.
 Proof.
  intros.
  rewrite <- (opp_def m).
  apply plus_le_compat.
  apply le_refl.
  apply opp_le_compat; auto.
 Qed.

 Lemma OMEGA2 : forall x y, 0 <= x -> 0 <= y -> 0 <= x + y.
 Proof.
 intros.
 replace 0 with (0+0).
 apply plus_le_compat; auto.
 rewrite plus_0_l; auto.
 Qed.

 Lemma OMEGA8 : forall x y, 0 <= x -> 0 <= y -> x = - y -> x = 0.
 Proof.
 intros.
 assert (y=-x).
  subst x; symmetry; apply opp_involutive.
 clear H1; subst y.
 destruct (eq_dec 0 x) as [H'|H']; auto.
 assert (H'':=le_neq_lt _ _ H H').
 generalize (plus_le_lt_compat _ _ _ _ H0 H'').
 rewrite plus_opp_l, plus_0_l.
 intros.
 elim (lt_not_eq _ _ H1); auto.
 Qed.

 Lemma sum2 :
 forall a b c d : int, 0 <= d -> 0 = a -> 0 <= b -> 0 <= a * c + b * d.
 Proof.
 intros.
 subst a; rewrite mult_0_l, plus_0_l.
 rewrite <- (mult_0_l 0).
 apply mult_le_compat; auto; apply le_refl.
 Qed.

 Lemma sum3 :
 forall a b c d : int,
  0 <= c -> 0 <= d -> 0 <= a -> 0 <= b -> 0 <= a * c + b * d.
 Proof.
 intros.
 rewrite <- (plus_0_l 0).
 apply plus_le_compat; auto.
 rewrite <- (mult_0_l 0).
 apply mult_le_compat; auto; apply le_refl.
 rewrite <- (mult_0_l 0).
 apply mult_le_compat; auto; apply le_refl.
 Qed.

 Lemma sum4 : forall k : int, k>0 -> 0 <= k.
 Proof.
 intros k; rewrite gt_lt_iff; apply lt_le_weak.
 Qed.

 (* Lemmas specific to integers (they use lt_le_int) *)

 Lemma lt_left : forall n m, n < m -> 0 <= m + -(1) + - n.
 Proof.
 intros; apply le_left.
 now rewrite <- le_lt_int.
 Qed.

 Lemma lt_left_inv : forall x y, 0 <= y + -(1) + - x -> x < y.
 Proof.
 intros.
 generalize (plus_le_compat _ _ _ _ H (le_refl x)); clear H.
 now rewrite plus_0_l, <-plus_assoc, plus_opp_l, plus_0_r, le_lt_int.
 Qed.

 Lemma OMEGA4 : forall x y z, x > 0 -> y > x -> z * y + x <> 0.
 Proof.
 intros.
 intro H'.
 rewrite gt_lt_iff in H,H0.
 destruct (lt_eq_lt_dec z 0) as [[G|G]|G].

 rewrite lt_0_neg' in G.
 generalize (plus_le_lt_compat _ _ _ _ (le_refl (z*y)) H0).
 rewrite H'.
 pattern y at 2; rewrite <-(mult_1_l y), <-mult_plus_distr_r.
 intros.
 rewrite le_lt_int in G.
 rewrite <- opp_plus_distr in G.
 assert (0 < y) by (apply lt_trans with x; auto).
 generalize (mult_le_compat _ _ _ _ G (lt_le_weak _ _ H2) (le_refl 0) (le_refl 0)).
 rewrite mult_0_l, mult_comm, <- opp_mult_distr_r, mult_comm, <-le_0_neg', le_lt_iff.
 intuition.

 subst; rewrite mult_0_l, plus_0_l in H'; subst.
 apply (lt_not_eq _ _ H); auto.

 apply (lt_not_eq 0 (z*y+x)); auto.
 rewrite <- (plus_0_l 0).
 apply plus_lt_compat; auto.
 apply mult_lt_0_compat; auto.
 apply lt_trans with x; auto.
 Qed.

 Lemma OMEGA19 : forall x, x<>0 -> 0 <= x + -(1) \/ 0 <= x * -(1) + -(1).
 Proof.
 intros.
 do 2 rewrite <- le_lt_int.
 rewrite <- opp_eq_mult_neg_1.
 destruct (lt_eq_lt_dec 0 x) as [[H'|H']|H'].
 auto.
 congruence.
 right.
 rewrite <-(mult_0_l (-(1))), <-(opp_eq_mult_neg_1 0).
 apply opp_lt_compat; auto.
 Qed.

 Lemma mult_le_approx :
  forall n m p, n > 0 -> n > p -> 0 <= m * n + p -> 0 <= m.
 Proof.
 intros n m p.
 do 2 rewrite gt_lt_iff.
 do 2 rewrite le_lt_iff; intros.
 contradict H1.
 rewrite lt_0_neg' in H1.
 rewrite lt_0_neg'.
 rewrite opp_plus_distr.
 rewrite mult_comm, opp_mult_distr_r.
 rewrite le_lt_int.
 rewrite <- plus_assoc, (plus_comm (-p)), plus_assoc.
 apply lt_left.
 rewrite le_lt_int.
 rewrite le_lt_int in H0.
 apply le_trans with (n+-(1)); auto.
 apply plus_le_compat; [ | apply le_refl ].
 rewrite le_lt_int in H1.
 generalize (mult_le_compat _ _ _ _ (lt_le_weak _ _ H) H1 (le_refl 0) (le_refl 0)).
 rewrite mult_0_l.
 rewrite mult_plus_distr_l.
 rewrite <- opp_eq_mult_neg_1.
 intros.
 generalize (plus_le_compat _ _ _ _ (le_refl n) H2).
 now rewrite plus_permute, opp_def, plus_0_r, plus_0_r.
 Qed.

 (* Some decidabilities *)

 Lemma dec_eq : forall i j:int, decidable (i=j).
 Proof.
  red; intros; destruct (eq_dec i j); auto.
 Qed.

 Lemma dec_ne : forall i j:int, decidable (i<>j).
 Proof.
  red; intros; destruct (eq_dec i j); auto.
 Qed.

 Lemma dec_le : forall i j:int, decidable (i<=j).
 Proof.
  red; intros; destruct (le_dec i j); auto.
 Qed.

 Lemma dec_lt : forall i j:int, decidable (i<j).
 Proof.
  red; intros; destruct (lt_dec i j); auto.
 Qed.

 Lemma dec_ge : forall i j:int, decidable (i>=j).
 Proof.
  red; intros; rewrite ge_le_iff; destruct (le_dec j i); auto.
 Qed.

 Lemma dec_gt : forall i j:int, decidable (i>j).
 Proof.
  red; intros; rewrite gt_lt_iff; destruct (lt_dec j i); auto.
 Qed.

End IntProperties.




Module IntOmega (I:Int).
Import I.
Module IP:=IntProperties(I).
Import IP.
Local Notation int := I.t.

(* \subsubsection{Definition of reified integer expressions}
   Terms are either:
   \begin{itemize}
   \item integers [Tint]
   \item variables [Tvar]
   \item operation over integers (addition, product, opposite, subtraction)
   The last two are translated in additions and products. *)

Inductive term : Set :=
  | Tint : int -> term
  | Tplus : term -> term -> term
  | Tmult : term -> term -> term
  | Tminus : term -> term -> term
  | Topp : term -> term
  | Tvar : nat -> term.

Delimit Scope romega_scope with term.
Arguments Tint _%I.
Arguments Tplus (_ _)%term.
Arguments Tmult (_ _)%term.
Arguments Tminus (_ _)%term.
Arguments Topp _%term.

Infix "+" := Tplus : romega_scope.
Infix "*" := Tmult : romega_scope.
Infix "-" := Tminus : romega_scope.
Notation "- x" := (Topp x) : romega_scope.
Notation "[ x ]" := (Tvar x) (at level 0) : romega_scope.

(* \subsubsection{Definition of reified goals} *)

(* Very restricted definition of handled predicates that should be extended
   to cover a wider set of operations.
   Taking care of negations and disequations require solving more than a
   goal in parallel. This is a major improvement over previous versions. *)

Inductive proposition : Set :=
  | EqTerm : term -> term -> proposition (* equality between terms *)
  | LeqTerm : term -> term -> proposition (* less or equal on terms *)
  | TrueTerm : proposition (* true *)
  | FalseTerm : proposition (* false *)
  | Tnot : proposition -> proposition (* negation *)
  | GeqTerm : term -> term -> proposition
  | GtTerm : term -> term -> proposition
  | LtTerm : term -> term -> proposition
  | NeqTerm : term -> term -> proposition
  | Tor : proposition -> proposition -> proposition
  | Tand : proposition -> proposition -> proposition
  | Timp : proposition -> proposition -> proposition
  | Tprop : nat -> proposition.

(* Definition of goals as a list of hypothesis *)
Notation hyps := (list proposition).

(* Definition of lists of subgoals  (set of open goals) *)
Notation lhyps := (list hyps).

(* a single goal packed in a subgoal list *)
Notation singleton := (fun a : hyps => a :: nil).

(* an absurd goal *)
Definition absurd := FalseTerm :: nil.

(* \subsubsection{Traces for merging equations}
   This inductive type describes how the monomial of two equations should be
   merged when the equations are added.

   For [F_equal], both equations have the same head variable and coefficient
   must be added, furthermore if coefficients are opposite, [F_cancel] should
   be used to collapse the term. [F_left] and [F_right] indicate which monomial
   should be put first in the result *)

Inductive t_fusion : Set :=
  | F_equal : t_fusion
  | F_cancel : t_fusion
  | F_left : t_fusion
  | F_right : t_fusion.

(* \subsubsection{Rewriting steps to normalize terms} *)
Inductive step : Set :=
  (* apply the rewriting steps to both subterms of an operation *)
  | C_DO_BOTH : step -> step -> step
  (* apply the rewriting step to the first branch *)
  | C_LEFT : step -> step
  (* apply the rewriting step to the second branch *)
  | C_RIGHT : step -> step
  (* apply two steps consecutively to a term *)
  | C_SEQ : step -> step -> step
  (* empty step *)
  | C_NOP : step
  (* the following operations correspond to actual rewriting *)
  | C_OPP_PLUS : step
  | C_OPP_OPP : step
  | C_OPP_MULT_R : step
  | C_OPP_ONE : step
  (* This is a special step that reduces the term (computation) *)
  | C_REDUCE : step
  | C_MULT_PLUS_DISTR : step
  | C_MULT_OPP_LEFT : step
  | C_MULT_ASSOC_R : step
  | C_PLUS_ASSOC_R : step
  | C_PLUS_ASSOC_L : step
  | C_PLUS_PERMUTE : step
  | C_PLUS_COMM : step
  | C_RED0 : step
  | C_RED1 : step
  | C_RED2 : step
  | C_RED3 : step
  | C_RED4 : step
  | C_RED5 : step
  | C_RED6 : step
  | C_MULT_ASSOC_REDUCED : step
  | C_MINUS : step
  | C_MULT_COMM : step.

(* \subsubsection{Omega steps} *)
(* The following inductive type describes steps as they can be found in
   the trace coming from the decision procedure Omega. *)

Inductive t_omega : Set :=
  (* n = 0 and n!= 0 *)
  | O_CONSTANT_NOT_NUL : nat -> t_omega
  | O_CONSTANT_NEG : nat -> t_omega
  (* division and approximation of an equation *)
  | O_DIV_APPROX : int -> int -> term -> nat -> t_omega -> nat -> t_omega
  (* no solution because no exact division *)
  | O_NOT_EXACT_DIVIDE : int -> int -> term -> nat -> nat -> t_omega
  (* exact division *)
  | O_EXACT_DIVIDE : int -> term -> nat -> t_omega -> nat -> t_omega
  | O_SUM : int -> nat -> int -> nat -> list t_fusion -> t_omega -> t_omega
  | O_CONTRADICTION : nat -> nat -> nat -> t_omega
  | O_MERGE_EQ : nat -> nat -> nat -> t_omega -> t_omega
  | O_SPLIT_INEQ : nat -> nat -> t_omega -> t_omega -> t_omega
  | O_CONSTANT_NUL : nat -> t_omega
  | O_NEGATE_CONTRADICT : nat -> nat -> t_omega
  | O_NEGATE_CONTRADICT_INV : nat -> nat -> nat -> t_omega
  | O_STATE : int -> step -> nat -> nat -> t_omega -> t_omega.

(* \subsubsection{Rules for normalizing the hypothesis} *)
(* These rules indicate how to normalize useful propositions
   of each useful hypothesis before the decomposition of hypothesis.
   The rules include the inversion phase for negation removal. *)

Inductive p_step : Set :=
  | P_LEFT : p_step -> p_step
  | P_RIGHT : p_step -> p_step
  | P_INVERT : step -> p_step
  | P_STEP : step -> p_step
  | P_NOP : p_step.

(* List of normalizations to perform : if the type [p_step] had a constructor
   that indicated visiting both left and right branches, we would be able to
   restrict ourselves to the case of only one normalization by hypothesis.
   And since all hypothesis are useful (otherwise they wouldn't be included),
   we would be able to replace [h_step] by a simple list. *)

Inductive h_step : Set :=
    pair_step : nat -> p_step -> h_step.

(* \subsubsection{Rules for decomposing the hypothesis} *)
(* This type allows navigation in the logical constructors that
   form the predicats of the hypothesis in order to decompose them.
   This allows in particular to extract one hypothesis from a
   conjunction with possibly the right level of negations. *)

Inductive direction : Set :=
  | D_left : direction
  | D_right : direction
  | D_mono : direction.

(* This type allows extracting useful components from hypothesis, either
   hypothesis generated by splitting a disjonction, or equations.
   The last constructor indicates how to solve the obtained system
   via the use of the trace type of Omega [t_omega] *)

Inductive e_step : Set :=
  | E_SPLIT : nat -> list direction -> e_step -> e_step -> e_step
  | E_EXTRACT : nat -> list direction -> e_step -> e_step
  | E_SOLVE : t_omega -> e_step.

(* \subsection{Efficient decidable equality} *)
(* For each reified data-type, we define an efficient equality test.
   It is not the one produced by [Decide Equality].

   Then we prove two theorem allowing elimination of such equalities :
   \begin{verbatim}
   (t1,t2: typ) (eq_typ t1 t2) = true -> t1 = t2.
   (t1,t2: typ) (eq_typ t1 t2) = false -> ~ t1 = t2.
   \end{verbatim} *)

(* \subsubsection{Reified terms} *)

Open Scope romega_scope.

Fixpoint eq_term (t1 t2 : term) {struct t2} : bool :=
  match t1, t2 with
  | Tint st1, Tint st2 => beq st1 st2
  | (st11 + st12), (st21 + st22) => eq_term st11 st21 && eq_term st12 st22
  | (st11 * st12), (st21 * st22) => eq_term st11 st21 && eq_term st12 st22
  | (st11 - st12), (st21 - st22) => eq_term st11 st21 && eq_term st12 st22
  | (- st1), (- st2) => eq_term st1 st2
  | [st1], [st2] => beq_nat st1 st2
  | _, _ => false
  end.

Close Scope romega_scope.

Theorem eq_term_true : forall t1 t2 : term, eq_term t1 t2 = true -> t1 = t2.
Proof.
 induction t1; destruct t2; simpl in *; try discriminate;
 (rewrite andb_true_iff; intros (H1,H2)) || intros H; f_equal;
 auto using beq_true, beq_nat_true.
Qed.

Theorem eq_term_refl : forall t0 : term, eq_term t0 t0 = true.
Proof.
 induction t0; simpl in *; try (apply andb_true_iff; split); trivial.
 - now apply beq_iff.
 - now apply beq_nat_true_iff.
Qed.

Ltac trivial_case := unfold not; intros; discriminate.

Theorem eq_term_false :
 forall t1 t2 : term, eq_term t1 t2 = false -> t1 <> t2.
Proof.
 intros t1 t2 H E. subst t2. now rewrite eq_term_refl in H.
Qed.

(* \subsubsection{Tactiques pour éliminer ces tests}

   Si on se contente de faire un [Case (eq_typ t1 t2)] on perd
   totalement dans chaque branche le fait que [t1=t2] ou [~t1=t2].

   Initialement, les développements avaient été réalisés avec les
   tests rendus par [Decide Equality], c'est à dire un test rendant
   des termes du type [{t1=t2}+{~t1=t2}]. Faire une élimination sur un
   tel test préserve bien l'information voulue mais calculatoirement de
   telles fonctions sont trop lentes. *)

(* Les tactiques définies si après se comportent exactement comme si on
   avait utilisé le test précédent et fait une elimination dessus. *)

Ltac elim_eq_term t1 t2 :=
  pattern (eq_term t1 t2); apply bool_eq_ind; intro Aux;
   [ generalize (eq_term_true t1 t2 Aux); clear Aux
   | generalize (eq_term_false t1 t2 Aux); clear Aux ].

Ltac elim_beq t1 t2 :=
  pattern (beq t1 t2); apply bool_eq_ind; intro Aux;
   [ generalize (beq_true t1 t2 Aux); clear Aux
   | generalize (beq_false t1 t2 Aux); clear Aux ].

Ltac elim_bgt t1 t2 :=
  pattern (bgt t1 t2); apply bool_eq_ind; intro Aux;
  [ generalize (bgt_true t1 t2 Aux); clear Aux
  | generalize (bgt_false t1 t2 Aux); clear Aux ].


(* \subsection{Interprétations}
   \subsubsection{Interprétation des termes dans Z} *)

Fixpoint interp_term (env : list int) (t : term) {struct t} : int :=
  match t with
  | Tint x => x
  | (t1 + t2)%term => interp_term env t1 + interp_term env t2
  | (t1 * t2)%term => interp_term env t1 * interp_term env t2
  | (t1 - t2)%term => interp_term env t1 - interp_term env t2
  | (- t)%term => - interp_term env t
  | [n]%term => nth n env 0
  end.

(* \subsubsection{Interprétation des prédicats} *)

Fixpoint interp_proposition (envp : list Prop) (env : list int)
 (p : proposition) {struct p} : Prop :=
  match p with
  | EqTerm t1 t2 => interp_term env t1 = interp_term env t2
  | LeqTerm t1 t2 => interp_term env t1 <= interp_term env t2
  | TrueTerm => True
  | FalseTerm => False
  | Tnot p' => ~ interp_proposition envp env p'
  | GeqTerm t1 t2 => interp_term env t1 >= interp_term env t2
  | GtTerm t1 t2 => interp_term env t1 > interp_term env t2
  | LtTerm t1 t2 => interp_term env t1 < interp_term env t2
  | NeqTerm t1 t2 => (interp_term env t1)<>(interp_term env t2)
  | Tor p1 p2 =>
      interp_proposition envp env p1 \/ interp_proposition envp env p2
  | Tand p1 p2 =>
      interp_proposition envp env p1 /\ interp_proposition envp env p2
  | Timp p1 p2 =>
      interp_proposition envp env p1 -> interp_proposition envp env p2
  | Tprop n => nth n envp True
  end.

(* \subsubsection{Inteprétation des listes d'hypothèses}
   \paragraph{Sous forme de conjonction}
   Interprétation sous forme d'une conjonction d'hypothèses plus faciles
   à manipuler individuellement *)

Fixpoint interp_hyps (envp : list Prop) (env : list int)
 (l : hyps) {struct l} : Prop :=
  match l with
  | nil => True
  | p' :: l' => interp_proposition envp env p' /\ interp_hyps envp env l'
  end.

(* \paragraph{sous forme de but}
   C'est cette interpétation que l'on utilise sur le but (car on utilise
   [Generalize] et qu'une conjonction est forcément lourde (répétition des
   types dans les conjonctions intermédiaires) *)

Fixpoint interp_goal_concl (c : proposition) (envp : list Prop)
 (env : list int) (l : hyps) {struct l} : Prop :=
  match l with
  | nil => interp_proposition envp env c
  | p' :: l' =>
      interp_proposition envp env p' -> interp_goal_concl c envp env l'
  end.

Notation interp_goal := (interp_goal_concl FalseTerm).

(* Les théorèmes qui suivent assurent la correspondance entre les deux
   interprétations. *)

Theorem goal_to_hyps :
 forall (envp : list Prop) (env : list int) (l : hyps),
 (interp_hyps envp env l -> False) -> interp_goal envp env l.
Proof.
 simple induction l;
 [ simpl; auto
 | simpl; intros a l1 H1 H2 H3; apply H1; intro H4; apply H2; auto ].
Qed.

Theorem hyps_to_goal :
 forall (envp : list Prop) (env : list int) (l : hyps),
 interp_goal envp env l -> interp_hyps envp env l -> False.
Proof.
 simple induction l; simpl; [ auto | intros; apply H; elim H1; auto ].
Qed.

(* \subsection{Manipulations sur les hypothèses} *)

(* \subsubsection{Définitions de base de stabilité pour la réflexion} *)
(* Une opération laisse un terme stable si l'égalité est préservée *)
Definition term_stable (f : term -> term) :=
  forall (e : list int) (t : term), interp_term e t = interp_term e (f t).

(* Une opération est valide sur une hypothèse, si l'hypothèse implique le
   résultat de l'opération. \emph{Attention : cela ne concerne que des
   opérations sur les hypothèses et non sur les buts (contravariance)}.
   On définit la validité pour une opération prenant une ou deux propositions
   en argument (cela suffit pour omega). *)

Definition valid1 (f : proposition -> proposition) :=
  forall (ep : list Prop) (e : list int) (p1 : proposition),
  interp_proposition ep e p1 -> interp_proposition ep e (f p1).

Definition valid2 (f : proposition -> proposition -> proposition) :=
  forall (ep : list Prop) (e : list int) (p1 p2 : proposition),
  interp_proposition ep e p1 ->
  interp_proposition ep e p2 -> interp_proposition ep e (f p1 p2).

(* Dans cette notion de validité, la fonction prend directement une
   liste de propositions et rend une nouvelle liste de proposition.
   On reste contravariant *)

Definition valid_hyps (f : hyps -> hyps) :=
  forall (ep : list Prop) (e : list int) (lp : hyps),
  interp_hyps ep e lp -> interp_hyps ep e (f lp).

(* Enfin ce théorème élimine la contravariance et nous ramène à une
   opération sur les buts *)

Theorem valid_goal :
  forall (ep : list Prop) (env : list int) (l : hyps) (a : hyps -> hyps),
  valid_hyps a -> interp_goal ep env (a l) -> interp_goal ep env l.
Proof.
 intros; simpl; apply goal_to_hyps; intro H1;
 apply (hyps_to_goal ep env (a l) H0); apply H; assumption.
Qed.

(* \subsubsection{Généralisation a des listes de buts (disjonctions)} *)


Fixpoint interp_list_hyps (envp : list Prop) (env : list int)
 (l : lhyps) {struct l} : Prop :=
  match l with
  | nil => False
  | h :: l' => interp_hyps envp env h \/ interp_list_hyps envp env l'
  end.

Fixpoint interp_list_goal (envp : list Prop) (env : list int)
 (l : lhyps) {struct l} : Prop :=
  match l with
  | nil => True
  | h :: l' => interp_goal envp env h /\ interp_list_goal envp env l'
  end.

Theorem list_goal_to_hyps :
 forall (envp : list Prop) (env : list int) (l : lhyps),
 (interp_list_hyps envp env l -> False) -> interp_list_goal envp env l.
Proof.
 simple induction l; simpl;
 [ auto
 | intros h1 l1 H H1; split;
    [ apply goal_to_hyps; intro H2; apply H1; auto
    | apply H; intro H2; apply H1; auto ] ].
Qed.

Theorem list_hyps_to_goal :
 forall (envp : list Prop) (env : list int) (l : lhyps),
 interp_list_goal envp env l -> interp_list_hyps envp env l -> False.
Proof.
 simple induction l; simpl;
 [ auto
 | intros h1 l1 H (H1, H2) H3; elim H3; intro H4;
    [ apply hyps_to_goal with (1 := H1); assumption | auto ] ].
Qed.

Definition valid_list_hyps (f : hyps -> lhyps) :=
  forall (ep : list Prop) (e : list int) (lp : hyps),
  interp_hyps ep e lp -> interp_list_hyps ep e (f lp).

Definition valid_list_goal (f : hyps -> lhyps) :=
  forall (ep : list Prop) (e : list int) (lp : hyps),
  interp_list_goal ep e (f lp) -> interp_goal ep e lp.

Theorem goal_valid :
 forall f : hyps -> lhyps, valid_list_hyps f -> valid_list_goal f.
Proof.
 unfold valid_list_goal; intros f H ep e lp H1; apply goal_to_hyps;
 intro H2; apply list_hyps_to_goal with (1 := H1);
 apply (H ep e lp); assumption.
Qed.

Theorem append_valid :
 forall (ep : list Prop) (e : list int) (l1 l2 : lhyps),
 interp_list_hyps ep e l1 \/ interp_list_hyps ep e l2 ->
 interp_list_hyps ep e (l1 ++ l2).
Proof.
 intros ep e; simple induction l1;
 [ simpl; intros l2 [H| H]; [ contradiction | trivial ]
 | simpl; intros h1 t1 HR l2 [[H| H]| H];
    [ auto
    | right; apply (HR l2); left; trivial
    | right; apply (HR l2); right; trivial ] ].

Qed.

(* \subsubsection{Opérateurs valides sur les hypothèses} *)

(* Extraire une hypothèse de la liste *)
Definition nth_hyps (n : nat) (l : hyps) := nth n l TrueTerm.
Unset Printing Notations.
Theorem nth_valid :
 forall (ep : list Prop) (e : list int) (i : nat) (l : hyps),
 interp_hyps ep e l -> interp_proposition ep e (nth_hyps i l).
Proof.
 unfold nth_hyps; simple induction i;
 [ simple induction l; simpl; [ auto | intros; elim H0; auto ]
 | intros n H; simple induction l;
    [ simpl; trivial
    | intros; simpl; apply H; elim H1; auto ] ].
Qed.

(* Appliquer une opération (valide) sur deux hypothèses extraites de
   la liste et ajouter le résultat à la liste. *)
Definition apply_oper_2 (i j : nat)
  (f : proposition -> proposition -> proposition) (l : hyps) :=
  f (nth_hyps i l) (nth_hyps j l) :: l.

Theorem apply_oper_2_valid :
 forall (i j : nat) (f : proposition -> proposition -> proposition),
 valid2 f -> valid_hyps (apply_oper_2 i j f).
Proof.
 intros i j f Hf; unfold apply_oper_2, valid_hyps; simpl;
 intros lp Hlp; split; [ apply Hf; apply nth_valid; assumption | assumption ].
Qed.

(* Modifier une hypothèse par application d'une opération valide *)

Fixpoint apply_oper_1 (i : nat) (f : proposition -> proposition)
 (l : hyps) {struct i} : hyps :=
  match l with
  | nil => nil (A:=proposition)
  | p :: l' =>
      match i with
      | O => f p :: l'
      | S j => p :: apply_oper_1 j f l'
      end
  end.

Theorem apply_oper_1_valid :
 forall (i : nat) (f : proposition -> proposition),
 valid1 f -> valid_hyps (apply_oper_1 i f).
Proof.
 unfold valid_hyps; intros i f Hf ep e; elim i;
 [ intro lp; case lp;
    [ simpl; trivial
    | simpl; intros p l' (H1, H2); split;
       [ apply Hf with (1 := H1) | assumption ] ]
 | intros n Hrec lp; case lp;
    [ simpl; auto
    | simpl; intros p l' (H1, H2); split;
       [ assumption | apply Hrec; assumption ] ] ].
Qed.

(* \subsubsection{Manipulations de termes} *)
(* Les fonctions suivantes permettent d'appliquer une fonction de
   réécriture sur un sous terme du terme principal. Avec la composition,
   cela permet de construire des réécritures complexes proches des
   tactiques de conversion *)

Definition apply_left (f : term -> term) (t : term) :=
  match t with
  | (x + y)%term => (f x + y)%term
  | (x * y)%term => (f x * y)%term
  | (- x)%term => (- f x)%term
  | x => x
  end.

Definition apply_right (f : term -> term) (t : term) :=
  match t with
  | (x + y)%term => (x + f y)%term
  | (x * y)%term => (x * f y)%term
  | x => x
  end.

Definition apply_both (f g : term -> term) (t : term) :=
  match t with
  | (x + y)%term => (f x + g y)%term
  | (x * y)%term => (f x * g y)%term
  | x => x
  end.

(* Les théorèmes suivants montrent la stabilité (conditionnée) des
   fonctions. *)

Theorem apply_left_stable :
 forall f : term -> term, term_stable f -> term_stable (apply_left f).
Proof.
 unfold term_stable; intros f H e t; case t; auto; simpl;
 intros; elim H; trivial.
Qed.

Theorem apply_right_stable :
 forall f : term -> term, term_stable f -> term_stable (apply_right f).
Proof.
 unfold term_stable; intros f H e t; case t; auto; simpl;
 intros t0 t1; elim H; trivial.
Qed.

Theorem apply_both_stable :
 forall f g : term -> term,
 term_stable f -> term_stable g -> term_stable (apply_both f g).
Proof.
 unfold term_stable; intros f g H1 H2 e t; case t; auto; simpl;
 intros t0 t1; elim H1; elim H2; trivial.
Qed.

Theorem compose_term_stable :
 forall f g : term -> term,
 term_stable f -> term_stable g -> term_stable (fun t : term => f (g t)).
Proof.
 unfold term_stable; intros f g Hf Hg e t; elim Hf; apply Hg.
Qed.

(* \subsection{Les règles de réécriture} *)
(* Chacune des règles de réécriture est accompagnée par sa preuve de
   stabilité. Toutes ces preuves ont la même forme : il faut analyser
   suivant la forme du terme (élimination de chaque Case). On a besoin d'une
   élimination uniquement dans les cas d'utilisation d'égalité décidable.

   Cette tactique itère la décomposition des Case. Elle est
   constituée de deux fonctions s'appelant mutuellement :
   \begin{itemize}
    \item une fonction d'enrobage qui lance la recherche sur le but,
    \item une fonction récursive qui décompose ce but. Quand elle a trouvé un
          Case, elle l'élimine.
   \end{itemize}
   Les motifs sur les cas sont très imparfaits et dans certains cas, il
   semble que cela ne marche pas. On aimerait plutot un motif de la
   forme [ Case (?1 :: T) of _ end ] permettant de s'assurer que l'on
   utilise le bon type.

   Chaque élimination introduit correctement exactement le nombre d'hypothèses
   nécessaires et conserve dans le cas d'une égalité la connaissance du
   résultat du test en faisant la réécriture. Pour un test de comparaison,
   on conserve simplement le résultat.

   Cette fonction déborde très largement la résolution des réécritures
   simples et fait une bonne partie des preuves des pas de Omega.
*)

(* \subsubsection{La tactique pour prouver la stabilité} *)

Ltac loop t :=
  match t with
  (* Global *)
  | (?X1 = ?X2) => loop X1 || loop X2
  | (_ -> ?X1) => loop X1
  (* Interpretations *)
  | (interp_hyps _ _ ?X1) => loop X1
  | (interp_list_hyps _ _ ?X1) => loop X1
  | (interp_proposition _ _ ?X1) => loop X1
  | (interp_term _ ?X1) => loop X1
  (* Propositions *)
  | (EqTerm ?X1 ?X2) => loop X1 || loop X2
  | (LeqTerm ?X1 ?X2) => loop X1 || loop X2
  (* Termes *)
  | (?X1 + ?X2)%term => loop X1 || loop X2
  | (?X1 - ?X2)%term => loop X1 || loop X2
  | (?X1 * ?X2)%term => loop X1 || loop X2
  | (- ?X1)%term => loop X1
  | (Tint ?X1) => loop X1
  (* Eliminations *)
  | match ?X1 with
    | EqTerm x x0 => _
    | LeqTerm x x0 => _
    | TrueTerm => _
    | FalseTerm => _
    | Tnot x => _
    | GeqTerm x x0 => _
    | GtTerm x x0 => _
    | LtTerm x x0 => _
    | NeqTerm x x0 => _
    | Tor x x0 => _
    | Tand x x0 => _
    | Timp x x0 => _
    | Tprop x => _
    end => destruct X1; auto; Simplify
  | match ?X1 with
    | Tint x => _
    | (x + x0)%term => _
    | (x * x0)%term => _
    | (x - x0)%term => _
    | (- x)%term => _
    | [x]%term => _
    end => destruct X1; auto; Simplify
  | (if beq ?X1 ?X2 then _ else _) =>
      let H := fresh "H" in
      elim_beq X1 X2; intro H; try (rewrite H in *; clear H);
       simpl; auto; Simplify
  | (if bgt ?X1 ?X2 then _ else _) =>
      let H := fresh "H" in
      elim_bgt X1 X2; intro H; simpl; auto; Simplify
  | (if eq_term ?X1 ?X2 then _ else _) =>
      let H := fresh "H" in
      elim_eq_term X1 X2; intro H; try (rewrite H in *; clear H);
       simpl; auto; Simplify
  | (if _ && _ then _ else _) => rewrite andb_if; Simplify
  | (if negb _ then _ else _) => rewrite negb_if; Simplify
  | _ => fail
  end

with Simplify := match goal with
  |  |- ?X1 => try loop X1
  | _ => idtac
  end.

Ltac prove_stable x th :=
  match constr:x with
  | ?X1 =>
      unfold term_stable, X1; intros; Simplify; simpl;
       apply th
  end.

(* \subsubsection{Les règles elle mêmes} *)
Definition Tplus_assoc_l (t : term) :=
  match t with
  | (n + (m + p))%term => (n + m + p)%term
  | _ => t
  end.

Theorem Tplus_assoc_l_stable : term_stable Tplus_assoc_l.
Proof.
 prove_stable Tplus_assoc_l (ring.(Radd_assoc)).
Qed.

Definition Tplus_assoc_r (t : term) :=
  match t with
  | (n + m + p)%term => (n + (m + p))%term
  | _ => t
  end.

Theorem Tplus_assoc_r_stable : term_stable Tplus_assoc_r.
Proof.
 prove_stable Tplus_assoc_r plus_assoc_reverse.
Qed.

Definition Tmult_assoc_r (t : term) :=
  match t with
  | (n * m * p)%term => (n * (m * p))%term
  | _ => t
  end.

Theorem Tmult_assoc_r_stable : term_stable Tmult_assoc_r.
Proof.
 prove_stable Tmult_assoc_r mult_assoc_reverse.
Qed.

Definition Tplus_permute (t : term) :=
  match t with
  | (n + (m + p))%term => (m + (n + p))%term
  | _ => t
  end.

Theorem Tplus_permute_stable : term_stable Tplus_permute.
Proof.
 prove_stable Tplus_permute plus_permute.
Qed.

Definition Tplus_comm (t : term) :=
  match t with
  | (x + y)%term => (y + x)%term
  | _ => t
  end.

Theorem Tplus_comm_stable : term_stable Tplus_comm.
Proof.
 prove_stable Tplus_comm plus_comm.
Qed.

Definition Tmult_comm (t : term) :=
  match t with
  | (x * y)%term => (y * x)%term
  | _ => t
  end.

Theorem Tmult_comm_stable : term_stable Tmult_comm.
Proof.
 prove_stable Tmult_comm mult_comm.
Qed.

Definition T_OMEGA10 (t : term) :=
  match t with
  | ((v * Tint c1 + l1) * Tint k1 + (v' * Tint c2 + l2) * Tint k2)%term =>
      if eq_term v v'
      then (v * Tint (c1 * k1 + c2 * k2)%I + (l1 * Tint k1 + l2 * Tint k2))%term
      else t
  | _ => t
  end.

Theorem T_OMEGA10_stable : term_stable T_OMEGA10.
Proof.
 prove_stable T_OMEGA10 OMEGA10.
Qed.

Definition T_OMEGA11 (t : term) :=
  match t with
  | ((v1 * Tint c1 + l1) * Tint k1 + l2)%term =>
      (v1 * Tint (c1 * k1) + (l1 * Tint k1 + l2))%term
  | _ => t
  end.

Theorem T_OMEGA11_stable : term_stable T_OMEGA11.
Proof.
 prove_stable T_OMEGA11 OMEGA11.
Qed.

Definition T_OMEGA12 (t : term) :=
  match t with
  | (l1 + (v2 * Tint c2 + l2) * Tint k2)%term =>
      (v2 * Tint (c2 * k2) + (l1 + l2 * Tint k2))%term
  | _ => t
  end.

Theorem T_OMEGA12_stable : term_stable T_OMEGA12.
Proof.
 prove_stable T_OMEGA12 OMEGA12.
Qed.

Definition T_OMEGA13 (t : term) :=
  match t with
  | (v * Tint x + l1 + (v' * Tint x' + l2))%term =>
      if eq_term v v' && beq x (-x')
      then (l1+l2)%term
      else t
  | _ => t
  end.

Theorem T_OMEGA13_stable : term_stable T_OMEGA13.
Proof.
 unfold term_stable, T_OMEGA13; intros; Simplify; simpl;
 apply OMEGA13.
Qed.

Definition T_OMEGA15 (t : term) :=
  match t with
  | (v * Tint c1 + l1 + (v' * Tint c2 + l2) * Tint k2)%term =>
      if eq_term v v'
      then (v * Tint (c1 + c2 * k2)%I + (l1 + l2 * Tint k2))%term
      else t
  | _ => t
  end.

Theorem T_OMEGA15_stable : term_stable T_OMEGA15.
Proof.
 prove_stable T_OMEGA15 OMEGA15.
Qed.

Definition T_OMEGA16 (t : term) :=
  match t with
  | ((v * Tint c + l) * Tint k)%term => (v * Tint (c * k) + l * Tint k)%term
  | _ => t
  end.


Theorem T_OMEGA16_stable : term_stable T_OMEGA16.
Proof.
 prove_stable T_OMEGA16 OMEGA16.
Qed.

Definition Tred_factor5 (t : term) :=
  match t with
  | (x * Tint c + y)%term => if beq c 0 then y else t
  | _ => t
  end.

Theorem Tred_factor5_stable : term_stable Tred_factor5.
Proof.
 prove_stable Tred_factor5 red_factor5.
Qed.

Definition Topp_plus (t : term) :=
  match t with
  | (- (x + y))%term => (- x + - y)%term
  | _ => t
  end.

Theorem Topp_plus_stable : term_stable Topp_plus.
Proof.
 prove_stable Topp_plus opp_plus_distr.
Qed.


Definition Topp_opp (t : term) :=
  match t with
  | (- - x)%term => x
  | _ => t
  end.

Theorem Topp_opp_stable : term_stable Topp_opp.
Proof.
 prove_stable Topp_opp opp_involutive.
Qed.

Definition Topp_mult_r (t : term) :=
  match t with
  | (- (x * Tint k))%term => (x * Tint (- k))%term
  | _ => t
  end.

Theorem Topp_mult_r_stable : term_stable Topp_mult_r.
Proof.
 prove_stable Topp_mult_r opp_mult_distr_r.
Qed.

Definition Topp_one (t : term) :=
  match t with
  | (- x)%term => (x * Tint (-(1)))%term
  | _ => t
  end.

Theorem Topp_one_stable : term_stable Topp_one.
Proof.
 prove_stable Topp_one opp_eq_mult_neg_1.
Qed.

Definition Tmult_plus_distr (t : term) :=
  match t with
  | ((n + m) * p)%term => (n * p + m * p)%term
  | _ => t
  end.

Theorem Tmult_plus_distr_stable : term_stable Tmult_plus_distr.
Proof.
 prove_stable Tmult_plus_distr mult_plus_distr_r.
Qed.

Definition Tmult_opp_left (t : term) :=
  match t with
  | (- x * Tint y)%term => (x * Tint (- y))%term
  | _ => t
  end.

Theorem Tmult_opp_left_stable : term_stable Tmult_opp_left.
Proof.
 prove_stable Tmult_opp_left mult_opp_comm.
Qed.

Definition Tmult_assoc_reduced (t : term) :=
  match t with
  | (n * Tint m * Tint p)%term => (n * Tint (m * p))%term
  | _ => t
  end.

Theorem Tmult_assoc_reduced_stable : term_stable Tmult_assoc_reduced.
Proof.
 prove_stable Tmult_assoc_reduced mult_assoc_reverse.
Qed.

Definition Tred_factor0 (t : term) := (t * Tint 1)%term.

Theorem Tred_factor0_stable : term_stable Tred_factor0.
Proof.
 prove_stable Tred_factor0 red_factor0.
Qed.

Definition Tred_factor1 (t : term) :=
  match t with
  | (x + y)%term =>
      if eq_term x y
      then (x * Tint 2)%term
      else t
  | _ => t
  end.

Theorem Tred_factor1_stable : term_stable Tred_factor1.
Proof.
 prove_stable Tred_factor1 red_factor1.
Qed.

Definition Tred_factor2 (t : term) :=
  match t with
  | (x + y * Tint k)%term =>
      if eq_term x y
      then (x * Tint (1 + k))%term
      else t
  | _ => t
  end.

Theorem Tred_factor2_stable : term_stable Tred_factor2.
Proof.
 prove_stable Tred_factor2 red_factor2.
Qed.

Definition Tred_factor3 (t : term) :=
  match t with
  | (x * Tint k + y)%term =>
      if eq_term x y
      then (x * Tint (1 + k))%term
      else t
  | _ => t
  end.

Theorem Tred_factor3_stable : term_stable Tred_factor3.
Proof.
 prove_stable Tred_factor3 red_factor3.
Qed.


Definition Tred_factor4 (t : term) :=
  match t with
  | (x * Tint k1 + y * Tint k2)%term =>
      if eq_term x y
      then (x * Tint (k1 + k2))%term
      else t
  | _ => t
  end.

Theorem Tred_factor4_stable : term_stable Tred_factor4.
Proof.
 prove_stable Tred_factor4 red_factor4.
Qed.

Definition Tred_factor6 (t : term) := (t + Tint 0)%term.

Theorem Tred_factor6_stable : term_stable Tred_factor6.
Proof.
 prove_stable Tred_factor6 red_factor6.
Qed.

Definition Tminus_def (t : term) :=
  match t with
  | (x - y)%term => (x + - y)%term
  | _ => t
  end.

Theorem Tminus_def_stable : term_stable Tminus_def.
Proof.
 prove_stable Tminus_def minus_def.
Qed.

(* \subsection{Fonctions de réécriture complexes} *)

(* \subsubsection{Fonction de réduction} *)
(* Cette fonction réduit un terme dont la forme normale est un entier. Il
   suffit pour cela d'échanger le constructeur [Tint] avec les opérateurs
   réifiés. La réduction est ``gratuite''.  *)

Fixpoint reduce (t : term) : term :=
  match t with
  | (x + y)%term =>
      match reduce x with
      | Tint x' =>
          match reduce y with
          | Tint y' => Tint (x' + y')
          | y' => (Tint x' + y')%term
          end
      | x' => (x' + reduce y)%term
      end
  | (x * y)%term =>
      match reduce x with
      | Tint x' =>
          match reduce y with
          | Tint y' => Tint (x' * y')
          | y' => (Tint x' * y')%term
          end
      | x' => (x' * reduce y)%term
      end
  | (x - y)%term =>
      match reduce x with
      | Tint x' =>
          match reduce y with
          | Tint y' => Tint (x' - y')
          | y' => (Tint x' - y')%term
          end
      | x' => (x' - reduce y)%term
      end
  | (- x)%term =>
      match reduce x with
      | Tint x' => Tint (- x')
      | x' => (- x')%term
      end
  | _ => t
  end.

Theorem reduce_stable : term_stable reduce.
Proof.
 unfold term_stable; intros e t; elim t; auto;
 try
  (intros t0 H0 t1 H1; simpl; rewrite H0; rewrite H1;
    (case (reduce t0);
      [ intro z0; case (reduce t1); intros; auto
      | intros; auto
      | intros; auto
      | intros; auto
      | intros; auto
      | intros; auto ])); intros t0 H0; simpl;
 rewrite H0; case (reduce t0); intros; auto.
Qed.

(* \subsubsection{Fusions}
    \paragraph{Fusion de deux équations} *)
(* On donne une somme de deux équations qui sont supposées normalisées.
   Cette fonction prend une trace de fusion en argument et transforme
   le terme en une équation normalisée. C'est une version très simplifiée
   du moteur de réécriture [rewrite]. *)

Fixpoint fusion (trace : list t_fusion) (t : term) {struct trace} : term :=
  match trace with
  | nil => reduce t
  | step :: trace' =>
      match step with
      | F_equal => apply_right (fusion trace') (T_OMEGA10 t)
      | F_cancel => fusion trace' (Tred_factor5 (T_OMEGA10 t))
      | F_left => apply_right (fusion trace') (T_OMEGA11 t)
      | F_right => apply_right (fusion trace') (T_OMEGA12 t)
      end
  end.

Theorem fusion_stable : forall trace : list t_fusion, term_stable (fusion trace).
Proof.
 simple induction trace; simpl;
 [ exact reduce_stable
 | intros stp l H; case stp;
    [ apply compose_term_stable;
       [ apply apply_right_stable; assumption | exact T_OMEGA10_stable ]
    | unfold term_stable; intros e t1; rewrite T_OMEGA10_stable;
       rewrite Tred_factor5_stable; apply H
    | apply compose_term_stable;
       [ apply apply_right_stable; assumption | exact T_OMEGA11_stable ]
    | apply compose_term_stable;
       [ apply apply_right_stable; assumption | exact T_OMEGA12_stable ] ] ].
Qed.

(* \paragraph{Fusion de deux équations dont une sans coefficient} *)

Definition fusion_right (trace : list t_fusion) (t : term) : term :=
  match trace with
  | nil => reduce t (* Il faut mettre un compute *)
  | step :: trace' =>
      match step with
      | F_equal => apply_right (fusion trace') (T_OMEGA15 t)
      | F_cancel => fusion trace' (Tred_factor5 (T_OMEGA15 t))
      | F_left => apply_right (fusion trace') (Tplus_assoc_r t)
      | F_right => apply_right (fusion trace') (T_OMEGA12 t)
      end
  end.

(* \paragraph{Fusion avec annihilation} *)
(* Normalement le résultat est une constante *)

Fixpoint fusion_cancel (trace : nat) (t : term) {struct trace} : term :=
  match trace with
  | O => reduce t
  | S trace' => fusion_cancel trace' (T_OMEGA13 t)
  end.

Theorem fusion_cancel_stable : forall t : nat, term_stable (fusion_cancel t).
Proof.
 unfold term_stable, fusion_cancel; intros trace e; elim trace;
 [ exact (reduce_stable e)
 | intros n H t; elim H; exact (T_OMEGA13_stable e t) ].
Qed.

(* \subsubsection{Opérations affines sur une équation} *)
(* \paragraph{Multiplication scalaire et somme d'une constante} *)

Fixpoint scalar_norm_add (trace : nat) (t : term) {struct trace} : term :=
  match trace with
  | O => reduce t
  | S trace' => apply_right (scalar_norm_add trace') (T_OMEGA11 t)
  end.

Theorem scalar_norm_add_stable :
 forall t : nat, term_stable (scalar_norm_add t).
Proof.
 unfold term_stable, scalar_norm_add; intros trace; elim trace;
 [ exact reduce_stable
 | intros n H e t; elim apply_right_stable;
    [ exact (T_OMEGA11_stable e t) | exact H ] ].
Qed.

(* \paragraph{Multiplication scalaire} *)
Fixpoint scalar_norm (trace : nat) (t : term) {struct trace} : term :=
  match trace with
  | O => reduce t
  | S trace' => apply_right (scalar_norm trace') (T_OMEGA16 t)
  end.

Theorem scalar_norm_stable : forall t : nat, term_stable (scalar_norm t).
Proof.
 unfold term_stable, scalar_norm; intros trace; elim trace;
 [ exact reduce_stable
 | intros n H e t; elim apply_right_stable;
    [ exact (T_OMEGA16_stable e t) | exact H ] ].
Qed.

(* \paragraph{Somme d'une constante} *)
Fixpoint add_norm (trace : nat) (t : term) {struct trace} : term :=
  match trace with
  | O => reduce t
  | S trace' => apply_right (add_norm trace') (Tplus_assoc_r t)
  end.

Theorem add_norm_stable : forall t : nat, term_stable (add_norm t).
Proof.
 unfold term_stable, add_norm; intros trace; elim trace;
 [ exact reduce_stable
 | intros n H e t; elim apply_right_stable;
    [ exact (Tplus_assoc_r_stable e t) | exact H ] ].
Qed.

(* \subsection{La fonction de normalisation des termes (moteur de réécriture)} *)


Fixpoint t_rewrite (s : step) : term -> term :=
  match s with
  | C_DO_BOTH s1 s2 => apply_both (t_rewrite s1) (t_rewrite s2)
  | C_LEFT s => apply_left (t_rewrite s)
  | C_RIGHT s => apply_right (t_rewrite s)
  | C_SEQ s1 s2 => fun t : term => t_rewrite s2 (t_rewrite s1 t)
  | C_NOP => fun t : term => t
  | C_OPP_PLUS => Topp_plus
  | C_OPP_OPP => Topp_opp
  | C_OPP_MULT_R => Topp_mult_r
  | C_OPP_ONE => Topp_one
  | C_REDUCE => reduce
  | C_MULT_PLUS_DISTR => Tmult_plus_distr
  | C_MULT_OPP_LEFT => Tmult_opp_left
  | C_MULT_ASSOC_R => Tmult_assoc_r
  | C_PLUS_ASSOC_R => Tplus_assoc_r
  | C_PLUS_ASSOC_L => Tplus_assoc_l
  | C_PLUS_PERMUTE => Tplus_permute
  | C_PLUS_COMM => Tplus_comm
  | C_RED0 => Tred_factor0
  | C_RED1 => Tred_factor1
  | C_RED2 => Tred_factor2
  | C_RED3 => Tred_factor3
  | C_RED4 => Tred_factor4
  | C_RED5 => Tred_factor5
  | C_RED6 => Tred_factor6
  | C_MULT_ASSOC_REDUCED => Tmult_assoc_reduced
  | C_MINUS => Tminus_def
  | C_MULT_COMM => Tmult_comm
  end.

Theorem t_rewrite_stable : forall s : step, term_stable (t_rewrite s).
Proof.
 simple induction s; simpl;
 [ intros; apply apply_both_stable; auto
 | intros; apply apply_left_stable; auto
 | intros; apply apply_right_stable; auto
 | unfold term_stable; intros; elim H0; apply H
 | unfold term_stable; auto
 | exact Topp_plus_stable
 | exact Topp_opp_stable
 | exact Topp_mult_r_stable
 | exact Topp_one_stable
 | exact reduce_stable
 | exact Tmult_plus_distr_stable
 | exact Tmult_opp_left_stable
 | exact Tmult_assoc_r_stable
 | exact Tplus_assoc_r_stable
 | exact Tplus_assoc_l_stable
 | exact Tplus_permute_stable
 | exact Tplus_comm_stable
 | exact Tred_factor0_stable
 | exact Tred_factor1_stable
 | exact Tred_factor2_stable
 | exact Tred_factor3_stable
 | exact Tred_factor4_stable
 | exact Tred_factor5_stable
 | exact Tred_factor6_stable
 | exact Tmult_assoc_reduced_stable
 | exact Tminus_def_stable
 | exact Tmult_comm_stable ].
Qed.

(* \subsection{tactiques de résolution d'un but omega normalisé}
   Trace de la procédure
\subsubsection{Tactiques générant une contradiction}
\paragraph{[O_CONSTANT_NOT_NUL]} *)

Definition constant_not_nul (i : nat) (h : hyps) :=
  match nth_hyps i h with
  | EqTerm (Tint Nul) (Tint n) =>
      if beq n Nul then h else absurd
  | _ => h
  end.

Theorem constant_not_nul_valid :
 forall i : nat, valid_hyps (constant_not_nul i).
Proof.
 unfold valid_hyps, constant_not_nul; intros i ep e lp H.
 generalize (nth_valid ep e i lp H); Simplify.
Qed.

(* \paragraph{[O_CONSTANT_NEG]} *)

Definition constant_neg (i : nat) (h : hyps) :=
  match nth_hyps i h with
  | LeqTerm (Tint Nul) (Tint Neg) =>
     if bgt Nul Neg then absurd else h
  | _ => h
  end.

Theorem constant_neg_valid : forall i : nat, valid_hyps (constant_neg i).
Proof.
 unfold valid_hyps, constant_neg; intros;
 generalize (nth_valid ep e i lp); Simplify; simpl.
 rewrite gt_lt_iff in H0; rewrite le_lt_iff; intuition.
Qed.

(* \paragraph{[NOT_EXACT_DIVIDE]} *)
Definition not_exact_divide (k1 k2 : int) (body : term)
  (t i : nat) (l : hyps) :=
  match nth_hyps i l with
  | EqTerm (Tint Nul) b =>
      if beq Nul 0 &&
         eq_term (scalar_norm_add t (body * Tint k1 + Tint k2)%term) b &&
         bgt k2 0 &&
         bgt k1 k2
      then absurd
      else l
  | _ => l
  end.

Theorem not_exact_divide_valid :
 forall (k1 k2 : int) (body : term) (t0 i : nat),
 valid_hyps (not_exact_divide k1 k2 body t0 i).
Proof.
 unfold valid_hyps, not_exact_divide; intros;
 generalize (nth_valid ep e i lp); Simplify.
 rewrite (scalar_norm_add_stable t0 e), <-H1.
 do 2 rewrite <- scalar_norm_add_stable; simpl in *; intros.
 absurd (interp_term e body * k1 + k2 = 0);
 [ now apply OMEGA4 | symmetry; auto ].
Qed.

(* \paragraph{[O_CONTRADICTION]} *)

Definition contradiction (t i j : nat) (l : hyps) :=
  match nth_hyps i l with
  | LeqTerm (Tint Nul) b1 =>
      match nth_hyps j l with
      | LeqTerm (Tint Nul') b2 =>
          match fusion_cancel t (b1 + b2)%term with
          | Tint k => if beq Nul 0 && beq Nul' 0 && bgt 0 k
                      then absurd
                      else l
          | _ => l
          end
      | _ => l
      end
  | _ => l
  end.

Theorem contradiction_valid :
 forall t i j : nat, valid_hyps (contradiction t i j).
Proof.
 unfold valid_hyps, contradiction; intros t i j ep e l H;
 generalize (nth_valid _ _ i _ H); generalize (nth_valid _ _ j _ H);
 case (nth_hyps i l); auto; intros t1 t2; case t1;
 auto; case (nth_hyps j l);
 auto; intros t3 t4; case t3; auto;
 simpl; intros z z' H1 H2;
 generalize (eq_refl (interp_term e (fusion_cancel t (t2 + t4)%term)));
 pattern (fusion_cancel t (t2 + t4)%term) at 2 3;
 case (fusion_cancel t (t2 + t4)%term); simpl;
 auto; intro k; elim (fusion_cancel_stable t); simpl.
 Simplify; intro H3.
 generalize (OMEGA2 _ _ H2 H1); rewrite H3.
 rewrite gt_lt_iff in H0; rewrite le_lt_iff; intuition.
Qed.

(* \paragraph{[O_NEGATE_CONTRADICT]} *)

Definition negate_contradict (i1 i2 : nat) (h : hyps) :=
  match nth_hyps i1 h with
  | EqTerm (Tint Nul) b1 =>
      match nth_hyps i2 h with
      | NeqTerm (Tint Nul') b2 =>
          if beq Nul 0 && beq Nul' 0 && eq_term b1 b2
          then absurd
          else h
      | _ => h
      end
  | NeqTerm (Tint Nul) b1 =>
      match nth_hyps i2 h with
      | EqTerm (Tint Nul') b2 =>
          if beq Nul 0 && beq Nul' 0 && eq_term b1 b2
          then absurd
          else h
      | _ => h
      end
  | _ => h
  end.

Definition negate_contradict_inv (t i1 i2 : nat) (h : hyps) :=
  match nth_hyps i1 h with
  | EqTerm (Tint Nul) b1 =>
      match nth_hyps i2 h with
      | NeqTerm (Tint Nul') b2 =>
          if beq Nul 0 && beq Nul' 0 &&
             eq_term b1 (scalar_norm t (b2 * Tint (-(1)))%term)
          then absurd
          else h
      | _ => h
      end
  | NeqTerm (Tint Nul) b1 =>
      match nth_hyps i2 h with
      | EqTerm (Tint Nul') b2 =>
          if beq Nul 0 && beq Nul' 0 &&
             eq_term b1 (scalar_norm t (b2 * Tint (-(1)))%term)
          then absurd
          else h
      | _ => h
      end
  | _ => h
  end.

Theorem negate_contradict_valid :
 forall i j : nat, valid_hyps (negate_contradict i j).
Proof.
 unfold valid_hyps, negate_contradict; intros i j ep e l H;
 generalize (nth_valid _ _ i _ H); generalize (nth_valid _ _ j _ H);
 case (nth_hyps i l); auto; intros t1 t2; case t1;
 auto; intros z; auto; case (nth_hyps j l);
 auto; intros t3 t4; case t3; auto; intros z';
 auto; simpl; intros H1 H2; Simplify.
Qed.

Theorem negate_contradict_inv_valid :
 forall t i j : nat, valid_hyps (negate_contradict_inv t i j).
Proof.
 unfold valid_hyps, negate_contradict_inv; intros t i j ep e l H;
 generalize (nth_valid _ _ i _ H); generalize (nth_valid _ _ j _ H);
 case (nth_hyps i l); auto; intros t1 t2; case t1;
 auto; intros z; auto; case (nth_hyps j l);
 auto; intros t3 t4; case t3; auto; intros z';
 auto; simpl; intros H1 H2; Simplify;
 [
 rewrite <- scalar_norm_stable in H2; simpl in *;
 elim (mult_integral (interp_term e t4) (-(1))); intuition;
 elim minus_one_neq_zero; auto
 |
 elim H2; clear H2;
 rewrite <- scalar_norm_stable; simpl in *;
 now rewrite <- H1, mult_0_l
 ].
Qed.

(* \subsubsection{Tactiques générant une nouvelle équation} *)
(* \paragraph{[O_SUM]}
 C'est une oper2 valide mais elle traite plusieurs cas à la fois (suivant
 les opérateurs de comparaison des deux arguments) d'où une
 preuve un peu compliquée. On utilise quelques lemmes qui sont des
 généralisations des théorèmes utilisés par OMEGA. *)

Definition sum (k1 k2 : int) (trace : list t_fusion)
  (prop1 prop2 : proposition) :=
  match prop1 with
  | EqTerm (Tint Null) b1 =>
      match prop2 with
      | EqTerm (Tint Null') b2 =>
          if beq Null 0 && beq Null' 0
          then EqTerm (Tint 0) (fusion trace (b1 * Tint k1 + b2 * Tint k2)%term)
          else TrueTerm
      | LeqTerm (Tint Null') b2 =>
          if beq Null 0 && beq Null' 0 && bgt k2 0
          then LeqTerm (Tint 0)
                (fusion trace (b1 * Tint k1 + b2 * Tint k2)%term)
          else TrueTerm
      | _ => TrueTerm
      end
  | LeqTerm (Tint Null) b1 =>
      if beq Null 0 && bgt k1 0
      then match prop2 with
          | EqTerm (Tint Null') b2 =>
              if beq Null' 0 then
              LeqTerm (Tint 0)
                (fusion trace (b1 * Tint k1 + b2 * Tint k2)%term)
              else TrueTerm
          | LeqTerm (Tint Null') b2 =>
              if beq Null' 0 && bgt k2 0
              then LeqTerm (Tint 0)
                    (fusion trace (b1 * Tint k1 + b2 * Tint k2)%term)
              else TrueTerm
          | _ => TrueTerm
          end
      else TrueTerm
  | NeqTerm (Tint Null) b1 =>
      match prop2 with
      | EqTerm (Tint Null') b2 =>
          if beq Null 0 && beq Null' 0 && (negb (beq k1 0))
          then NeqTerm (Tint 0)
                 (fusion trace (b1 * Tint k1 + b2 * Tint k2)%term)
          else TrueTerm
      | _ => TrueTerm
      end
  | _ => TrueTerm
  end.


Theorem sum_valid :
 forall (k1 k2 : int) (t : list t_fusion), valid2 (sum k1 k2 t).
Proof.
 unfold valid2; intros k1 k2 t ep e p1 p2; unfold sum;
 Simplify; simpl; auto; try elim (fusion_stable t);
 simpl; intros;
 [ apply sum1; assumption
 | apply sum2; try assumption; apply sum4; assumption
 | rewrite plus_comm; apply sum2; try assumption; apply sum4; assumption
 | apply sum3; try assumption; apply sum4; assumption
 | apply sum5; auto ].
Qed.

(* \paragraph{[O_EXACT_DIVIDE]}
   c'est une oper1 valide mais on préfère une substitution a ce point la *)

Definition exact_divide (k : int) (body : term) (t : nat)
  (prop : proposition) :=
  match prop with
  | EqTerm (Tint Null) b =>
      if beq Null 0 &&
         eq_term (scalar_norm t (body * Tint k)%term) b &&
         negb (beq k 0)
      then EqTerm (Tint 0) body
      else TrueTerm
  | NeqTerm (Tint Null) b =>
      if beq Null 0 &&
         eq_term (scalar_norm t (body * Tint k)%term) b &&
         negb (beq k 0)
      then NeqTerm (Tint 0) body
      else TrueTerm
  | _ => TrueTerm
  end.

Theorem exact_divide_valid :
 forall (k : int) (t : term) (n : nat), valid1 (exact_divide k t n).
Proof.
 unfold valid1, exact_divide; intros k1 k2 t ep e p1;
 Simplify; simpl; auto; subst;
 rewrite <- scalar_norm_stable; simpl; intros;
 [ destruct (mult_integral _ _ (eq_sym H0)); intuition
 | contradict H0; rewrite <- H0, mult_0_l; auto
 ].
Qed.


(* \paragraph{[O_DIV_APPROX]}
  La preuve reprend le schéma de la précédente mais on
  est sur une opération de type valid1 et non sur une opération terminale. *)

Definition divide_and_approx (k1 k2 : int) (body : term)
  (t : nat) (prop : proposition) :=
  match prop with
  | LeqTerm (Tint Null) b =>
      if beq Null 0 &&
         eq_term (scalar_norm_add t (body * Tint k1 + Tint k2)%term) b &&
         bgt k1 0 &&
         bgt k1 k2
      then LeqTerm (Tint 0) body
      else prop
  | _ => prop
  end.

Theorem divide_and_approx_valid :
 forall (k1 k2 : int) (body : term) (t : nat),
 valid1 (divide_and_approx k1 k2 body t).
Proof.
 unfold valid1, divide_and_approx; intros k1 k2 body t ep e p1;
 Simplify; simpl; auto; subst;
 elim (scalar_norm_add_stable t e); simpl.
 intro H2; apply mult_le_approx with (3 := H2); assumption.
Qed.

(* \paragraph{[MERGE_EQ]} *)

Definition merge_eq (t : nat) (prop1 prop2 : proposition) :=
  match prop1 with
  | LeqTerm (Tint Null) b1 =>
      match prop2 with
      | LeqTerm (Tint Null') b2 =>
          if beq Null 0 && beq Null' 0 &&
             eq_term b1 (scalar_norm t (b2 * Tint (-(1)))%term)
          then EqTerm (Tint 0) b1
          else TrueTerm
      | _ => TrueTerm
      end
  | _ => TrueTerm
  end.

Theorem merge_eq_valid : forall n : nat, valid2 (merge_eq n).
Proof.
 unfold valid2, merge_eq; intros n ep e p1 p2; Simplify; simpl;
 auto; elim (scalar_norm_stable n e); simpl;
 intros; symmetry ; apply OMEGA8 with (2 := H0);
 [ assumption | elim opp_eq_mult_neg_1; trivial ].
Qed.



(* \paragraph{[O_CONSTANT_NUL]} *)

Definition constant_nul (i : nat) (h : hyps) :=
  match nth_hyps i h with
  | NeqTerm (Tint Null) (Tint Null') =>
      if beq Null Null' then absurd else h
  | _ => h
  end.

Theorem constant_nul_valid : forall i : nat, valid_hyps (constant_nul i).
Proof.
 unfold valid_hyps, constant_nul; intros;
 generalize (nth_valid ep e i lp); Simplify; simpl;
 intro H1; absurd (0 = 0); intuition.
Qed.

(* \paragraph{[O_STATE]} *)

Definition state (m : int) (s : step) (prop1 prop2 : proposition) :=
  match prop1 with
  | EqTerm (Tint Null) b1 =>
      match prop2 with
      | EqTerm b2 b3 =>
          if beq Null 0
          then EqTerm (Tint 0) (t_rewrite s (b1 + (- b3 + b2) * Tint m)%term)
          else TrueTerm
      | _ => TrueTerm
      end
  | _ => TrueTerm
  end.

Theorem state_valid : forall (m : int) (s : step), valid2 (state m s).
Proof.
 unfold valid2; intros m s ep e p1 p2; unfold state; Simplify;
 simpl; auto; elim (t_rewrite_stable s e); simpl;
 intros H1 H2; elim H1.
 now rewrite H2, plus_opp_l, plus_0_l, mult_0_l.
Qed.

(* \subsubsection{Tactiques générant plusieurs but}
   \paragraph{[O_SPLIT_INEQ]}
   La seule pour le moment (tant que la normalisation n'est pas réfléchie). *)

Definition split_ineq (i t : nat) (f1 f2 : hyps -> lhyps)
  (l : hyps) :=
  match nth_hyps i l with
  | NeqTerm (Tint Null) b1 =>
      if beq Null 0 then
      f1 (LeqTerm (Tint 0) (add_norm t (b1 + Tint (-(1)))%term) :: l) ++
      f2
        (LeqTerm (Tint 0)
           (scalar_norm_add t (b1 * Tint (-(1)) + Tint (-(1)))%term) :: l)
       else l :: nil
  | _ => l :: nil
  end.

Theorem split_ineq_valid :
 forall (i t : nat) (f1 f2 : hyps -> lhyps),
 valid_list_hyps f1 ->
 valid_list_hyps f2 -> valid_list_hyps (split_ineq i t f1 f2).
Proof.
 unfold valid_list_hyps, split_ineq; intros i t f1 f2 H1 H2 ep e lp H;
 generalize (nth_valid _ _ i _ H); case (nth_hyps i lp);
 simpl; auto; intros t1 t2; case t1; simpl;
 auto; intros z; simpl; auto; intro H3.
 Simplify.
 apply append_valid; elim (OMEGA19 (interp_term e t2));
 [ intro H4; left; apply H1; simpl; elim (add_norm_stable t);
    simpl; auto
 | intro H4; right; apply H2; simpl; elim (scalar_norm_add_stable t);
    simpl; auto
 | generalize H3; unfold not; intros E1 E2; apply E1;
    symmetry ; trivial ].
Qed.


(* \subsection{La fonction de rejeu de la trace} *)

Fixpoint execute_omega (t : t_omega) (l : hyps) {struct t} : lhyps :=
  match t with
  | O_CONSTANT_NOT_NUL n => singleton (constant_not_nul n l)
  | O_CONSTANT_NEG n => singleton (constant_neg n l)
  | O_DIV_APPROX k1 k2 body t cont n =>
      execute_omega cont (apply_oper_1 n (divide_and_approx k1 k2 body t) l)
  | O_NOT_EXACT_DIVIDE k1 k2 body t i =>
      singleton (not_exact_divide k1 k2 body t i l)
  | O_EXACT_DIVIDE k body t cont n =>
      execute_omega cont (apply_oper_1 n (exact_divide k body t) l)
  | O_SUM k1 i1 k2 i2 t cont =>
      execute_omega cont (apply_oper_2 i1 i2 (sum k1 k2 t) l)
  | O_CONTRADICTION t i j => singleton (contradiction t i j l)
  | O_MERGE_EQ t i1 i2 cont =>
      execute_omega cont (apply_oper_2 i1 i2 (merge_eq t) l)
  | O_SPLIT_INEQ t i cont1 cont2 =>
      split_ineq i t (execute_omega cont1) (execute_omega cont2) l
  | O_CONSTANT_NUL i => singleton (constant_nul i l)
  | O_NEGATE_CONTRADICT i j => singleton (negate_contradict i j l)
  | O_NEGATE_CONTRADICT_INV t i j =>
      singleton (negate_contradict_inv t i j l)
  | O_STATE m s i1 i2 cont =>
      execute_omega cont (apply_oper_2 i1 i2 (state m s) l)
  end.

Theorem omega_valid : forall tr : t_omega, valid_list_hyps (execute_omega tr).
Proof.
 simple induction tr; simpl;
 [ unfold valid_list_hyps; simpl; intros; left;
    apply (constant_not_nul_valid n ep e lp H)
 | unfold valid_list_hyps; simpl; intros; left;
    apply (constant_neg_valid n ep e lp H)
 | unfold valid_list_hyps, valid_hyps;
    intros k1 k2 body n t' Ht' m ep e lp H; apply Ht';
    apply
     (apply_oper_1_valid m (divide_and_approx k1 k2 body n)
        (divide_and_approx_valid k1 k2 body n) ep e lp H)
 | unfold valid_list_hyps; simpl; intros; left;
    apply (not_exact_divide_valid _ _ _ _ _ ep e lp H)
 | unfold valid_list_hyps, valid_hyps;
    intros k body n t' Ht' m ep e lp H; apply Ht';
    apply
     (apply_oper_1_valid m (exact_divide k body n)
        (exact_divide_valid k body n) ep e lp H)
 | unfold valid_list_hyps, valid_hyps;
    intros k1 i1 k2 i2 trace t' Ht' ep e lp H; apply Ht';
    apply
     (apply_oper_2_valid i1 i2 (sum k1 k2 trace) (sum_valid k1 k2 trace) ep e
        lp H)
 | unfold valid_list_hyps; simpl; intros; left;
    apply (contradiction_valid n n0 n1 ep e lp H)
 | unfold valid_list_hyps, valid_hyps;
    intros trace i1 i2 t' Ht' ep e lp H; apply Ht';
    apply
     (apply_oper_2_valid i1 i2 (merge_eq trace) (merge_eq_valid trace) ep e
        lp H)
 | intros t' i k1 H1 k2 H2; unfold valid_list_hyps; simpl;
    intros ep e lp H;
    apply
     (split_ineq_valid i t' (execute_omega k1) (execute_omega k2) H1 H2 ep e
        lp H)
 | unfold valid_list_hyps; simpl; intros i ep e lp H; left;
    apply (constant_nul_valid i ep e lp H)
 | unfold valid_list_hyps; simpl; intros i j ep e lp H; left;
    apply (negate_contradict_valid i j ep e lp H)
 | unfold valid_list_hyps; simpl; intros n i j ep e lp H;
    left; apply (negate_contradict_inv_valid n i j ep e lp H)
 | unfold valid_list_hyps, valid_hyps;
    intros m s i1 i2 t' Ht' ep e lp H; apply Ht';
    apply (apply_oper_2_valid i1 i2 (state m s) (state_valid m s) ep e lp H) ].
Qed.


(* \subsection{Les opérations globales sur le but}
   \subsubsection{Normalisation} *)

Definition move_right (s : step) (p : proposition) :=
  match p with
  | EqTerm t1 t2 => EqTerm (Tint 0) (t_rewrite s (t1 + - t2)%term)
  | LeqTerm t1 t2 => LeqTerm (Tint 0) (t_rewrite s (t2 + - t1)%term)
  | GeqTerm t1 t2 => LeqTerm (Tint 0) (t_rewrite s (t1 + - t2)%term)
  | LtTerm t1 t2 => LeqTerm (Tint 0) (t_rewrite s (t2 + Tint (-(1)) + - t1)%term)
  | GtTerm t1 t2 => LeqTerm (Tint 0) (t_rewrite s (t1 + Tint (-(1)) + - t2)%term)
  | NeqTerm t1 t2 => NeqTerm (Tint 0) (t_rewrite s (t1 + - t2)%term)
  | p => p
  end.

Theorem move_right_valid : forall s : step, valid1 (move_right s).
Proof.
 unfold valid1, move_right; intros s ep e p; Simplify; simpl;
 elim (t_rewrite_stable s e); simpl;
 [ symmetry ; apply egal_left; assumption
 | intro; apply le_left; assumption
 | intro; apply le_left; rewrite <- ge_le_iff; assumption
 | intro; apply lt_left; rewrite <- gt_lt_iff; assumption
 | intro; apply lt_left; assumption
 | intro; apply ne_left_2; assumption ].
Qed.

Definition do_normalize (i : nat) (s : step) := apply_oper_1 i (move_right s).

Theorem do_normalize_valid :
 forall (i : nat) (s : step), valid_hyps (do_normalize i s).
Proof.
 intros; unfold do_normalize; apply apply_oper_1_valid;
 apply move_right_valid.
Qed.

Fixpoint do_normalize_list (l : list step) (i : nat)
 (h : hyps) {struct l} : hyps :=
  match l with
  | s :: l' => do_normalize_list l' (S i) (do_normalize i s h)
  | nil => h
  end.

Theorem do_normalize_list_valid :
 forall (l : list step) (i : nat), valid_hyps (do_normalize_list l i).
Proof.
 simple induction l; simpl; unfold valid_hyps;
 [ auto
 | intros a l' Hl' i ep e lp H; unfold valid_hyps in Hl'; apply Hl';
    apply (do_normalize_valid i a ep e lp); assumption ].
Qed.

Theorem normalize_goal :
 forall (s : list step) (ep : list Prop) (env : list int) (l : hyps),
 interp_goal ep env (do_normalize_list s 0 l) -> interp_goal ep env l.
Proof.
 intros; apply valid_goal with (2 := H); apply do_normalize_list_valid.
Qed.

(* \subsubsection{Exécution de la trace} *)

Theorem execute_goal :
 forall (tr : t_omega) (ep : list Prop) (env : list int) (l : hyps),
 interp_list_goal ep env (execute_omega tr l) -> interp_goal ep env l.
Proof.
 intros; apply (goal_valid (execute_omega tr) (omega_valid tr) ep env l H).
Qed.


Theorem append_goal :
 forall (ep : list Prop) (e : list int) (l1 l2 : lhyps),
 interp_list_goal ep e l1 /\ interp_list_goal ep e l2 ->
 interp_list_goal ep e (l1 ++ l2).
Proof.
 intros ep e; simple induction l1;
 [ simpl; intros l2 (H1, H2); assumption
 | simpl; intros h1 t1 HR l2 ((H1, H2), H3); split; auto ].
Qed.

(* A simple decidability checker : if the proposition belongs to the
   simple grammar describe below then it is decidable. Proof is by
   induction and uses well known theorem about arithmetic and propositional
   calculus *)

Fixpoint decidability (p : proposition) : bool :=
  match p with
  | EqTerm _ _ => true
  | LeqTerm _ _ => true
  | GeqTerm _ _ => true
  | GtTerm _ _ => true
  | LtTerm _ _ => true
  | NeqTerm _ _ => true
  | FalseTerm => true
  | TrueTerm => true
  | Tnot t => decidability t
  | Tand t1 t2 => decidability t1 && decidability t2
  | Timp t1 t2 => decidability t1 && decidability t2
  | Tor t1 t2 => decidability t1 && decidability t2
  | Tprop _ => false
  end.

Theorem decidable_correct :
 forall (ep : list Prop) (e : list int) (p : proposition),
 decidability p = true -> decidable (interp_proposition ep e p).
Proof.
 simple induction p; simpl; intros;
 [ apply dec_eq
 | apply dec_le
 | left; auto
 | right; unfold not; auto
 | apply dec_not; auto
 | apply dec_ge
 | apply dec_gt
 | apply dec_lt
 | apply dec_ne
 | apply dec_or; elim andb_prop with (1 := H1); auto
 | apply dec_and; elim andb_prop with (1 := H1); auto
 | apply dec_imp; elim andb_prop with (1 := H1); auto
 | discriminate H ].
Qed.

(* An interpretation function for a complete goal with an explicit
   conclusion. We use an intermediate fixpoint. *)

Fixpoint interp_full_goal (envp : list Prop) (env : list int)
 (c : proposition) (l : hyps) {struct l} : Prop :=
  match l with
  | nil => interp_proposition envp env c
  | p' :: l' =>
      interp_proposition envp env p' -> interp_full_goal envp env c l'
  end.

Definition interp_full (ep : list Prop) (e : list int)
  (lc : hyps * proposition) : Prop :=
  match lc with
  | (l, c) => interp_full_goal ep e c l
  end.

(* Relates the interpretation of a complete goal with the interpretation
   of its hypothesis and conclusion *)

Theorem interp_full_false :
 forall (ep : list Prop) (e : list int) (l : hyps) (c : proposition),
 (interp_hyps ep e l -> interp_proposition ep e c) -> interp_full ep e (l, c).
Proof.
 simple induction l; unfold interp_full; simpl;
 [ auto | intros a l1 H1 c H2 H3; apply H1; auto ].
Qed.

(* Push the conclusion in the list of hypothesis using a double negation
   If the decidability cannot be "proven", then just forget about the
   conclusion (equivalent of replacing it with false) *)

Definition to_contradict (lc : hyps * proposition) :=
  match lc with
  | (l, c) => if decidability c then Tnot c :: l else l
  end.

(* The previous operation is valid in the sense that the new list of
   hypothesis implies the original goal *)

Theorem to_contradict_valid :
 forall (ep : list Prop) (e : list int) (lc : hyps * proposition),
 interp_goal ep e (to_contradict lc) -> interp_full ep e lc.
Proof.
 intros ep e lc; case lc; intros l c; simpl;
 pattern (decidability c); apply bool_eq_ind;
 [ simpl; intros H H1; apply interp_full_false; intros H2;
    apply not_not;
    [ apply decidable_correct; assumption
    | unfold not at 1; intro H3; apply hyps_to_goal with (2 := H2);
       auto ]
 | intros H1 H2; apply interp_full_false; intro H3;
    elim hyps_to_goal with (1 := H2); assumption ].
Qed.

(* [map_cons x l] adds [x] at the head of each list in [l] (which is a list
   of lists *)

Fixpoint map_cons (A : Set) (x : A) (l : list (list A)) {struct l} :
 list (list A) :=
  match l with
  | nil => nil
  | l :: ll => (x :: l) :: map_cons A x ll
  end.

(* This function breaks up a list of hypothesis in a list of simpler
   list of hypothesis that together implie the original one. The goal
   of all this is to transform the goal in a list of solvable problems.
   Note that :
	- we need a way to drive the analysis as some hypotheis may not
          require a split.
        - this procedure must be perfectly mimicked by the ML part otherwise
          hypothesis will get desynchronised and this will be a mess.
 *)

Fixpoint destructure_hyps (nn : nat) (ll : hyps) {struct nn} : lhyps :=
  match nn with
  | O => ll :: nil
  | S n =>
      match ll with
      | nil => nil :: nil
      | Tor p1 p2 :: l =>
          destructure_hyps n (p1 :: l) ++ destructure_hyps n (p2 :: l)
      | Tand p1 p2 :: l => destructure_hyps n (p1 :: p2 :: l)
      | Timp p1 p2 :: l =>
          if decidability p1
          then
           destructure_hyps n (Tnot p1 :: l) ++ destructure_hyps n (p2 :: l)
          else map_cons _ (Timp p1 p2) (destructure_hyps n l)
      | Tnot p :: l =>
          match p with
          | Tnot p1 =>
              if decidability p1
              then destructure_hyps n (p1 :: l)
              else map_cons _ (Tnot (Tnot p1)) (destructure_hyps n l)
          | Tor p1 p2 => destructure_hyps n (Tnot p1 :: Tnot p2 :: l)
          | Tand p1 p2 =>
              if decidability p1
              then
               destructure_hyps n (Tnot p1 :: l) ++
               destructure_hyps n (Tnot p2 :: l)
              else map_cons _ (Tnot p) (destructure_hyps n l)
          | _ => map_cons _ (Tnot p) (destructure_hyps n l)
          end
      | x :: l => map_cons _ x (destructure_hyps n l)
      end
  end.

Theorem map_cons_val :
 forall (ep : list Prop) (e : list int) (p : proposition) (l : lhyps),
 interp_proposition ep e p ->
 interp_list_hyps ep e l -> interp_list_hyps ep e (map_cons _ p l).
Proof.
 simple induction l; simpl; [ auto | intros; elim H1; intro H2; auto ].
Qed.

Hint Resolve map_cons_val append_valid decidable_correct.

Theorem destructure_hyps_valid :
 forall n : nat, valid_list_hyps (destructure_hyps n).
Proof.
 simple induction n;
 [ unfold valid_list_hyps; simpl; auto
 | unfold valid_list_hyps at 2; intros n1 H ep e lp; case lp;
    [ simpl; auto
    | intros p l; case p;
       try
        (simpl; intros; apply map_cons_val; simpl; elim H0;
          auto);
       [ intro p'; case p';
          try
           (simpl; intros; apply map_cons_val; simpl; elim H0;
             auto);
          [ simpl; intros p1 (H1, H2);
             pattern (decidability p1); apply bool_eq_ind;
             intro H3;
             [ apply H; simpl; split;
                [ apply not_not; auto | assumption ]
             | auto ]
          | simpl; intros p1 p2 (H1, H2); apply H; simpl;
             elim not_or with (1 := H1); auto
          | simpl; intros p1 p2 (H1, H2);
             pattern (decidability p1); apply bool_eq_ind;
             intro H3;
             [ apply append_valid; elim not_and with (2 := H1);
                [ intro; left; apply H; simpl; auto
                | intro; right; apply H; simpl; auto
                | auto ]
             | auto ] ]
       | simpl; intros p1 p2 (H1, H2); apply append_valid;
          (elim H1; intro H3; simpl; [ left | right ]);
          apply H; simpl; auto
       | simpl; intros; apply H; simpl; tauto
       | simpl; intros p1 p2 (H1, H2);
          pattern (decidability p1); apply bool_eq_ind;
          intro H3;
          [ apply append_valid; elim imp_simp with (2 := H1);
             [ intro H4; left; simpl; apply H; simpl; auto
             | intro H4; right; simpl; apply H; simpl; auto
             | auto ]
          | auto ] ] ] ].
Qed.

Definition prop_stable (f : proposition -> proposition) :=
  forall (ep : list Prop) (e : list int) (p : proposition),
  interp_proposition ep e p <-> interp_proposition ep e (f p).

Definition p_apply_left (f : proposition -> proposition)
  (p : proposition) :=
  match p with
  | Timp x y => Timp (f x) y
  | Tor x y => Tor (f x) y
  | Tand x y => Tand (f x) y
  | Tnot x => Tnot (f x)
  | x => x
  end.

Theorem p_apply_left_stable :
 forall f : proposition -> proposition,
 prop_stable f -> prop_stable (p_apply_left f).
Proof.
 unfold prop_stable; intros f H ep e p; split;
 (case p; simpl; auto; intros p1; elim (H ep e p1); tauto).
Qed.

Definition p_apply_right (f : proposition -> proposition)
  (p : proposition) :=
  match p with
  | Timp x y => Timp x (f y)
  | Tor x y => Tor x (f y)
  | Tand x y => Tand x (f y)
  | Tnot x => Tnot (f x)
  | x => x
  end.

Theorem p_apply_right_stable :
 forall f : proposition -> proposition,
 prop_stable f -> prop_stable (p_apply_right f).
Proof.
 unfold prop_stable; intros f H ep e p; split;
 (case p; simpl; auto;
   [ intros p1; elim (H ep e p1); tauto
   | intros p1 p2; elim (H ep e p2); tauto
   | intros p1 p2; elim (H ep e p2); tauto
   | intros p1 p2; elim (H ep e p2); tauto ]).
Qed.

Definition p_invert (f : proposition -> proposition)
  (p : proposition) :=
  match p with
  | EqTerm x y => Tnot (f (NeqTerm x y))
  | LeqTerm x y => Tnot (f (GtTerm x y))
  | GeqTerm x y => Tnot (f (LtTerm x y))
  | GtTerm x y => Tnot (f (LeqTerm x y))
  | LtTerm x y => Tnot (f (GeqTerm x y))
  | NeqTerm x y => Tnot (f (EqTerm x y))
  | x => x
  end.

Theorem p_invert_stable :
 forall f : proposition -> proposition,
 prop_stable f -> prop_stable (p_invert f).
Proof.
 unfold prop_stable; intros f H ep e p; split;
 (case p; simpl; auto;
   [ intros t1 t2; elim (H ep e (NeqTerm t1 t2)); simpl;
      generalize (dec_eq (interp_term e t1) (interp_term e t2));
      unfold decidable; tauto
   | intros t1 t2; elim (H ep e (GtTerm t1 t2)); simpl;
      generalize (dec_gt (interp_term e t1) (interp_term e t2));
      unfold decidable; rewrite le_lt_iff, <- gt_lt_iff; tauto
   | intros t1 t2; elim (H ep e (LtTerm t1 t2)); simpl;
      generalize (dec_lt (interp_term e t1) (interp_term e t2));
      unfold decidable; rewrite ge_le_iff, le_lt_iff; tauto
   | intros t1 t2; elim (H ep e (LeqTerm t1 t2)); simpl;
      generalize (dec_gt (interp_term e t1) (interp_term e t2));
      unfold decidable; repeat rewrite le_lt_iff;
      repeat rewrite gt_lt_iff; tauto
   | intros t1 t2; elim (H ep e (GeqTerm t1 t2)); simpl;
      generalize (dec_lt (interp_term e t1) (interp_term e t2));
      unfold decidable; repeat rewrite ge_le_iff;
      repeat rewrite le_lt_iff; tauto
   | intros t1 t2; elim (H ep e (EqTerm t1 t2)); simpl;
      generalize (dec_eq (interp_term e t1) (interp_term e t2));
      unfold decidable; tauto ]).
Qed.

Theorem move_right_stable : forall s : step, prop_stable (move_right s).
Proof.
 unfold move_right, prop_stable; intros s ep e p; split;
 [ Simplify; simpl; elim (t_rewrite_stable s e); simpl;
    [ symmetry ; apply egal_left; assumption
    | intro; apply le_left; assumption
    | intro; apply le_left; rewrite <- ge_le_iff; assumption
    | intro; apply lt_left; rewrite <- gt_lt_iff; assumption
    | intro; apply lt_left; assumption
    | intro; apply ne_left_2; assumption ]
 | case p; simpl; intros; auto; generalize H; elim (t_rewrite_stable s);
    simpl; intro H1;
    [ rewrite (plus_0_r_reverse (interp_term e t1)); rewrite H1;
       rewrite plus_permute; rewrite plus_opp_r;
       rewrite plus_0_r; trivial
    | apply (fun a b => plus_le_reg_r a b (- interp_term e t0));
       rewrite plus_opp_r; assumption
    | rewrite ge_le_iff;
       apply (fun a b => plus_le_reg_r a b (- interp_term e t1));
       rewrite plus_opp_r; assumption
    | rewrite gt_lt_iff; apply lt_left_inv; assumption
    | apply lt_left_inv; assumption
    | unfold not; intro H2; apply H1;
       rewrite H2; rewrite plus_opp_r; trivial ] ].
Qed.


Fixpoint p_rewrite (s : p_step) : proposition -> proposition :=
  match s with
  | P_LEFT s => p_apply_left (p_rewrite s)
  | P_RIGHT s => p_apply_right (p_rewrite s)
  | P_STEP s => move_right s
  | P_INVERT s => p_invert (move_right s)
  | P_NOP => fun p : proposition => p
  end.

Theorem p_rewrite_stable : forall s : p_step, prop_stable (p_rewrite s).
Proof.
 simple induction s; simpl;
 [ intros; apply p_apply_left_stable; trivial
 | intros; apply p_apply_right_stable; trivial
 | intros; apply p_invert_stable; apply move_right_stable
 | apply move_right_stable
 | unfold prop_stable; simpl; intros; split; auto ].
Qed.

Fixpoint normalize_hyps (l : list h_step) (lh : hyps) {struct l} : hyps :=
  match l with
  | nil => lh
  | pair_step i s :: r => normalize_hyps r (apply_oper_1 i (p_rewrite s) lh)
  end.

Theorem normalize_hyps_valid :
 forall l : list h_step, valid_hyps (normalize_hyps l).
Proof.
 simple induction l; unfold valid_hyps; simpl;
 [ auto
 | intros n_s r; case n_s; intros n s H ep e lp H1; apply H;
    apply apply_oper_1_valid;
    [ unfold valid1; intros ep1 e1 p1 H2;
       elim (p_rewrite_stable s ep1 e1 p1); auto
    | assumption ] ].
Qed.

Theorem normalize_hyps_goal :
 forall (s : list h_step) (ep : list Prop) (env : list int) (l : hyps),
 interp_goal ep env (normalize_hyps s l) -> interp_goal ep env l.
Proof.
 intros; apply valid_goal with (2 := H); apply normalize_hyps_valid.
Qed.

Fixpoint extract_hyp_pos (s : list direction) (p : proposition) {struct s} :
 proposition :=
  match s with
  | D_left :: l =>
      match p with
      | Tand x y => extract_hyp_pos l x
      | _ => p
      end
  | D_right :: l =>
      match p with
      | Tand x y => extract_hyp_pos l y
      | _ => p
      end
  | D_mono :: l => match p with
                   | Tnot x => extract_hyp_neg l x
                   | _ => p
                   end
  | _ => p
  end

 with extract_hyp_neg (s : list direction) (p : proposition) {struct s} :
 proposition :=
  match s with
  | D_left :: l =>
      match p with
      | Tor x y => extract_hyp_neg l x
      | Timp x y => if decidability x then extract_hyp_pos l x else Tnot p
      | _ => Tnot p
      end
  | D_right :: l =>
      match p with
      | Tor x y => extract_hyp_neg l y
      | Timp x y => extract_hyp_neg l y
      | _ => Tnot p
      end
  | D_mono :: l =>
      match p with
      | Tnot x => if decidability x then extract_hyp_pos l x else Tnot p
      | _ => Tnot p
      end
  | _ =>
      match p with
      | Tnot x => if decidability x then x else Tnot p
      | _ => Tnot p
      end
  end.

Definition co_valid1 (f : proposition -> proposition) :=
  forall (ep : list Prop) (e : list int) (p1 : proposition),
  interp_proposition ep e (Tnot p1) -> interp_proposition ep e (f p1).

Theorem extract_valid :
 forall s : list direction,
 valid1 (extract_hyp_pos s) /\ co_valid1 (extract_hyp_neg s).
Proof.
 unfold valid1, co_valid1; simple induction s;
 [ split;
    [ simpl; auto
    | intros ep e p1; case p1; simpl; auto; intro p;
       pattern (decidability p); apply bool_eq_ind;
       [ intro H; generalize (decidable_correct ep e p H);
          unfold decidable; tauto
       | simpl; auto ] ]
 | intros a s' (H1, H2); simpl in H2; split; intros ep e p; case a; auto;
    case p; auto; simpl; intros;
    (apply H1; tauto) ||
      (apply H2; tauto) ||
        (pattern (decidability p0); apply bool_eq_ind;
          [ intro H3; generalize (decidable_correct ep e p0 H3);
             unfold decidable; intro H4; apply H1;
             tauto
          | intro; tauto ]) ].
Qed.

Fixpoint decompose_solve (s : e_step) (h : hyps) {struct s} : lhyps :=
  match s with
  | E_SPLIT i dl s1 s2 =>
      match extract_hyp_pos dl (nth_hyps i h) with
      | Tor x y => decompose_solve s1 (x :: h) ++ decompose_solve s2 (y :: h)
      | Tnot (Tand x y) =>
          if decidability x
          then
           decompose_solve s1 (Tnot x :: h) ++
           decompose_solve s2 (Tnot y :: h)
          else h :: nil
      | Timp x y =>
          if decidability x then
            decompose_solve s1 (Tnot x :: h) ++ decompose_solve s2 (y :: h)
          else h::nil
      | _ => h :: nil
      end
  | E_EXTRACT i dl s1 =>
      decompose_solve s1 (extract_hyp_pos dl (nth_hyps i h) :: h)
  | E_SOLVE t => execute_omega t h
  end.

Theorem decompose_solve_valid :
 forall s : e_step, valid_list_goal (decompose_solve s).
Proof.
 intro s; apply goal_valid; unfold valid_list_hyps; elim s;
 simpl; intros;
 [ cut (interp_proposition ep e1 (extract_hyp_pos l (nth_hyps n lp)));
    [ case (extract_hyp_pos l (nth_hyps n lp)); simpl; auto;
       [ intro p; case p; simpl; auto; intros p1 p2 H2;
          pattern (decidability p1); apply bool_eq_ind;
          [ intro H3; generalize (decidable_correct ep e1 p1 H3); intro H4;
             apply append_valid; elim H4; intro H5;
             [ right; apply H0; simpl; tauto
             | left; apply H; simpl; tauto ]
          | simpl; auto ]
       | intros p1 p2 H2; apply append_valid; simpl; elim H2;
          [ intros H3; left; apply H; simpl; auto
          | intros H3; right; apply H0; simpl; auto ]
       | intros p1 p2 H2;
         pattern (decidability p1); apply bool_eq_ind;
          [ intro H3; generalize (decidable_correct ep e1 p1 H3); intro H4;
             apply append_valid; elim H4; intro H5;
             [ right; apply H0; simpl; tauto
             | left; apply H; simpl; tauto ]
          | simpl; auto ] ]
    | elim (extract_valid l); intros H2 H3; apply H2; apply nth_valid; auto ]
 | intros; apply H; simpl; split;
    [ elim (extract_valid l); intros H2 H3; apply H2; apply nth_valid; auto
    | auto ]
 | apply omega_valid with (1 := H) ].
Qed.

(* \subsection{La dernière étape qui élimine tous les séquents inutiles} *)

Definition valid_lhyps (f : lhyps -> lhyps) :=
  forall (ep : list Prop) (e : list int) (lp : lhyps),
  interp_list_hyps ep e lp -> interp_list_hyps ep e (f lp).

Fixpoint reduce_lhyps (lp : lhyps) : lhyps :=
  match lp with
  | (FalseTerm :: nil) :: lp' => reduce_lhyps lp'
  | x :: lp' => x :: reduce_lhyps lp'
  | nil => nil (A:=hyps)
  end.

Theorem reduce_lhyps_valid : valid_lhyps reduce_lhyps.
Proof.
 unfold valid_lhyps; intros ep e lp; elim lp;
 [ simpl; auto
 | intros a l HR; elim a;
    [ simpl; tauto
    | intros a1 l1; case l1; case a1; simpl; try tauto ] ].
Qed.

Theorem do_reduce_lhyps :
 forall (envp : list Prop) (env : list int) (l : lhyps),
 interp_list_goal envp env (reduce_lhyps l) -> interp_list_goal envp env l.
Proof.
 intros envp env l H; apply list_goal_to_hyps; intro H1;
 apply list_hyps_to_goal with (1 := H); apply reduce_lhyps_valid;
 assumption.
Qed.

Definition concl_to_hyp (p : proposition) :=
  if decidability p then Tnot p else TrueTerm.

Definition do_concl_to_hyp :
  forall (envp : list Prop) (env : list int) (c : proposition) (l : hyps),
  interp_goal envp env (concl_to_hyp c :: l) ->
  interp_goal_concl c envp env l.
Proof.
 simpl; intros envp env c l; induction l as [| a l Hrecl];
 [ simpl; unfold concl_to_hyp;
    pattern (decidability c); apply bool_eq_ind;
    [ intro H; generalize (decidable_correct envp env c H);
       unfold decidable; simpl; tauto
    | simpl; intros H1 H2; elim H2; trivial ]
 | simpl; tauto ].
Qed.

Definition omega_tactic (t1 : e_step) (t2 : list h_step)
  (c : proposition) (l : hyps) :=
  reduce_lhyps (decompose_solve t1 (normalize_hyps t2 (concl_to_hyp c :: l))).

Theorem do_omega :
 forall (t1 : e_step) (t2 : list h_step) (envp : list Prop)
   (env : list int) (c : proposition) (l : hyps),
 interp_list_goal envp env (omega_tactic t1 t2 c l) ->
 interp_goal_concl c envp env l.
Proof.
 unfold omega_tactic; intros; apply do_concl_to_hyp;
 apply (normalize_hyps_goal t2); apply (decompose_solve_valid t1);
 apply do_reduce_lhyps; assumption.
Qed.

End IntOmega.

(* For now, the above modular construction is instanciated on Z,
   in order to retrieve the initial ROmega. *)

Module ZOmega := IntOmega(Z_as_Int).
