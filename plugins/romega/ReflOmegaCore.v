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

  Bind Scope Int_scope with t.

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
  rewrite <- (plus_0_r y), <- (plus_0_r z), <-(opp_def x).
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

 Lemma mult_0_l x : 0*x = 0.
 Proof.
  assert (H := mult_plus_distr_r 0 1 x).
  rewrite plus_0_l, mult_1_l, plus_comm in H.
  apply plus_reg_l with x.
  now rewrite <- H, plus_0_r.
 Qed.

 Lemma mult_0_r x : x*0 = 0.
 Proof.
   rewrite mult_comm. apply mult_0_l.
 Qed.

 Lemma mult_1_r x : x*1 = x.
 Proof.
   rewrite mult_comm. apply mult_1_l.
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

 Lemma egal_left_iff n m : n = m <-> 0 = n + - m.
 Proof.
  split. intros. symmetry. now apply egal_left.
  intros. apply plus_reg_l with (-m).
  rewrite plus_comm, <- H. symmetry. apply plus_opp_l.
 Qed.

 Lemma ne_left_2 : forall x y : int, x<>y -> 0<>(x + - y).
 Proof.
 intros; contradict H.
 apply (plus_reg_l (-y)).
 now rewrite plus_opp_l, plus_comm, H.
 Qed.

 (* Special lemmas for factorisation. *)

 Lemma red_factor0 : forall n, n = n*1.
 Proof. symmetry; apply mult_1_r. Qed.

 Lemma red_factor1 : forall n, n+n = n*2.
 Proof.
  intros; unfold two.
  now rewrite mult_comm, mult_plus_distr_r, mult_1_l.
 Qed.

 Lemma red_factor2 : forall n m, n + n*m = n * (1+m).
 Proof.
  intros; rewrite mult_plus_distr_l.
  now rewrite mult_1_r.
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

 Lemma beq_iff i j : beq i j = true <-> i=j.
 Proof.
 unfold beq. rewrite <- (compare_Eq i j). now destruct compare.
 Qed.

 Lemma beq_reflect i j : reflect (i=j) (beq i j).
 Proof.
 apply iff_reflect. symmetry. apply beq_iff.
 Qed.

 Lemma eq_dec : forall n m:int, { n=m } + { n<>m }.
 Proof.
  intros n m; generalize (beq_iff n m); destruct beq; [left|right]; intuition.
 Qed.

 Definition bgt i j := match compare i j with Gt => true | _ => false end.

 Lemma bgt_iff i j : bgt i j = true <-> i>j.
 Proof.
 unfold bgt. rewrite <- (compare_Gt i j). now destruct compare.
 Qed.

 Lemma bgt_reflect i j : reflect (i>j) (bgt i j).
 Proof.
 apply iff_reflect. symmetry. apply bgt_iff.
 Qed.

 Lemma le_is_lt_or_eq : forall n m, n<=m -> { n<m } + { n=m }.
 Proof.
  intros n m Hnm.
  destruct (eq_dec n m) as [H'|H'].
  - right; intuition.
  - left; rewrite lt_le_iff.
    contradict H'.
    now apply le_antisym.
 Qed.

 Lemma le_neq_lt : forall n m, n<=m -> n<>m -> n<m.
 Proof.
  intros n m H. now destruct (le_is_lt_or_eq _ _ H).
 Qed.

 Lemma le_trans : forall n m p, n<=m -> m<=p -> n<=p.
 Proof.
  intros n m p; rewrite 3 le_lt_iff; intros A B C.
  destruct (lt_eq_lt_dec p m) as [[H|H]|H]; subst; auto.
  generalize (lt_trans _ _ _ H C); intuition.
 Qed.

 Lemma not_eq (a b:int) : ~ a <> b <-> a = b.
 Proof.
  destruct (eq_dec a b); intuition.
 Qed.

 (* order and operations *)

 Lemma le_0_neg : forall n, 0 <= n <-> -n <= 0.
 Proof.
 intros.
 rewrite <- (mult_0_l (-(1))) at 2.
 rewrite <- opp_eq_mult_neg_1.
 split; intros.
 - apply opp_le_compat; auto.
 - rewrite <-(opp_involutive 0), <-(opp_involutive n).
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
 rewrite <- (mult_0_l (-(1))) at 2.
 rewrite <- opp_eq_mult_neg_1.
 split; intros.
 - apply opp_lt_compat; auto.
 - rewrite <-(opp_involutive 0), <-(opp_involutive n).
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

 Lemma mult_integral_r n m : 0 < n -> n * m = 0 -> m = 0.
 Proof.
 intros Hn H.
 destruct (lt_eq_lt_dec 0 m) as [[Hm| <- ]|Hm]; auto; exfalso.
 - generalize (mult_lt_0_compat _ _ Hn Hm).
   rewrite H.
   exact (lt_irrefl 0).
 - rewrite lt_0_neg' in Hm.
   generalize (mult_lt_0_compat _ _ Hn Hm).
   rewrite <- opp_mult_distr_r, opp_eq_mult_neg_1, H, mult_0_l.
   exact (lt_irrefl 0).
 Qed.

 Lemma mult_integral n m : n * m = 0 -> n = 0 \/ m = 0.
 Proof.
 intros H.
 destruct (lt_eq_lt_dec 0 n) as [[Hn|Hn]|Hn].
 - right; apply (mult_integral_r n m); trivial.
 - now left.
 - right; apply (mult_integral_r (-n) m).
   + now apply lt_0_neg'.
   + rewrite mult_comm, <- opp_mult_distr_r, mult_comm, H.
     now rewrite opp_eq_mult_neg_1, mult_0_l.
 Qed.

 Lemma mult_le_compat_l i j k :
   0<=k -> i<=j -> k*i <= k*j.
 Proof.
 intros Hk Hij.
 apply le_is_lt_or_eq in Hk. apply le_is_lt_or_eq in Hij.
 destruct Hk as [Hk | <-], Hij as [Hij | <-];
  rewrite ? mult_0_l; try apply le_refl.
 now apply lt_le_weak, mult_lt_compat_l.
 Qed.

 Lemma mult_le_compat i j k l :
   i<=j -> k<=l -> 0<=i -> 0<=k -> i*k<=j*l.
 Proof.
 intros Hij Hkl Hi Hk.
 apply le_trans with (i*l).
 - now apply mult_le_compat_l.
 - rewrite (mult_comm i), (mult_comm j).
   apply mult_le_compat_l; trivial.
   now apply le_trans with k.
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

 Lemma le_left n m : n <= m <-> 0 <= m + - n.
 Proof.
  split; intros.
  - rewrite <- (opp_def m).
    apply plus_le_compat.
    apply le_refl.
    apply opp_le_compat; auto.
  - apply plus_le_reg_r with (-n).
    now rewrite plus_opp_r.
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
 intros. rewrite <- le_left.
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

 - rewrite lt_0_neg' in G.
   generalize (plus_le_lt_compat _ _ _ _ (le_refl (z*y)) H0).
   rewrite H'.
   rewrite <-(mult_1_l y) at 2. rewrite <-mult_plus_distr_r.
   intros.
   rewrite le_lt_int in G.
   rewrite <- opp_plus_distr in G.
   assert (0 < y) by (apply lt_trans with x; auto).
   generalize (mult_le_compat _ _ _ _ G (lt_le_weak _ _ H2) (le_refl 0) (le_refl 0)).
   rewrite mult_0_l, mult_comm, <- opp_mult_distr_r, mult_comm, <-le_0_neg', le_lt_iff.
   intuition.

 - subst; rewrite mult_0_l, plus_0_l in H'; subst.
   apply (lt_not_eq _ _ H); auto.

 - apply (lt_not_eq 0 (z*y+x)); auto.
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

 Lemma pos_ge_1 n : 0 < n -> 1 <= n.
 Proof.
 intros. apply plus_le_reg_r with (-(1)). rewrite opp_def.
 now apply le_lt_int.
 Qed.

 Lemma mult_le_approx n m p :
  n > 0 -> n > p -> 0 <= m * n + p -> 0 <= m.
 Proof.
 do 2 rewrite gt_lt_iff.
 do 2 rewrite le_lt_iff; intros Hn Hpn H Hm. destruct H.
 apply lt_0_neg', pos_ge_1 in Hm.
 rewrite lt_0_neg'.
 rewrite opp_plus_distr, mult_comm, opp_mult_distr_r.
 rewrite le_lt_int.
 rewrite <- plus_assoc, (plus_comm (-p)), plus_assoc.
 apply lt_left.
 rewrite le_lt_int.
 apply le_trans with (n+-(1)); [ now apply le_lt_int | ].
 apply plus_le_compat; [ | apply le_refl ].
 rewrite <- (mult_1_r n) at 1.
 apply mult_le_compat_l; auto using lt_le_weak.
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
  | Tvar : N -> term.

Bind Scope romega_scope with term.
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

(* \subsubsection{Omega steps} *)
(* The following inductive type describes steps as they can be found in
   the trace coming from the decision procedure Omega. *)

Inductive t_omega : Set :=
  (* n = 0 and n!= 0 *)
  | O_CONSTANT_NOT_NUL : nat -> t_omega
  | O_CONSTANT_NEG : nat -> t_omega
  (* division and approximation of an equation *)
  | O_DIV_APPROX : nat -> int -> int -> term -> t_omega -> t_omega
  (* no solution because no exact division *)
  | O_NOT_EXACT_DIVIDE : nat -> int -> int -> term -> t_omega
  (* exact division *)
  | O_EXACT_DIVIDE : nat -> int -> term -> t_omega -> t_omega
  | O_SUM : int -> nat -> int -> nat -> t_omega -> t_omega
  | O_CONTRADICTION : nat -> nat -> t_omega
  | O_MERGE_EQ : nat -> nat -> t_omega -> t_omega
  | O_SPLIT_INEQ : nat -> t_omega -> t_omega -> t_omega
  | O_CONSTANT_NUL : nat -> t_omega
  | O_NEGATE_CONTRADICT : nat -> nat -> t_omega
  | O_NEGATE_CONTRADICT_INV : nat -> nat -> t_omega
  | O_STATE : int -> nat -> nat -> t_omega -> t_omega.

(* \subsubsection{Rules for decomposing the hypothesis} *)
(* This type allows navigation in the logical constructors that
   form the predicats of the hypothesis in order to decompose them.
   This allows in particular to extract one hypothesis from a conjunction.
   NB: negations are silently traversed. *)

Inductive direction : Set :=
  | D_left : direction
  | D_right : direction.

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
   Then we prove the correctness of this test :
   \begin{verbatim}
   forall t1 t2 : term; eq_term t1 t2 = true <-> t1 = t2.
   \end{verbatim} *)

(* \subsubsection{Reified terms} *)

Fixpoint eq_term (t1 t2 : term) {struct t2} : bool :=
  match t1, t2 with
  | Tint st1, Tint st2 => beq st1 st2
  | (st11 + st12), (st21 + st22) => eq_term st11 st21 && eq_term st12 st22
  | (st11 * st12), (st21 * st22) => eq_term st11 st21 && eq_term st12 st22
  | (st11 - st12), (st21 - st22) => eq_term st11 st21 && eq_term st12 st22
  | (- st1), (- st2) => eq_term st1 st2
  | [st1], [st2] => N.eqb st1 st2
  | _, _ => false
  end%term.

Theorem eq_term_iff (t t' : term) :
 eq_term t t' = true <-> t = t'.
Proof.
 revert t'. induction t; destruct t'; simpl in *;
 rewrite ?andb_true_iff, ?beq_iff, ?N.eqb_eq, ?IHt, ?IHt1, ?IHt2;
  intuition congruence.
Qed.

Theorem eq_term_reflect (t t' : term) : reflect (t=t') (eq_term t t').
Proof.
 apply iff_reflect. symmetry. apply eq_term_iff.
Qed.

(* \subsection{Interprétations}
   \subsubsection{Interprétation des termes dans Z} *)

Fixpoint Nnth {A} (n:N)(l:list A)(default:A) :=
 match n, l with
   | _, nil => default
   | 0%N, x::_ => x
   | _, _::l => Nnth (N.pred n) l default
 end.

Fixpoint interp_term (env : list int) (t : term) {struct t} : int :=
  match t with
  | Tint x => x
  | (t1 + t2)%term => interp_term env t1 + interp_term env t2
  | (t1 * t2)%term => interp_term env t1 * interp_term env t2
  | (t1 - t2)%term => interp_term env t1 - interp_term env t2
  | (- t)%term => - interp_term env t
  | [n]%term => Nnth n env 0
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
 simple induction l.
 - simpl; auto.
 - simpl; intros a l1 H1 H2 H3; apply H1; intro H4; apply H2; auto.
Qed.

Theorem hyps_to_goal :
 forall (envp : list Prop) (env : list int) (l : hyps),
 interp_goal envp env l -> interp_hyps envp env l -> False.
Proof.
 simple induction l; simpl.
 - auto.
 - intros; apply H; elim H1; auto.
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
 simple induction l; simpl.
 - auto.
 - intros h1 l1 H H1; split.
    + apply goal_to_hyps; intro H2; apply H1; auto.
    + apply H; intro H2; apply H1; auto.
Qed.

Theorem list_hyps_to_goal :
 forall (envp : list Prop) (env : list int) (l : lhyps),
 interp_list_goal envp env l -> interp_list_hyps envp env l -> False.
Proof.
 simple induction l; simpl.
 - auto.
 - intros h1 l1 H (H1, H2) H3; elim H3; intro H4.
   + apply hyps_to_goal with (1 := H1); assumption.
   + auto.
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
 induction l1; simpl in *.
 - now intros l2 [H| H].
 - intros l2 [[H| H]| H].
   + auto.
   + right; apply IHl1; now left.
   + right; apply IHl1; now right.
Qed.

(* \subsubsection{Opérateurs valides sur les hypothèses} *)

(* Extraire une hypothèse de la liste *)
Definition nth_hyps (n : nat) (l : hyps) := nth n l TrueTerm.

Theorem nth_valid :
 forall (ep : list Prop) (e : list int) (i : nat) (l : hyps),
 interp_hyps ep e l -> interp_proposition ep e (nth_hyps i l).
Proof.
 unfold nth_hyps. induction i; destruct l; simpl in *; try easy.
 intros (H1,H2). now apply IHi.
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
 intros lp Hlp; split.
 - apply Hf; apply nth_valid; assumption.
 - assumption.
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
 unfold valid_hyps; intros i f Hf ep e; elim i.
 - intro lp; case lp.
    + simpl; trivial.
    + simpl; intros p l' (H1, H2); split.
       * apply Hf with (1 := H1).
       * assumption.
 - intros n Hrec lp; case lp.
    + simpl; auto.
    + simpl; intros p l' (H1, H2); split.
       * assumption.
       * apply Hrec; assumption.
Qed.

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
  (* Terms *)
  | (?X1 + ?X2)%term => loop X1 || loop X2
  | (?X1 - ?X2)%term => loop X1 || loop X2
  | (?X1 * ?X2)%term => loop X1 || loop X2
  | (- ?X1)%term => loop X1
  | (Tint ?X1) => loop X1
  (* Eliminations *)
  | (if beq ?X1 ?X2 then _ else _) =>
      let H := fresh "H" in
      case (beq_reflect X1 X2); intro H;
      try (rewrite H in *; clear H); simpl; auto; Simplify
  | (if bgt ?X1 ?X2 then _ else _) =>
      case (bgt_reflect X1 X2); intro; simpl; auto; Simplify
  | (if eq_term ?X1 ?X2 then _ else _) =>
      let H := fresh "H" in
      case (eq_term_reflect X1 X2); intro H;
      try (rewrite H in *; clear H); simpl; auto; Simplify
  | (if _ && _ then _ else _) => rewrite andb_if; Simplify
  | (if negb _ then _ else _) => rewrite negb_if; Simplify
  | match N.compare ?X1 ?X2 with _ => _ end =>
    destruct (N.compare_spec X1 X2); Simplify
  | match ?X1 with _ => _ end => destruct X1; auto; Simplify
  | _ => fail
  end

with Simplify := match goal with
  |  |- ?X1 => try loop X1
  | _ => idtac
  end.

(* \subsubsection{Opérations affines sur une équation} *)

(* \paragraph{Multiplication scalaire et somme d'une constante} *)

(* invariant: k1<>0 *)

Fixpoint scalar_norm_add (t : term) (k1 k2 : int) : term :=
  match t with
  | (v1 * Tint x1 + l1)%term =>
    (v1 * Tint (x1 * k1) + scalar_norm_add l1 k1 k2)%term
  | Tint x => Tint (x * k1 + k2)
  | _ => (t * Tint k1 + Tint k2)%term (* shouldn't happen *)
  end.

Theorem scalar_norm_add_stable e t k1 k2 :
 interp_term e (t * Tint k1 + Tint k2)%term =
 interp_term e (scalar_norm_add t k1 k2).
Proof.
 induction t; simpl; Simplify; simpl; auto.
 rewrite <- IHt2. simpl. apply OMEGA11.
Qed.

(* \paragraph{Multiplication scalaire} *)

Definition scalar_norm (t : term) (k : int) := scalar_norm_add t k 0.

Theorem scalar_norm_stable e t k :
 interp_term e (t * Tint k)%term = interp_term e (scalar_norm t k).
Proof.
 unfold scalar_norm. rewrite <- scalar_norm_add_stable. simpl.
 symmetry. apply plus_0_r.
Qed.

(* \paragraph{Somme d'une constante} *)

Fixpoint add_norm (t : term) (k : int) : term :=
  match t with
  | (m + l)%term => (m + add_norm l k)%term
  | Tint x => Tint (x + k)
  | _ => (t + Tint k)%term
  end.

Theorem add_norm_stable e t k :
 interp_term e (t + Tint k)%term = interp_term e (add_norm t k).
Proof.
 induction t; simpl; Simplify; simpl; auto.
 rewrite <- IHt2. simpl. symmetry. apply plus_assoc.
Qed.

(* \subsubsection{Fusions}
    \paragraph{Fusion de deux équations} *)
(* On donne une somme de deux équations qui sont supposées normalisées.
   Cette fonction prend une trace de fusion en argument et transforme
   le terme en une équation normalisée. *)
(* Invariant : k1 and k2 non-null *)

Fixpoint fusion (t1 t2 : term) (k1 k2 : int) : term :=
  match t1 with
  | ([v1] * Tint x1 + l1)%term =>
    (fix fusion_t1 t2 : term :=
       match t2 with
         | ([v2] * Tint x2 + l2)%term =>
           match N.compare v1 v2 with
             | Eq =>
               let k := x1 * k1 + x2 * k2 in
               if beq k 0 then fusion l1 l2 k1 k2
               else ([v1] * Tint k + fusion l1 l2 k1 k2)%term
             | Lt => ([v2] * Tint (x2 * k2) + fusion_t1 l2)%term
             | Gt => ([v1] * Tint (x1 * k1) + fusion l1 t2 k1 k2)%term
           end
         | Tint x2 => ([v1] * Tint (x1 * k1) + fusion l1 t2 k1 k2)%term
         | _ => (t1 * Tint k1 + t2 * Tint k2)%term
       end) t2
  | Tint x1 => scalar_norm_add t2 k2 (x1 * k1)
  | _ => (t1 * Tint k1 + t2 * Tint k2)%term (* shouldn't happen *)
  end.

Theorem fusion_stable e t1 t2 k1 k2 :
 interp_term e (t1 * Tint k1 + t2 * Tint k2)%term =
 interp_term e (fusion t1 t2 k1 k2).
Proof.
 revert t2; induction t1; simpl; Simplify; simpl; auto.
 - intros; rewrite <- scalar_norm_add_stable. simpl. apply plus_comm.
 - intros. Simplify. induction t2; simpl; Simplify; simpl; auto.
   + rewrite <- IHt1_2. simpl. apply OMEGA11.
   + rewrite <- IHt1_2. simpl. subst n0. rewrite OMEGA10, H0.
     now rewrite mult_comm, mult_0_l, plus_0_l.
   + rewrite <- IHt1_2. simpl. subst n0. apply OMEGA10.
   + rewrite <- IHt2_2. simpl. apply OMEGA12.
   + rewrite <- IHt1_2. simpl. apply OMEGA11.
Qed.

(* Main function of term normalization.
   Precondition: all [Tmult] should be on at least one [Tint].
   Postcondition: [([v1]*Tint k1 + ([v2]*Tint k2 + (... + Tint cst)))]
    with [v1>v2>...] and [ki<>0].
 *)

Fixpoint normalize t :=
  match t with
  | Tint n => Tint n
  | [n]%term => ([n] * Tint 1 + Tint 0)%term
  | (t + t')%term => fusion (normalize t) (normalize t') 1 1
  | (- t)%term => scalar_norm (normalize t) (-(1))
  | (t - t')%term => fusion (normalize t) (normalize t') 1 (-(1))
  | (Tint k * t)%term | (t * Tint k)%term =>
    if beq k 0 then Tint 0
    else scalar_norm (normalize t) k
  | (t1 * t2)%term => (t1 * t2)%term (* shouldn't happen *)
  end.

Theorem normalize_stable : term_stable normalize.
Proof.
 intros e t.
 induction t; simpl; Simplify; simpl;
 rewrite <- ?scalar_norm_stable; simpl in *; rewrite <- ?IHt1;
 rewrite <- ?fusion_stable; simpl;
 rewrite ?mult_0_l, ?mult_0_r, ?mult_1_l, ?mult_1_r, ?plus_0_r; auto.
 - now f_equal.
 - rewrite mult_comm. now f_equal.
 - rewrite <- opp_eq_mult_neg_1, <-minus_def. now f_equal.
 - rewrite <- opp_eq_mult_neg_1. now f_equal.
Qed.

(* \paragraph{Fusion avec annihilation} *)
(* Normalement le résultat est une constante *)

Fixpoint fusion_cancel (t1 t2 : term) : term :=
  match t1, t2 with
  | (v1 * Tint x1 + l1)%term, (v2 * Tint x2 + l2)%term =>
    if eq_term v1 v2 && beq x1 (-x2)
    then fusion_cancel l1 l2
    else (t1+t2)%term (* should not happen *)
  | Tint x1, Tint x2 => Tint (x1+x2)
  | _, _ => (t1+t2)%term (* should not happen *)
  end.

Theorem fusion_cancel_stable e t1 t2 :
 interp_term e (t1+t2)%term = interp_term e (fusion_cancel t1 t2).
Proof.
 revert t2. induction t1; destruct t2; simpl; Simplify; auto.
 simpl in *.
 rewrite <- IHt1_2.
 apply OMEGA13.
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
 unfold valid_hyps, constant_neg. intros.
 generalize (nth_valid ep e i lp). Simplify; simpl.
 rewrite gt_lt_iff in *; rewrite le_lt_iff; intuition.
Qed.

(* \paragraph{[NOT_EXACT_DIVIDE]} *)
Definition not_exact_divide (i : nat) (k1 k2 : int) (body : term)
  (l : hyps) :=
  match nth_hyps i l with
  | EqTerm (Tint Nul) b =>
      if beq Nul 0 &&
         eq_term (scalar_norm_add body k1 k2) b &&
         bgt k2 0 &&
         bgt k1 k2
      then absurd
      else l
  | _ => l
  end.

Theorem not_exact_divide_valid :
 forall (i : nat)(k1 k2 : int) (body : term),
 valid_hyps (not_exact_divide i k1 k2 body).
Proof.
 unfold valid_hyps, not_exact_divide; intros.
 generalize (nth_valid ep e i lp); Simplify.
 rewrite <-H1, <-scalar_norm_add_stable. simpl.
 intros.
 absurd (interp_term e body * k1 + k2 = 0).
 - now apply OMEGA4.
 - symmetry; auto.
Qed.

(* \paragraph{[O_CONTRADICTION]} *)

Definition contradiction (i j : nat) (l : hyps) :=
  match nth_hyps i l with
  | LeqTerm (Tint Nul) b1 =>
      match nth_hyps j l with
      | LeqTerm (Tint Nul') b2 =>
          match fusion_cancel b1 b2 with
          | Tint k => if beq Nul 0 && beq Nul' 0 && bgt 0 k
                      then absurd
                      else l
          | _ => l
          end
      | _ => l
      end
  | _ => l
  end.

Theorem contradiction_valid (i j : nat) : valid_hyps (contradiction i j).
Proof.
 unfold valid_hyps, contradiction; intros ep e l H.
 generalize (nth_valid _ _ i _ H) (nth_valid _ _ j _ H).
 case (nth_hyps i l); trivial. intros t1 t2.
 case t1; trivial. clear t1; intros x1.
 case (nth_hyps j l); trivial. intros t3 t4.
 case t3; trivial. clear t3; intros x3.
 destruct fusion_cancel as [ t0 | | | | | ] eqn:E; trivial.
 change t0 with (interp_term e (Tint t0)).
 rewrite <- E, <- fusion_cancel_stable.
 Simplify.
 intros H1 H2.
 generalize (OMEGA2 _ _ H1 H2).
 rewrite gt_lt_iff in *; rewrite le_lt_iff. intuition.
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

Definition negate_contradict_inv (i1 i2 : nat) (h : hyps) :=
  match nth_hyps i1 h with
  | EqTerm (Tint Nul) b1 =>
      match nth_hyps i2 h with
      | NeqTerm (Tint Nul') b2 =>
          if beq Nul 0 && beq Nul' 0 &&
             eq_term b1 (scalar_norm b2 (-(1)))
          then absurd
          else h
      | _ => h
      end
  | NeqTerm (Tint Nul) b1 =>
      match nth_hyps i2 h with
      | EqTerm (Tint Nul') b2 =>
          if beq Nul 0 && beq Nul' 0 &&
             eq_term b1 (scalar_norm b2 (-(1)))
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
 generalize (nth_valid _ _ i _ H) (nth_valid _ _ j _ H);
 case (nth_hyps i l); auto; intros t1 t2; case t1;
 auto; intros z; auto; case (nth_hyps j l);
 auto; intros t3 t4; case t3; auto; intros z';
 auto; simpl; intros; Simplify.
Qed.

Theorem negate_contradict_inv_valid :
 forall i j : nat, valid_hyps (negate_contradict_inv i j).
Proof.
 unfold valid_hyps, negate_contradict_inv; intros i j ep e l H;
 generalize (nth_valid _ _ i _ H) (nth_valid _ _ j _ H);
 case (nth_hyps i l); auto; intros t1 t2; case t1;
 auto; intros z; auto; case (nth_hyps j l);
 auto; intros t3 t4; case t3; auto; intros z';
 auto; simpl; intros H1 H2; Simplify.
 - rewrite <- scalar_norm_stable in H1; simpl in *;
   elim (mult_integral (interp_term e t4) (-(1))); intuition;
   elim minus_one_neq_zero; auto.
 - elim H1; clear H1;
   rewrite <- scalar_norm_stable; simpl in *;
   now rewrite <- H2, mult_0_l.
Qed.

(* \subsubsection{Tactiques générant une nouvelle équation} *)
(* \paragraph{[O_SUM]}
 C'est une oper2 valide mais elle traite plusieurs cas à la fois (suivant
 les opérateurs de comparaison des deux arguments) d'où une
 preuve un peu compliquée. On utilise quelques lemmes qui sont des
 généralisations des théorèmes utilisés par OMEGA. *)

Definition sum (k1 k2 : int) (prop1 prop2 : proposition) :=
  match prop1 with
  | EqTerm (Tint Null) b1 =>
      match prop2 with
      | EqTerm (Tint Null') b2 =>
          if beq Null 0 && beq Null' 0
          then EqTerm (Tint 0) (fusion b1 b2 k1 k2)
          else TrueTerm
      | LeqTerm (Tint Null') b2 =>
          if beq Null 0 && beq Null' 0 && bgt k2 0
          then LeqTerm (Tint 0) (fusion b1 b2 k1 k2)
          else TrueTerm
      | _ => TrueTerm
      end
  | LeqTerm (Tint Null) b1 =>
      if beq Null 0 && bgt k1 0
      then match prop2 with
          | EqTerm (Tint Null') b2 =>
              if beq Null' 0 then
              LeqTerm (Tint 0) (fusion b1 b2 k1 k2)
              else TrueTerm
          | LeqTerm (Tint Null') b2 =>
              if beq Null' 0 && bgt k2 0
              then LeqTerm (Tint 0) (fusion b1 b2 k1 k2)
              else TrueTerm
          | _ => TrueTerm
          end
      else TrueTerm
  | NeqTerm (Tint Null) b1 =>
      match prop2 with
      | EqTerm (Tint Null') b2 =>
          if beq Null 0 && beq Null' 0 && (negb (beq k1 0))
          then NeqTerm (Tint 0) (fusion b1 b2 k1 k2)
          else TrueTerm
      | _ => TrueTerm
      end
  | _ => TrueTerm
  end.


Theorem sum_valid :
 forall (k1 k2 : int), valid2 (sum k1 k2).
Proof.
 unfold valid2; intros k1 k2 t ep e p1 p2; unfold sum;
 Simplify; simpl; rewrite <- ?fusion_stable;
 simpl; intros; auto.
 - apply sum1; assumption.
 - apply sum2; try assumption; apply sum4; assumption.
 - rewrite plus_comm; apply sum2; try assumption; apply sum4; assumption.
 - apply sum3; try assumption; apply sum4; assumption.
 - apply sum5; auto.
Qed.

(* \paragraph{[O_EXACT_DIVIDE]}
   c'est une oper1 valide mais on préfère une substitution a ce point la *)

Definition exact_divide (k : int) (body : term) (prop : proposition) :=
  match prop with
  | EqTerm (Tint Null) b =>
      if beq Null 0 &&
         eq_term (scalar_norm body k) b &&
         negb (beq k 0)
      then EqTerm (Tint 0) body
      else TrueTerm
  | NeqTerm (Tint Null) b =>
      if beq Null 0 &&
         eq_term (scalar_norm body k) b &&
         negb (beq k 0)
      then NeqTerm (Tint 0) body
      else TrueTerm
  | _ => TrueTerm
  end.

Theorem exact_divide_valid :
 forall (k : int) (t : term), valid1 (exact_divide k t).
Proof.
 unfold valid1, exact_divide; intros k t ep e p1;
 Simplify; simpl; auto; subst;
 rewrite <- scalar_norm_stable; simpl; intros.
 - destruct (mult_integral _ _ (eq_sym H0)); intuition.
 - contradict H0; rewrite <- H0, mult_0_l; auto.
Qed.


(* \paragraph{[O_DIV_APPROX]}
  La preuve reprend le schéma de la précédente mais on
  est sur une opération de type valid1 et non sur une opération terminale. *)

Definition divide_and_approx (k1 k2 : int) (body : term)
  (prop : proposition) :=
  match prop with
  | LeqTerm (Tint Null) b =>
      if beq Null 0 &&
         eq_term (scalar_norm_add body k1 k2) b &&
         bgt k1 0 &&
         bgt k1 k2
      then LeqTerm (Tint 0) body
      else prop
  | _ => prop
  end.

Theorem divide_and_approx_valid :
 forall (k1 k2 : int) (body : term),
 valid1 (divide_and_approx k1 k2 body).
Proof.
 unfold valid1, divide_and_approx.
 intros k1 k2 body ep e p1. Simplify. subst.
 rewrite <- scalar_norm_add_stable. simpl.
 intro H; now apply mult_le_approx with (3 := H).
Qed.

(* \paragraph{[MERGE_EQ]} *)

Definition merge_eq (prop1 prop2 : proposition) :=
  match prop1 with
  | LeqTerm (Tint Null) b1 =>
      match prop2 with
      | LeqTerm (Tint Null') b2 =>
          if beq Null 0 && beq Null' 0 &&
             eq_term b1 (scalar_norm b2 (-(1)))
          then EqTerm (Tint 0) b1
          else TrueTerm
      | _ => TrueTerm
      end
  | _ => TrueTerm
  end.

Theorem merge_eq_valid : valid2 merge_eq.
Proof.
 unfold valid2, merge_eq; intros ep e p1 p2; Simplify; simpl; auto.
 rewrite <- scalar_norm_stable. simpl.
 intros; symmetry ; apply OMEGA8 with (2 := H0).
 - assumption.
 - elim opp_eq_mult_neg_1; trivial.
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
 generalize (nth_valid ep e i lp); Simplify; simpl; intuition.
Qed.

(* \paragraph{[O_STATE]} *)

Definition state (m : int) (prop1 prop2 : proposition) :=
  match prop1 with
  | EqTerm (Tint Null) b1 =>
      match prop2 with
      | EqTerm (Tint Null') b2 =>
          if beq Null 0 && beq Null' 0
          then EqTerm (Tint 0) (fusion b1 b2 1 m)
          else TrueTerm
      | _ => TrueTerm
      end
  | _ => TrueTerm
  end.

Theorem state_valid : forall (m : int), valid2 (state m).
Proof.
 unfold valid2; intros m ep e p1 p2.
 unfold state; Simplify; simpl; auto.
 rewrite <- fusion_stable. simpl in *. intros H H'.
 rewrite <- H, <- H'. now rewrite !mult_0_l, plus_0_l.
Qed.

(* \subsubsection{Tactiques générant plusieurs but}
   \paragraph{[O_SPLIT_INEQ]}
   La seule pour le moment (tant que la normalisation n'est pas réfléchie). *)

Definition split_ineq (i : nat) (f1 f2 : hyps -> lhyps) (l : hyps) :=
  match nth_hyps i l with
  | NeqTerm (Tint Null) b1 =>
      if beq Null 0 then
       f1 (LeqTerm (Tint 0) (add_norm b1 (-(1))) :: l) ++
       f2 (LeqTerm (Tint 0) (scalar_norm_add b1 (-(1)) (-(1))) :: l)
      else l :: nil
  | _ => l :: nil
  end.

Theorem split_ineq_valid :
 forall (i : nat) (f1 f2 : hyps -> lhyps),
 valid_list_hyps f1 ->
 valid_list_hyps f2 -> valid_list_hyps (split_ineq i f1 f2).
Proof.
 unfold valid_list_hyps, split_ineq; intros i f1 f2 H1 H2 ep e lp H;
 generalize (nth_valid _ _ i _ H); case (nth_hyps i lp);
 simpl; auto; intros t1 t2; case t1; simpl;
 auto; intros z; simpl; auto; intro H3.
 Simplify.
 apply append_valid; elim (OMEGA19 (interp_term e t2)).
 - intro H4; left; apply H1; simpl; rewrite <- add_norm_stable;
    simpl; auto.
 - intro H4; right; apply H2; simpl; rewrite <- scalar_norm_add_stable;
    simpl; auto.
 - generalize H3; unfold not; intros E1 E2; apply E1;
    symmetry ; trivial.
Qed.


(* \subsection{Replaying the resolution trace} *)

Fixpoint execute_omega (t : t_omega) (l : hyps) {struct t} : lhyps :=
  match t with
  | O_CONSTANT_NOT_NUL n => singleton (constant_not_nul n l)
  | O_CONSTANT_NEG n => singleton (constant_neg n l)
  | O_DIV_APPROX n k1 k2 body cont =>
      execute_omega cont (apply_oper_1 n (divide_and_approx k1 k2 body) l)
  | O_NOT_EXACT_DIVIDE i k1 k2 body =>
      singleton (not_exact_divide i k1 k2 body l)
  | O_EXACT_DIVIDE n k body cont =>
      execute_omega cont (apply_oper_1 n (exact_divide k body) l)
  | O_SUM k1 i1 k2 i2 cont =>
      execute_omega cont (apply_oper_2 i1 i2 (sum k1 k2) l)
  | O_CONTRADICTION i j => singleton (contradiction i j l)
  | O_MERGE_EQ i1 i2 cont =>
      execute_omega cont (apply_oper_2 i1 i2 merge_eq l)
  | O_SPLIT_INEQ i cont1 cont2 =>
      split_ineq i (execute_omega cont1) (execute_omega cont2) l
  | O_CONSTANT_NUL i => singleton (constant_nul i l)
  | O_NEGATE_CONTRADICT i j => singleton (negate_contradict i j l)
  | O_NEGATE_CONTRADICT_INV i j =>
      singleton (negate_contradict_inv i j l)
  | O_STATE m i1 i2 cont =>
      execute_omega cont (apply_oper_2 i1 i2 (state m) l)
  end.

Theorem omega_valid : forall tr : t_omega, valid_list_hyps (execute_omega tr).
Proof.
 simple induction tr; simpl.
 - unfold valid_list_hyps; simpl; intros; left;
    apply (constant_not_nul_valid n ep e lp H).
 - unfold valid_list_hyps; simpl; intros; left;
    apply (constant_neg_valid n ep e lp H).
 - unfold valid_list_hyps, valid_hyps;
    intros m k1 k2 body t' Ht' ep e lp H; apply Ht';
    apply
     (apply_oper_1_valid m (divide_and_approx k1 k2 body)
        (divide_and_approx_valid k1 k2 body) ep e lp H).
 - unfold valid_list_hyps; simpl; intros; left;
    apply (not_exact_divide_valid _ _ _ _ ep e lp H).
 - unfold valid_list_hyps, valid_hyps;
    intros m k body t' Ht' ep e lp H; apply Ht';
    apply
     (apply_oper_1_valid m (exact_divide k body)
        (exact_divide_valid k body) ep e lp H).
 - unfold valid_list_hyps, valid_hyps;
    intros k1 i1 k2 i2 t' Ht' ep e lp H; apply Ht';
    apply
     (apply_oper_2_valid i1 i2 (sum k1 k2) (sum_valid k1 k2) ep e
        lp H).
 - unfold valid_list_hyps; simpl; intros; left.
    apply (contradiction_valid n n0 ep e lp H).
 - unfold valid_list_hyps, valid_hyps;
    intros i1 i2 t' Ht' ep e lp H; apply Ht';
    apply
     (apply_oper_2_valid i1 i2 merge_eq merge_eq_valid ep e
        lp H).
 - intros i k1 H1 k2 H2; unfold valid_list_hyps; simpl;
    intros ep e lp H;
    apply
     (split_ineq_valid i (execute_omega k1) (execute_omega k2) H1 H2 ep e
        lp H).
 - unfold valid_list_hyps; simpl; intros i ep e lp H; left;
    apply (constant_nul_valid i ep e lp H).
 - unfold valid_list_hyps; simpl; intros i j ep e lp H; left;
    apply (negate_contradict_valid i j ep e lp H).
 - unfold valid_list_hyps; simpl; intros i j ep e lp H;
    left; apply (negate_contradict_inv_valid i j ep e lp H).
 - unfold valid_list_hyps, valid_hyps;
    intros m i1 i2 t' Ht' ep e lp H; apply Ht';
    apply (apply_oper_2_valid i1 i2 (state m) (state_valid m) ep e lp H).
Qed.

(* \subsection{Les opérations globales sur le but}
   \subsubsection{Normalisation} *)

Fixpoint normalize_prop (negated:bool)(p:proposition) :=
  match p with
  | EqTerm t1 t2 =>
    if negated then Tnot (NeqTerm (Tint 0) (normalize (t1-t2)))
    else EqTerm (Tint 0) (normalize (t1-t2))
  | NeqTerm t1 t2 =>
    if negated then Tnot (EqTerm (Tint 0) (normalize (t1-t2)))
    else NeqTerm (Tint 0) (normalize (t1-t2))
  | LeqTerm t1 t2 =>
    if negated then Tnot (LeqTerm (Tint 0) (normalize (t1-t2+Tint (-(1)))))
    else LeqTerm (Tint 0) (normalize (t2-t1))
  | GeqTerm t1 t2 =>
    if negated then Tnot (LeqTerm (Tint 0) (normalize (t2-t1+Tint (-(1)))))
    else LeqTerm (Tint 0) (normalize (t1-t2))
  | LtTerm t1 t2 =>
    if negated then Tnot (LeqTerm (Tint 0) (normalize (t1-t2)))
    else LeqTerm (Tint 0) (normalize (t2-t1+Tint (-(1))))
  | GtTerm t1 t2 =>
    if negated then Tnot (LeqTerm (Tint 0) (normalize (t2-t1)))
    else LeqTerm (Tint 0) (normalize (t1-t2+Tint (-(1))))
  | Tnot p => Tnot (normalize_prop (negb negated) p)
  | Tor p p' => Tor (normalize_prop negated p) (normalize_prop negated p')
  | Tand p p' => Tand (normalize_prop negated p) (normalize_prop negated p')
  | Timp p p' => Timp (normalize_prop (negb negated) p)
                      (normalize_prop negated p')
  | Tprop _ | TrueTerm | FalseTerm => p
  end.

Definition normalize_hyps := List.map (normalize_prop false).

Opaque normalize.

Theorem normalize_prop_valid b e ep p :
  interp_proposition e ep p <->
  interp_proposition e ep (normalize_prop b p).
Proof.
 revert b.
 induction p; intros; simpl; try tauto.
 - destruct b; simpl;
   rewrite <- ?normalize_stable; simpl; rewrite ?minus_def.
   + rewrite not_eq. apply egal_left_iff.
   + apply egal_left_iff.
 - destruct b; simpl;
   rewrite <- ? normalize_stable; simpl; rewrite ?minus_def.
   + rewrite le_lt_iff. apply not_iff_compat.
     rewrite le_lt_int. rewrite le_left.
     rewrite <- !plus_assoc. now rewrite (plus_comm (-(1))).
   + apply le_left.
 - now rewrite <- IHp.
 - destruct b; simpl;
   rewrite <- ? normalize_stable; simpl; rewrite ?minus_def.
   + rewrite ge_le_iff, le_lt_iff. apply not_iff_compat.
     rewrite le_lt_int. rewrite le_left.
     rewrite <- !plus_assoc. now rewrite (plus_comm (-(1))).
   + rewrite ge_le_iff. apply le_left.
 - destruct b; simpl;
   rewrite <- ? normalize_stable; simpl; rewrite ?minus_def.
   + rewrite gt_lt_iff, lt_le_iff. apply not_iff_compat.
     apply le_left.
   + rewrite gt_lt_iff. rewrite le_lt_int. rewrite le_left.
     rewrite <- !plus_assoc. now rewrite (plus_comm (-(1))).
 - destruct b; simpl;
   rewrite <- ? normalize_stable; simpl; rewrite ?minus_def.
   + rewrite lt_le_iff. apply not_iff_compat.
     apply le_left.
   + rewrite le_lt_int, le_left.
     rewrite <- !plus_assoc. now rewrite (plus_comm (-(1))).
 - destruct b; simpl;
   rewrite <- ? normalize_stable; simpl; rewrite ?minus_def;
   apply not_iff_compat, egal_left_iff.
 - now rewrite <- IHp1, <- IHp2.
 - now rewrite <- IHp1, <- IHp2.
 - now rewrite <- IHp1, <- IHp2.
Qed.

Transparent normalize.

Theorem normalize_hyps_valid : valid_hyps normalize_hyps.
Proof.
 intros e ep l. induction l; simpl; intuition.
 now rewrite <- normalize_prop_valid.
Qed.

Theorem normalize_hyps_goal (ep : list Prop) (env : list int) (l : hyps) :
 interp_goal ep env (normalize_hyps l) -> interp_goal ep env l.
Proof.
 intros; apply valid_goal with (2 := H); apply normalize_hyps_valid.
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
 simple induction p; simpl; intros.
 - apply dec_eq.
 - apply dec_le.
 - left; auto.
 - right; unfold not; auto.
 - apply dec_not; auto.
 - apply dec_ge.
 - apply dec_gt.
 - apply dec_lt.
 - apply dec_ne.
 - apply dec_or; elim andb_prop with (1 := H1); auto.
 - apply dec_and; elim andb_prop with (1 := H1); auto.
 - apply dec_imp; elim andb_prop with (1 := H1); auto.
 - discriminate H.
Qed.

Fixpoint extract_hyp_pos (s : list direction) (p : proposition) :
 proposition :=
  match p, s with
  | Tand x y, D_left :: l => extract_hyp_pos l x
  | Tand x y, D_right :: l => extract_hyp_pos l y
  | Tnot x, _ => extract_hyp_neg s x
  | _, _ => p
  end

 with extract_hyp_neg (s : list direction) (p : proposition) :
 proposition :=
  match p, s with
  | Tor x y, D_left :: l => extract_hyp_neg l x
  | Tor x y, D_right :: l => extract_hyp_neg l y
  | Timp x y, D_left :: l =>
    if decidability x then extract_hyp_pos l x else Tnot p
  | Timp x y, D_right :: l => extract_hyp_neg l y
  | Tnot x, _ => if decidability x then extract_hyp_pos s x else Tnot p
  | _, _ => Tnot p
  end.

Theorem extract_valid :
 forall s : list direction, valid1 (extract_hyp_pos s).
Proof.
 assert (forall p s ep e,
         (interp_proposition ep e p ->
          interp_proposition ep e (extract_hyp_pos s p)) /\
         (interp_proposition ep e (Tnot p) ->
          interp_proposition ep e (extract_hyp_neg s p))).
 { induction p; destruct s; simpl; auto; split; try destruct d; try easy;
   intros; (apply IHp || apply IHp1 || apply IHp2 || idtac); simpl; try tauto;
   destruct decidability eqn:D; auto;
   apply (decidable_correct ep e) in D; unfold decidable in D;
   (apply IHp || apply IHp1); tauto. }
 red. intros. now apply H.
Qed.

(** Attempt to shorten error messages if romega goes rogue...
    NB: [interp_list_goal _ _ BUG = False /\ True]. *)
Definition BUG : lhyps := nil :: nil.

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
          else BUG
      | Timp x y =>
          if decidability x then
            decompose_solve s1 (Tnot x :: h) ++ decompose_solve s2 (y :: h)
          else BUG
      | _ => BUG
      end
  | E_EXTRACT i dl s1 =>
      decompose_solve s1 (extract_hyp_pos dl (nth_hyps i h) :: h)
  | E_SOLVE t => execute_omega t h
  end.

Theorem decompose_solve_valid (s : e_step) :
 valid_list_goal (decompose_solve s).
Proof.
 apply goal_valid. red. induction s; simpl; intros ep e lp H.
 - assert (H' : interp_proposition ep e (extract_hyp_pos l (nth_hyps n lp))).
   { now apply extract_valid, nth_valid. }
   destruct extract_hyp_pos; simpl in *; auto.
   + destruct p; simpl; auto.
     destruct decidability eqn:D; [ | simpl; auto].
     apply (decidable_correct ep e) in D.
     apply append_valid. simpl in *. destruct D.
     * right. apply IHs2. simpl; auto.
     * left. apply IHs1. simpl; auto.
   + apply append_valid. destruct H'.
     * left. apply IHs1. simpl; auto.
     * right. apply IHs2. simpl; auto.
   + destruct decidability eqn:D; [ | simpl; auto].
     apply (decidable_correct ep e) in D.
     apply append_valid. destruct D.
     * right. apply IHs2. simpl; auto.
     * left. apply IHs1. simpl; auto.
 - apply IHs; simpl; split; auto.
   now apply extract_valid, nth_valid.
 - now apply omega_valid.
Qed.

(* \subsection{La dernière étape qui élimine tous les séquents inutiles} *)

Definition valid_lhyps (f : lhyps -> lhyps) :=
  forall (ep : list Prop) (e : list int) (lp : lhyps),
  interp_list_hyps ep e lp -> interp_list_hyps ep e (f lp).

Fixpoint reduce_lhyps (lp : lhyps) : lhyps :=
  match lp with
  | nil => nil
  | (FalseTerm :: nil) :: lp' => reduce_lhyps lp'
  | x :: lp' => BUG
  end.

Theorem reduce_lhyps_valid : valid_lhyps reduce_lhyps.
Proof.
 unfold valid_lhyps; intros ep e lp; elim lp.
 - simpl; auto.
 - intros a l HR; elim a.
    + simpl; tauto.
    + intros a1 l1; case l1; case a1; simpl; tauto.
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
 induction l; simpl.
 - unfold concl_to_hyp; simpl.
   destruct decidability eqn:D; [ | simpl; tauto ].
   apply (decidable_correct envp env) in D. unfold decidable in D.
   simpl. tauto.
 - simpl in *; tauto.
Qed.

Definition omega_tactic (t1 : e_step) (c : proposition) (l : hyps) :=
  reduce_lhyps (decompose_solve t1 (normalize_hyps (concl_to_hyp c :: l))).

Theorem do_omega :
 forall (t : e_step) (envp : list Prop)
   (env : list int) (c : proposition) (l : hyps),
 interp_list_goal envp env (omega_tactic t c l) ->
 interp_goal_concl c envp env l.
Proof.
 unfold omega_tactic; intros t ep e c l H.
 apply do_concl_to_hyp.
 apply normalize_hyps_goal.
 apply (decompose_solve_valid t).
 now apply do_reduce_lhyps.
Qed.

End IntOmega.

(* For now, the above modular construction is instanciated on Z,
   in order to retrieve the initial ROmega. *)

Module ZOmega := IntOmega(Z_as_Int).
