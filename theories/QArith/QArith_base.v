(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Export ZArith.
Require Export ZArithRing.
Require Export Morphisms Setoid Bool.

(** * Definition of [Q] and basic properties *)

(** Rationals are pairs of [Z] and [positive] numbers. *)

Record Q : Set := Qmake {Qnum : Z; Qden : positive}.

Delimit Scope Q_scope with Q.
Bind Scope Q_scope with Q.
Arguments Scope Qmake [Z_scope positive_scope].
Open Scope Q_scope.
Ltac simpl_mult := repeat rewrite Zpos_mult_morphism.

(** [a#b] denotes the fraction [a] over [b]. *)

Notation "a # b" := (Qmake a b) (at level 55, no associativity) : Q_scope.

Definition inject_Z (x : Z) := Qmake x 1.
Arguments Scope inject_Z [Z_scope].

Notation QDen p := (Zpos (Qden p)).
Notation " 0 " := (0#1) : Q_scope.
Notation " 1 " := (1#1) : Q_scope.

Definition Qeq (p q : Q) := (Qnum p * QDen q)%Z = (Qnum q * QDen p)%Z.
Definition Qle (x y : Q) := (Qnum x * QDen y <= Qnum y * QDen x)%Z.
Definition Qlt (x y : Q) := (Qnum x * QDen y < Qnum y * QDen x)%Z.
Notation Qgt a b := (Qlt b a) (only parsing).
Notation Qge a b := (Qle b a) (only parsing).

Infix "==" := Qeq (at level 70, no associativity) : Q_scope.
Infix "<" := Qlt : Q_scope.
Infix "<=" := Qle : Q_scope.
Notation "x > y" := (Qlt y x)(only parsing) : Q_scope.
Notation "x >= y" := (Qle y x)(only parsing) : Q_scope.
Notation "x <= y <= z" := (x<=y/\y<=z) : Q_scope.

(** Another approach : using Qcompare for defining order relations. *)

Definition Qcompare (p q : Q) := (Qnum p * QDen q ?= Qnum q * QDen p)%Z.
Notation "p ?= q" := (Qcompare p q) : Q_scope.

Lemma Qeq_alt : forall p q, (p == q) <-> (p ?= q) = Eq.
Proof.
unfold Qeq, Qcompare; intros; split; intros.
rewrite H; apply Zcompare_refl.
apply Zcompare_Eq_eq; auto.
Qed.

Lemma Qlt_alt : forall p q, (p<q) <-> (p?=q = Lt).
Proof.
unfold Qlt, Qcompare, Zlt; split; auto.
Qed.

Lemma Qgt_alt : forall p q, (p>q) <-> (p?=q = Gt).
Proof.
unfold Qlt, Qcompare, Zlt.
intros; rewrite Zcompare_Gt_Lt_antisym; split; auto.
Qed.

Lemma Qle_alt : forall p q, (p<=q) <-> (p?=q <> Gt).
Proof.
unfold Qle, Qcompare, Zle; split; auto.
Qed.

Lemma Qge_alt : forall p q, (p>=q) <-> (p?=q <> Lt).
Proof.
unfold Qle, Qcompare, Zle.
split; intros; contradict H.
rewrite Zcompare_Gt_Lt_antisym; auto.
rewrite Zcompare_Gt_Lt_antisym in H; auto.
Qed.

Hint Unfold Qeq Qlt Qle : qarith.
Hint Extern 5 (?X1 <> ?X2) => intro; discriminate: qarith.

Lemma Qcompare_antisym : forall x y, CompOpp (x ?= y) = (y ?= x).
Proof.
 unfold "?=". intros. apply Zcompare_antisym.
Qed.

Lemma Qcompare_spec : forall x y, CompSpec Qeq Qlt x y (x ?= y).
Proof.
 intros.
 destruct (x ?= y) as [ ]_eqn:H; constructor; auto.
 rewrite Qeq_alt; auto.
 rewrite Qlt_alt, <- Qcompare_antisym, H; auto.
Qed.

(** * Properties of equality. *)

Theorem Qeq_refl : forall x, x == x.
Proof.
 auto with qarith.
Qed.

Theorem Qeq_sym : forall x y, x == y -> y == x.
Proof.
 auto with qarith.
Qed.

Theorem Qeq_trans : forall x y z, x == y -> y == z -> x == z.
Proof.
unfold Qeq; intros.
apply Zmult_reg_l with (QDen y).
auto with qarith.
transitivity (Qnum x * QDen y * QDen z)%Z; try ring.
rewrite H.
transitivity (Qnum y * QDen z * QDen x)%Z; try ring.
rewrite H0; ring.
Qed.

Hint Resolve Qeq_refl : qarith.
Hint Resolve Qeq_sym : qarith.
Hint Resolve Qeq_trans : qarith.

(** In a word, [Qeq] is a setoid equality. *)

Instance Q_Setoid : Equivalence Qeq.
Proof. split; red; eauto with qarith. Qed.

(** Furthermore, this equality is decidable: *)

Theorem Qeq_dec : forall x y, {x==y} + {~ x==y}.
Proof.
 intros; case (Z_eq_dec (Qnum x * QDen y) (Qnum y * QDen x)); auto.
Defined.

Definition Qeq_bool x y :=
  (Zeq_bool (Qnum x * QDen y) (Qnum y * QDen x))%Z.

Definition Qle_bool x y :=
  (Zle_bool (Qnum x * QDen y) (Qnum y * QDen x))%Z.

Lemma Qeq_bool_iff : forall x y, Qeq_bool x y = true <-> x == y.
Proof.
  unfold Qeq_bool, Qeq; intros.
  symmetry; apply Zeq_is_eq_bool.
Qed.

Lemma Qeq_bool_eq : forall x y, Qeq_bool x y = true -> x == y.
Proof.
  intros; rewrite <- Qeq_bool_iff; auto.
Qed.

Lemma Qeq_eq_bool : forall x y, x == y -> Qeq_bool x y = true.
Proof.
  intros; rewrite Qeq_bool_iff; auto.
Qed.

Lemma Qeq_bool_neq : forall x y, Qeq_bool x y = false -> ~ x == y.
Proof.
  intros x y H; rewrite <- Qeq_bool_iff, H; discriminate.
Qed.

Lemma Qle_bool_iff : forall x y, Qle_bool x y = true <-> x <= y.
Proof.
  unfold Qle_bool, Qle; intros.
  symmetry; apply Zle_is_le_bool.
Qed.

Lemma Qle_bool_imp_le : forall x y, Qle_bool x y = true -> x <= y.
Proof.
  intros; rewrite <- Qle_bool_iff; auto.
Qed.

Theorem Qnot_eq_sym : forall x y, ~x == y -> ~y == x.
Proof.
 auto with qarith.
Qed.

Hint Resolve Qnot_eq_sym : qarith.

(** * Addition, multiplication and opposite *)

(** The addition, multiplication and opposite are defined
   in the straightforward way: *)

Definition Qplus (x y : Q) :=
  (Qnum x * QDen y + Qnum y * QDen x) # (Qden x * Qden y).

Definition Qmult (x y : Q) := (Qnum x * Qnum y) # (Qden x * Qden y).

Definition Qopp (x : Q) := (- Qnum x) # (Qden x).

Definition Qminus (x y : Q) := Qplus x (Qopp y).

Definition Qinv (x : Q) :=
  match Qnum x with
  | Z0 => 0
  | Zpos p => (QDen x)#p
  | Zneg p => (Zneg (Qden x))#p
  end.

Definition Qdiv (x y : Q) := Qmult x (Qinv y).

Infix "+" := Qplus : Q_scope.
Notation "- x" := (Qopp x) : Q_scope.
Infix "-" := Qminus : Q_scope.
Infix "*" := Qmult : Q_scope.
Notation "/ x" := (Qinv x) : Q_scope.
Infix "/" := Qdiv : Q_scope.

(** A light notation for [Zpos] *)

Notation " ' x " := (Zpos x) (at level 20, no associativity) : Z_scope.

Lemma Qmake_Qdiv : forall a b, a#b==inject_Z a/inject_Z ('b).
Proof.
intros a b.
unfold Qeq.
simpl.
ring.
Qed.

(** * Setoid compatibility results *)

Instance Qplus_comp : Proper (Qeq==>Qeq==>Qeq) Qplus.
Proof.
  unfold Qeq, Qplus; simpl.
  Open Scope Z_scope.
  intros (p1, p2) (q1, q2) H (r1, r2) (s1, s2) H0; simpl in *.
  simpl_mult; ring_simplify.
  replace (p1 * 'r2 * 'q2) with (p1 * 'q2 * 'r2) by ring.
  rewrite H.
  replace (r1 * 'p2 * 'q2 * 's2) with (r1 * 's2 * 'p2 * 'q2) by ring.
  rewrite H0.
  ring.
  Close Scope Z_scope.
Qed.

Instance Qopp_comp : Proper (Qeq==>Qeq) Qopp.
Proof.
  unfold Qeq, Qopp; simpl.
  Open Scope Z_scope.
  intros x y H; simpl.
  replace (- Qnum x * ' Qden y) with (- (Qnum x * ' Qden y)) by ring.
  rewrite H;  ring.
  Close Scope Z_scope.
Qed.

Instance Qminus_comp : Proper (Qeq==>Qeq==>Qeq) Qminus.
Proof.
  intros x x' Hx y y' Hy.
  unfold Qminus. rewrite Hx, Hy; auto with qarith.
Qed.

Instance Qmult_comp : Proper (Qeq==>Qeq==>Qeq) Qmult.
Proof.
  unfold Qeq; simpl.
  Open Scope Z_scope.
  intros (p1, p2) (q1, q2) H (r1, r2) (s1, s2) H0; simpl in *.
  intros; simpl_mult; ring_simplify.
  replace (q1 * s1 * 'p2) with (q1 * 'p2 * s1) by ring.
  rewrite <- H.
  replace (p1 * r1 * 'q2 * 's2) with (r1 * 's2 * p1 * 'q2) by ring.
  rewrite H0.
  ring.
  Close Scope Z_scope.
Qed.

Instance Qinv_comp : Proper (Qeq==>Qeq) Qinv.
Proof.
  unfold Qeq, Qinv; simpl.
  Open Scope Z_scope.
  intros (p1, p2) (q1, q2); simpl.
  case p1; simpl.
  intros.
  assert (q1 = 0).
  elim (Zmult_integral q1 ('p2)); auto with zarith.
  intros; discriminate.
  subst; auto.
  case q1; simpl; intros; try discriminate.
  rewrite (Pmult_comm p2 p); rewrite (Pmult_comm q2 p0); auto.
  case q1; simpl; intros; try discriminate.
  rewrite (Pmult_comm p2 p); rewrite (Pmult_comm q2 p0); auto.
  Close Scope Z_scope.
Qed.

Instance Qdiv_comp : Proper (Qeq==>Qeq==>Qeq) Qdiv.
Proof.
  intros x x' Hx y y' Hy; unfold Qdiv.
  rewrite Hx, Hy; auto with qarith.
Qed.

Instance Qcompare_comp : Proper (Qeq==>Qeq==>eq) Qcompare.
Proof.
  unfold Qeq, Qcompare.
  Open Scope Z_scope.
  intros (p1,p2) (q1,q2) H (r1,r2) (s1,s2) H'; simpl in *.
  rewrite <- (Zcompare_mult_compat (q2*s2) (p1*'r2)).
  rewrite <- (Zcompare_mult_compat (p2*r2) (q1*'s2)).
  change ('(q2*s2)) with ('q2 * 's2).
  change ('(p2*r2)) with ('p2 * 'r2).
  replace ('q2 * 's2 * (p1*'r2)) with ((p1*'q2)*'r2*'s2) by ring.
  rewrite H.
  replace ('q2 * 's2 * (r1*'p2)) with ((r1*'s2)*'q2*'p2) by ring.
  rewrite H'.
  f_equal; ring.
  Close Scope Z_scope.
Qed.

Instance Qle_comp : Proper (Qeq==>Qeq==>iff) Qle.
Proof.
  intros p q H r s H'. rewrite 2 Qle_alt, H, H'; auto with *.
Qed.

Instance Qlt_compat : Proper (Qeq==>Qeq==>iff) Qlt.
Proof.
  intros p q H r s H'. rewrite 2 Qlt_alt, H, H'; auto with *.
Qed.

Instance Qeqb_comp : Proper (Qeq==>Qeq==>eq) Qeq_bool.
Proof.
 intros p q H r s H'; apply eq_true_iff_eq.
 rewrite 2 Qeq_bool_iff, H, H'; split; auto with qarith.
Qed.

Instance Qleb_comp : Proper (Qeq==>Qeq==>eq) Qle_bool.
Proof.
 intros p q H r s H'; apply eq_true_iff_eq.
 rewrite 2 Qle_bool_iff, H, H'; split; auto with qarith.
Qed.


(** [0] and [1] are apart *)

Lemma Q_apart_0_1 : ~ 1 == 0.
Proof.
  unfold Qeq; auto with qarith.
Qed.

(** * Properties of [Qadd] *)

(** Addition is associative: *)

Theorem Qplus_assoc : forall x y z, x+(y+z)==(x+y)+z.
Proof.
  intros (x1, x2) (y1, y2) (z1, z2).
  unfold Qeq, Qplus; simpl; simpl_mult; ring.
Qed.

(** [0] is a neutral element for addition: *)

Lemma Qplus_0_l : forall x, 0+x == x.
Proof.
  intros (x1, x2); unfold Qeq, Qplus; simpl; ring.
Qed.

Lemma Qplus_0_r : forall x, x+0 == x.
Proof.
  intros (x1, x2); unfold Qeq, Qplus; simpl.
  rewrite Pmult_comm; simpl; ring.
Qed.

(** Commutativity of addition: *)

Theorem Qplus_comm : forall x y, x+y == y+x.
Proof.
  intros (x1, x2); unfold Qeq, Qplus; simpl.
  intros; rewrite Pmult_comm; ring.
Qed.


(** * Properties of [Qopp] *)

Lemma Qopp_involutive : forall q, - -q == q.
Proof.
  red; simpl; intros; ring.
Qed.

Theorem Qplus_opp_r : forall q, q+(-q) == 0.
Proof.
  red; simpl; intro; ring.
Qed.


(** * Properties of [Qmult] *)

(** Multiplication is associative: *)

Theorem Qmult_assoc : forall n m p, n*(m*p)==(n*m)*p.
Proof.
  intros; red; simpl; rewrite Pmult_assoc; ring.
Qed.

(** multiplication and zero *)

Lemma Qmult_0_l : forall x , 0*x == 0.
Proof.
  intros; compute; reflexivity.
Qed.

Lemma Qmult_0_r : forall x , x*0 == 0.
Proof.
  intros; red; simpl; ring.
Qed.

(** [1] is a neutral element for multiplication: *)

Lemma Qmult_1_l : forall n, 1*n == n.
Proof.
  intro; red; simpl; destruct (Qnum n); auto.
Qed.

Theorem Qmult_1_r : forall n, n*1==n.
Proof.
  intro; red; simpl.
  rewrite Zmult_1_r with (n := Qnum n).
  rewrite Pmult_comm; simpl; trivial.
Qed.

(** Commutativity of multiplication *)

Theorem Qmult_comm : forall x y, x*y==y*x.
Proof.
  intros; red; simpl; rewrite Pmult_comm; ring.
Qed.

(** Distributivity over [Qadd] *)

Theorem Qmult_plus_distr_r : forall x y z, x*(y+z)==(x*y)+(x*z).
Proof.
  intros (x1, x2) (y1, y2) (z1, z2).
  unfold Qeq, Qmult, Qplus; simpl; simpl_mult; ring.
Qed.

Theorem Qmult_plus_distr_l : forall x y z, (x+y)*z==(x*z)+(y*z).
Proof.
  intros (x1, x2) (y1, y2) (z1, z2).
  unfold Qeq, Qmult, Qplus; simpl; simpl_mult; ring.
Qed.

(** Integrality *)

Theorem Qmult_integral : forall x y, x*y==0 -> x==0 \/ y==0.
Proof.
  intros (x1,x2) (y1,y2).
  unfold Qeq, Qmult; simpl; intros.
  destruct (Zmult_integral (x1*1)%Z (y1*1)%Z); auto.
  rewrite <- H; ring.
Qed.

Theorem Qmult_integral_l : forall x y, ~ x == 0 -> x*y == 0 -> y == 0.
Proof.
  intros (x1, x2) (y1, y2).
  unfold Qeq, Qmult; simpl; intros.
  apply Zmult_integral_l with x1; auto with zarith.
  rewrite <- H0; ring.
Qed.

(** * Inverse and division. *)

Lemma Qinv_involutive : forall q, (/ / q) == q.
Proof.
intros [[|n|n] d]; red; simpl; reflexivity.
Qed.

Theorem Qmult_inv_r : forall x, ~ x == 0 -> x*(/x) == 1.
Proof.
  intros (x1, x2); unfold Qeq, Qdiv, Qmult; case x1; simpl;
    intros; simpl_mult; try ring.
  elim H; auto.
Qed.

Lemma Qinv_mult_distr : forall p q, / (p * q) == /p * /q.
Proof.
  intros (x1,x2) (y1,y2); unfold Qeq, Qinv, Qmult; simpl.
  destruct x1; simpl; auto;
    destruct y1; simpl; auto.
Qed.

Theorem Qdiv_mult_l : forall x y, ~ y == 0 -> (x*y)/y == x.
Proof.
  intros; unfold Qdiv.
  rewrite <- (Qmult_assoc x y (Qinv y)).
  rewrite (Qmult_inv_r y H).
  apply Qmult_1_r.
Qed.

Theorem Qmult_div_r : forall x y, ~ y == 0 -> y*(x/y) == x.
Proof.
  intros; unfold Qdiv.
  rewrite (Qmult_assoc y x (Qinv y)).
  rewrite (Qmult_comm y x).
  fold (Qdiv (Qmult x y) y).
  apply Qdiv_mult_l; auto.
Qed.

(** * Properties of order upon Q. *)

Lemma Qle_refl : forall x, x<=x.
Proof.
  unfold Qle; auto with zarith.
Qed.

Lemma Qle_antisym : forall x y, x<=y -> y<=x -> x==y.
Proof.
  unfold Qle, Qeq; auto with zarith.
Qed.

Lemma Qle_trans : forall x y z, x<=y -> y<=z -> x<=z.
Proof.
  unfold Qle; intros (x1, x2) (y1, y2) (z1, z2); simpl; intros.
  Open Scope Z_scope.
  apply Zmult_le_reg_r with ('y2).
  red; trivial.
  apply Zle_trans with (y1 * 'x2 * 'z2).
  replace (x1 * 'z2 * 'y2) with (x1 * 'y2 * 'z2) by ring.
  apply Zmult_le_compat_r; auto with zarith.
  replace (y1 * 'x2 * 'z2) with (y1 * 'z2 * 'x2) by ring.
  replace (z1 * 'x2 * 'y2) with (z1 * 'y2 * 'x2) by ring.
  apply Zmult_le_compat_r; auto with zarith.
  Close Scope Z_scope.
Qed.

Hint Resolve Qle_trans : qarith.

Lemma Qlt_irrefl : forall x, ~x<x.
Proof.
 unfold Qlt. auto with zarith.
Qed.

Lemma Qlt_not_eq : forall x y, x<y -> ~ x==y.
Proof.
  unfold Qlt, Qeq; auto with zarith.
Qed.

(** Large = strict or equal *)

Lemma Qle_lteq : forall x y, x<=y <-> x<y \/ x==y.
Proof.
 intros.
 rewrite Qeq_alt, Qle_alt, Qlt_alt.
 destruct (x ?= y); intuition; discriminate.
Qed.

Lemma Qlt_le_weak : forall x y, x<y -> x<=y.
Proof.
  unfold Qle, Qlt; auto with zarith.
Qed.

Lemma Qle_lt_trans : forall x y z, x<=y -> y<z -> x<z.
Proof.
  unfold Qle, Qlt; intros (x1, x2) (y1, y2) (z1, z2); simpl; intros.
  Open Scope Z_scope.
  apply Zgt_lt.
  apply Zmult_gt_reg_r with ('y2).
  red; trivial.
  apply Zgt_le_trans with (y1 * 'x2 * 'z2).
  replace (y1 * 'x2 * 'z2) with (y1 * 'z2 * 'x2) by ring.
  replace (z1 * 'x2 * 'y2) with (z1 * 'y2 * 'x2) by ring.
  apply Zmult_gt_compat_r; auto with zarith.
  replace (x1 * 'z2 * 'y2) with (x1 * 'y2 * 'z2) by ring.
  apply Zmult_le_compat_r; auto with zarith.
  Close Scope Z_scope.
Qed.

Lemma Qlt_le_trans : forall x y z, x<y -> y<=z -> x<z.
Proof.
  unfold Qle, Qlt; intros (x1, x2) (y1, y2) (z1, z2); simpl; intros.
  Open Scope Z_scope.
  apply Zgt_lt.
  apply Zmult_gt_reg_r with ('y2).
  red; trivial.
  apply Zle_gt_trans with (y1 * 'x2 * 'z2).
  replace (y1 * 'x2 * 'z2) with (y1 * 'z2 * 'x2) by ring.
  replace (z1 * 'x2 * 'y2) with (z1 * 'y2 * 'x2) by ring.
  apply Zmult_le_compat_r; auto with zarith.
  replace (x1 * 'z2 * 'y2) with (x1 * 'y2 * 'z2) by ring.
  apply Zmult_gt_compat_r; auto with zarith.
  Close Scope Z_scope.
Qed.

Lemma Qlt_trans : forall x y z, x<y -> y<z -> x<z.
Proof.
  intros.
  apply Qle_lt_trans with y; auto.
  apply Qlt_le_weak; auto.
Qed.

(** [x<y] iff [~(y<=x)] *)

Lemma Qnot_lt_le : forall x y, ~ x<y -> y<=x.
Proof.
  unfold Qle, Qlt; auto with zarith.
Qed.

Lemma Qnot_le_lt : forall x y, ~ x<=y -> y<x.
Proof.
  unfold Qle, Qlt; auto with zarith.
Qed.

Lemma Qlt_not_le : forall x y, x<y -> ~ y<=x.
Proof.
  unfold Qle, Qlt; auto with zarith.
Qed.

Lemma Qle_not_lt : forall x y, x<=y -> ~ y<x.
Proof.
  unfold Qle, Qlt; auto with zarith.
Qed.

Lemma Qle_lt_or_eq : forall x y, x<=y -> x<y \/ x==y.
Proof.
  unfold Qle, Qlt, Qeq; intros; apply Zle_lt_or_eq; auto.
Qed.

Hint Resolve Qle_not_lt Qlt_not_le Qnot_le_lt Qnot_lt_le
 Qlt_le_weak Qlt_not_eq Qle_antisym Qle_refl: qarith.

(** Some decidability results about orders. *)

Lemma Q_dec : forall x y, {x<y} + {y<x} + {x==y}.
Proof.
  unfold Qlt, Qle, Qeq; intros.
  exact (Z_dec' (Qnum x * QDen y) (Qnum y * QDen x)).
Defined.

Lemma Qlt_le_dec : forall x y, {x<y} + {y<=x}.
Proof.
  unfold Qlt, Qle; intros.
  exact (Z_lt_le_dec (Qnum x * QDen y) (Qnum y * QDen x)).
Defined.

(** Compatibility of operations with respect to order. *)

Lemma Qopp_le_compat : forall p q, p<=q -> -q <= -p.
Proof.
  intros (a1,a2) (b1,b2); unfold Qle, Qlt; simpl.
  do 2 rewrite <- Zopp_mult_distr_l; omega.
Qed.

Hint Resolve Qopp_le_compat : qarith.

Lemma Qle_minus_iff : forall p q, p <= q <-> 0 <= q+-p.
Proof.
  intros (x1,x2) (y1,y2); unfold Qle; simpl.
  rewrite <- Zopp_mult_distr_l.
  split; omega.
Qed.

Lemma Qlt_minus_iff : forall p q, p < q <-> 0 < q+-p.
Proof.
  intros (x1,x2) (y1,y2); unfold Qlt; simpl.
  rewrite <- Zopp_mult_distr_l.
  split; omega.
Qed.

Lemma Qplus_le_compat :
  forall x y z t, x<=y -> z<=t -> x+z <= y+t.
Proof.
  unfold Qplus, Qle; intros (x1, x2) (y1, y2) (z1, z2) (t1, t2);
    simpl; simpl_mult.
  Open Scope Z_scope.
  intros.
  match goal with |- ?a <= ?b => ring_simplify a b end.
  rewrite Zplus_comm.
  apply Zplus_le_compat.
  match goal with |- ?a <= ?b => ring_simplify z1 t1 ('z2) ('t2) a b end.
  auto with zarith.
  match goal with |- ?a <= ?b => ring_simplify x1 y1 ('x2) ('y2) a b end.
  auto with zarith.
  Close Scope Z_scope.
Qed.

Lemma Qmult_le_compat_r : forall x y z, x <= y -> 0 <= z -> x*z <= y*z.
Proof.
  intros (a1,a2) (b1,b2) (c1,c2); unfold Qle, Qlt; simpl.
  Open Scope Z_scope.
  intros; simpl_mult.
  replace (a1*c1*('b2*'c2)) with ((a1*'b2)*(c1*'c2)) by ring.
  replace (b1*c1*('a2*'c2)) with ((b1*'a2)*(c1*'c2)) by ring.
  apply Zmult_le_compat_r; auto with zarith.
  Close Scope Z_scope.
Qed.

Lemma Qmult_lt_0_le_reg_r : forall x y z, 0 <  z  -> x*z <= y*z -> x <= y.
Proof.
  intros (a1,a2) (b1,b2) (c1,c2); unfold Qle, Qlt; simpl.
  Open Scope Z_scope.
  simpl_mult.
  replace (a1*c1*('b2*'c2)) with ((a1*'b2)*(c1*'c2)) by ring.
  replace (b1*c1*('a2*'c2)) with ((b1*'a2)*(c1*'c2)) by ring.
  intros; apply Zmult_le_reg_r with (c1*'c2); auto with zarith.
  Close Scope Z_scope.
Qed.

Lemma Qmult_lt_compat_r : forall x y z, 0 < z  -> x < y -> x*z < y*z.
Proof.
  intros (a1,a2) (b1,b2) (c1,c2); unfold Qle, Qlt; simpl.
  Open Scope Z_scope.
  intros; simpl_mult.
  replace (a1*c1*('b2*'c2)) with ((a1*'b2)*(c1*'c2)) by ring.
  replace (b1*c1*('a2*'c2)) with ((b1*'a2)*(c1*'c2)) by ring.
  apply Zmult_lt_compat_r; auto with zarith.
  apply Zmult_lt_0_compat.
  omega.
  compute; auto.
  Close Scope Z_scope.
Qed.

Lemma Qmult_le_0_compat : forall a b, 0 <= a -> 0 <= b -> 0 <= a*b.
Proof.
intros a b Ha Hb.
unfold Qle in *.
simpl in *.
auto with *.
Qed.

Lemma Qinv_le_0_compat : forall a, 0 <= a -> 0 <= /a.
Proof.
intros [[|n|n] d] Ha; assumption.
Qed.

Lemma Qle_shift_div_l : forall a b c,
 0 < c -> a*c <= b -> a <= b/c.
Proof.
intros a b c Hc H.
apply Qmult_lt_0_le_reg_r with (c).
 assumption.
setoid_replace (b/c*c) with (c*(b/c)) by apply Qmult_comm.
rewrite Qmult_div_r; try assumption.
auto with *.
Qed.

Lemma Qle_shift_inv_l : forall a c,
 0 < c -> a*c <= 1 -> a <= /c.
Proof.
intros a c Hc H.
setoid_replace (/c) with (1*/c) by (symmetry; apply Qmult_1_l).
change (a <= 1/c).
apply Qle_shift_div_l; assumption.
Qed.

Lemma Qle_shift_div_r : forall a b c,
 0 < b -> a <= c*b -> a/b <= c.
Proof.
intros a b c Hc H.
apply Qmult_lt_0_le_reg_r with b.
 assumption.
setoid_replace (a/b*b) with (b*(a/b)) by apply Qmult_comm.
rewrite Qmult_div_r; try assumption.
auto with *.
Qed.

Lemma Qle_shift_inv_r : forall b c,
 0 < b -> 1 <= c*b -> /b <= c.
Proof.
intros b c Hc H.
setoid_replace (/b) with (1*/b) by (symmetry; apply Qmult_1_l).
change (1/b <= c).
apply Qle_shift_div_r; assumption.
Qed.

Lemma Qinv_lt_0_compat : forall a, 0 < a -> 0 < /a.
Proof.
intros [[|n|n] d] Ha; assumption.
Qed.

Lemma Qlt_shift_div_l : forall a b c,
 0 < c -> a*c < b -> a < b/c.
Proof.
intros a b c Hc H.
apply Qnot_le_lt.
intros H0.
apply (Qlt_not_le _ _ H).
apply Qmult_lt_0_le_reg_r with (/c).
 apply Qinv_lt_0_compat.
 assumption.
setoid_replace (a*c/c) with (a) by (apply Qdiv_mult_l; auto with *).
assumption.
Qed.

Lemma Qlt_shift_inv_l : forall a c,
 0 < c -> a*c < 1 -> a < /c.
Proof.
intros a c Hc H.
setoid_replace (/c) with (1*/c) by (symmetry; apply Qmult_1_l).
change (a < 1/c).
apply Qlt_shift_div_l; assumption.
Qed.

Lemma Qlt_shift_div_r : forall a b c,
 0 < b -> a < c*b -> a/b < c.
Proof.
intros a b c Hc H.
apply Qnot_le_lt.
intros H0.
apply (Qlt_not_le _ _ H).
apply Qmult_lt_0_le_reg_r with (/b).
 apply Qinv_lt_0_compat.
 assumption.
setoid_replace (c*b/b) with (c) by (apply Qdiv_mult_l; auto with *).
assumption.
Qed.

Lemma Qlt_shift_inv_r : forall b c,
 0 < b -> 1 < c*b -> /b < c.
Proof.
intros b c Hc H.
setoid_replace (/b) with (1*/b) by (symmetry; apply Qmult_1_l).
change (1/b < c).
apply Qlt_shift_div_r; assumption.
Qed.

(** * Rational to the n-th power *)

Definition Qpower_positive (q:Q)(p:positive) : Q :=
 pow_pos Qmult q p.

Instance Qpower_positive_comp : Proper (Qeq==>eq==>Qeq) Qpower_positive.
Proof.
intros x x' Hx y y' Hy. rewrite <-Hy; clear y' Hy.
unfold Qpower_positive.
induction y; simpl;
try rewrite IHy;
try rewrite Hx;
reflexivity.
Qed.

Definition Qpower (q:Q) (z:Z) :=
    match z with
      | Zpos p => Qpower_positive q p
      | Z0 => 1
      | Zneg p => /Qpower_positive q p
    end.

Notation " q ^ z " := (Qpower q z) : Q_scope.

Instance Qpower_comp : Proper (Qeq==>eq==>Qeq) Qpower.
Proof.
intros x x' Hx y y' Hy. rewrite <- Hy; clear y' Hy.
destruct y; simpl; rewrite ?Hx; auto with *.
Qed.
