(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Export ZArith.
Require Export ZArithRing.
Require Export Setoid.

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

Notation " 'QDen'  p " := (Zpos (Qden p)) (at level 20, no associativity) : Q_scope.
Notation " 0 " := (0#1) : Q_scope.
Notation " 1 " := (1#1) : Q_scope.

Definition Qeq (p q : Q) := (Qnum p * QDen q)%Z = (Qnum q * QDen p)%Z.
Definition Qle (x y : Q) := (Qnum x * QDen y <= Qnum y * QDen x)%Z.
Definition Qlt (x y : Q) := (Qnum x * QDen y < Qnum y * QDen x)%Z.
Notation Qgt := (fun x y : Q => Qlt y x).
Notation Qge := (fun x y : Q => Qle y x).

Infix "==" := Qeq (at level 70, no associativity) : Q_scope. 
Infix "<" := Qlt : Q_scope.
Infix ">" := Qgt : Q_scope.
Infix "<=" := Qle : Q_scope.
Infix ">=" := Qge : Q_scope.
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
split; intros; swap H.
rewrite Zcompare_Gt_Lt_antisym; auto.
rewrite Zcompare_Gt_Lt_antisym in H0; auto.
Qed.

Hint Unfold Qeq Qlt Qle: qarith.
Hint Extern 5 (?X1 <> ?X2) => intro; discriminate: qarith.

(** Properties of equality. *)

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
unfold Qeq in |- *; intros.
apply Zmult_reg_l with (QDen y). 
auto with qarith.
ring; rewrite H; ring.
rewrite Zmult_assoc; rewrite H0; ring.
Qed.

(** Furthermore, this equality is decidable: *)

Theorem Qeq_dec : forall x y, {x==y} + {~ x==y}.
Proof.
 intros; case (Z_eq_dec (Qnum x * QDen y) (Qnum y * QDen x)); auto.
Defined.

(** We now consider [Q] seen as a setoid. *)

Definition Q_Setoid : Setoid_Theory Q Qeq.
Proof.
 split; unfold Qeq in |- *; auto; apply Qeq_trans.
Qed.

Add Setoid Q Qeq Q_Setoid as Qsetoid.

Hint Resolve (Seq_refl Q Qeq Q_Setoid): qarith.
Hint Resolve (Seq_sym Q Qeq Q_Setoid): qarith.
Hint Resolve (Seq_trans Q Qeq Q_Setoid): qarith.

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

(** Setoid compatibility results *)

Add Morphism Qplus : Qplus_comp. 
Proof.
unfold Qeq, Qplus; simpl.
Open Scope Z_scope.
intros (p1, p2) (q1, q2) H (r1, r2) (s1, s2) H0; simpl in *.
simpl_mult; ring.
replace (p1 * ('s2 * 'q2)) with (p1 * 'q2 * 's2) by ring.
rewrite H.
replace ('s2 * ('q2 * r1)) with (r1 * 's2 * 'q2) by ring.
rewrite H0.
ring.
Open Scope Q_scope.
Qed.

Add Morphism Qopp : Qopp_comp.
Proof.
unfold Qeq, Qopp; simpl.
intros; ring; rewrite H; ring.
Qed.

Add Morphism Qminus : Qminus_comp.
Proof.
intros.
unfold Qminus. 
rewrite H; rewrite H0; auto with qarith.
Qed.

Add Morphism Qmult : Qmult_comp.
Proof.
unfold Qeq; simpl.
Open Scope Z_scope.
intros (p1, p2) (q1, q2) H (r1, r2) (s1, s2) H0; simpl in *.
intros; simpl_mult; ring.
replace ('p2 * (q1 * s1)) with (q1 * 'p2 * s1) by ring.
rewrite <- H.
replace ('s2 * ('q2 * r1)) with (r1 * 's2 * 'q2) by ring.
rewrite H0.
ring.
Open Scope Q_scope.
Qed.

Add Morphism Qinv : Qinv_comp.
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
Open Scope Q_scope.
Qed.

Add Morphism Qdiv : Qdiv_comp.
Proof.
intros; unfold Qdiv.
rewrite H; rewrite H0; auto with qarith.
Qed.

Add Morphism Qle with signature Qeq ==> Qeq ==> iff as Qle_comp.
Proof.
cut (forall x1 x2, x1==x2 -> forall x3 x4, x3==x4 -> x1<=x3 -> x2<=x4).
split; apply H; assumption || (apply Qeq_sym ; assumption).

unfold Qeq, Qle; simpl.
Open Scope Z_scope.
intros (p1, p2) (q1, q2) H (r1, r2) (s1, s2) H0 H1; simpl in *.
apply Zmult_le_reg_r with ('p2).
unfold Zgt; auto.
replace (q1 * 's2 * 'p2) with (q1 * 'p2 * 's2) by ring.
rewrite <- H.
apply Zmult_le_reg_r with ('r2).
unfold Zgt; auto.
replace (s1 * 'q2 * 'p2 * 'r2) with (s1 * 'r2 * 'q2 * 'p2) by ring.
rewrite <- H0.
replace (p1 * 'q2 * 's2 * 'r2) with ('q2 * 's2 * (p1 * 'r2)) by ring.
replace (r1 * 's2 * 'q2 * 'p2) with ('q2 * 's2 * (r1 * 'p2)) by ring.
auto with zarith.
Open Scope Q_scope.
Qed.

Add Morphism Qlt with signature Qeq ==> Qeq ==> iff as  Qlt_comp.
Proof.
cut (forall x1 x2, x1==x2 -> forall x3 x4, x3==x4 -> x1<x3 -> x2<x4).
split; apply H; assumption || (apply Qeq_sym ; assumption).

unfold Qeq, Qlt; simpl.
Open Scope Z_scope.
intros (p1, p2) (q1, q2) H (r1, r2) (s1, s2) H0 H1; simpl in *.
apply Zgt_lt.
generalize (Zlt_gt _ _ H1); clear H1; intro H1.
apply Zmult_gt_reg_r with ('p2); auto with zarith.
replace (q1 * 's2 * 'p2) with (q1 * 'p2 * 's2) by ring.
rewrite <- H.
apply Zmult_gt_reg_r with ('r2); auto with zarith.
replace (s1 * 'q2 * 'p2 * 'r2) with (s1 * 'r2 * 'q2 * 'p2) by ring.
rewrite <- H0.
replace (p1 * 'q2 * 's2 * 'r2) with ('q2 * 's2 * (p1 * 'r2)) by ring.
replace (r1 * 's2 * 'q2 * 'p2) with ('q2 * 's2 * (r1 * 'p2)) by ring. 
apply Zlt_gt.
apply Zmult_gt_0_lt_compat_l; auto with zarith.
Open Scope Q_scope.
Qed.


Lemma Qcompare_egal_dec: forall n m p q : Q, 
 (n<m -> p<q) -> (n==m -> p==q) -> (n>m -> p>q) -> ((n?=m) = (p?=q)).
Proof.
intros.
do 2 rewrite Qeq_alt in H0.
unfold Qeq, Qlt, Qcompare in *.
apply Zcompare_egal_dec; auto.
omega.
Qed.


Add Morphism Qcompare : Qcompare_comp.
Proof.
intros; apply Qcompare_egal_dec; rewrite H; rewrite H0; auto.
Qed.


(** [0] and [1] are apart *)

Lemma Q_apart_0_1 : ~ 1 == 0.
Proof.
 unfold Qeq; auto with qarith.
Qed.

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

(** Properties of [Qopp] *)

Lemma Qopp_involutive : forall q, - -q == q.
Proof.
 red; simpl; intros; ring.
Qed.

Theorem Qplus_opp_r : forall q, q+(-q) == 0.
Proof.
 red; simpl; intro; ring.
Qed.

(** Multiplication is associative: *)

Theorem Qmult_assoc : forall n m p, n*(m*p)==(n*m)*p.
Proof.
 intros; red; simpl; rewrite Pmult_assoc; ring.
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

(** Distributivity *)

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

(** Inverse and division. *) 

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

(** Properties of order upon Q. *)

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
Open Scope Q_scope.
Qed.

Lemma Qlt_not_eq : forall x y, x<y -> ~ x==y.
Proof.
unfold Qlt, Qeq; auto with zarith.
Qed.

(** Large = strict or equal *)

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
Open Scope Q_scope.
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
Open Scope Q_scope.
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
match goal with |- ?a <= ?b => ring a; ring b end.
apply Zplus_le_compat.
replace ('t2 * ('y2 * (z1 * 'x2))) with (z1 * 't2 * ('y2 * 'x2)) by ring.
replace ('z2 * ('x2 * (t1 * 'y2))) with (t1 * 'z2 * ('y2 * 'x2)) by ring.
apply Zmult_le_compat_r; auto with zarith.
replace ('t2 * ('y2 * ('z2 * x1))) with (x1 * 'y2 * ('z2 * 't2)) by ring.
replace ('z2 * ('x2 * ('t2 * y1))) with (y1 * 'x2 * ('z2 * 't2)) by ring.
apply Zmult_le_compat_r; auto with zarith.
Open Scope Q_scope.
Qed.

Lemma Qmult_le_compat_r : forall x y z, x <= y -> 0 <= z -> x*z <= y*z.
Proof.
intros (a1,a2) (b1,b2) (c1,c2); unfold Qle, Qlt; simpl.
Open Scope Z_scope.
intros; simpl_mult.
replace (a1*c1*('b2*'c2)) with ((a1*'b2)*(c1*'c2)) by ring.
replace (b1*c1*('a2*'c2)) with ((b1*'a2)*(c1*'c2)) by ring.
apply Zmult_le_compat_r; auto with zarith.
Open Scope Q_scope.
Qed.

Lemma Qmult_lt_0_le_reg_r : forall x y z, 0 <  z  -> x*z <= y*z -> x <= y.
Proof.
intros (a1,a2) (b1,b2) (c1,c2); unfold Qle, Qlt; simpl.
Open Scope Z_scope.
simpl_mult.
replace (a1*c1*('b2*'c2)) with ((a1*'b2)*(c1*'c2)) by ring.
replace (b1*c1*('a2*'c2)) with ((b1*'a2)*(c1*'c2)) by ring.
intros; apply Zmult_le_reg_r with (c1*'c2); auto with zarith.
Open Scope Q_scope.
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
Open Scope Q_scope.
Qed.

(** Rational to the n-th power *)

Fixpoint Qpower (q:Q)(n:nat) { struct n } : Q := 
 match n with 
  | O => 1
  | S n => q * (Qpower q n)
 end. 

Notation " q ^ n " := (Qpower q n) : Q_scope.

Lemma Qpower_1 : forall n, 1^n == 1.
Proof.
induction n; simpl; auto with qarith.
rewrite IHn; auto with qarith.
Qed.

Lemma Qpower_0 : forall n, n<>O -> 0^n == 0.
Proof.
destruct n; simpl.
destruct 1; auto.
intros. 
compute; auto.
Qed.

Lemma Qpower_pos : forall p n, 0 <= p -> 0 <= p^n.
Proof.
induction n; simpl; auto with qarith.
intros; compute; intro; discriminate.
intros.
apply Qle_trans with (0*(p^n)).
compute; intro; discriminate.
apply Qmult_le_compat_r; auto.
Qed.

Lemma Qinv_power_n : forall n p, (1#p)^n == /(inject_Z ('p))^n.
Proof.
induction n.
compute; auto.
simpl.
intros; rewrite IHn; clear IHn.
unfold Qdiv; rewrite Qinv_mult_distr.
setoid_replace (1#p) with (/ inject_Z ('p)).
apply Qeq_refl.
compute; auto.
Qed.


