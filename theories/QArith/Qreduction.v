(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** * Normalisation functions for rational numbers. *)

Require Export QArith_base.
Require Export Znumtheory.

(** First, a function that (tries to) build a positive back from a Z. *)

Definition Z2P (z : Z) :=
  match z with
  | Z0 => 1%positive
  | Zpos p => p
  | Zneg p => p
  end.

Lemma Z2P_correct : forall z : Z, (0 < z)%Z -> Zpos (Z2P z) = z.
Proof.
 simple destruct z; simpl in |- *; auto; intros; discriminate.
Qed.

Lemma Z2P_correct2 : forall z : Z, 0%Z <> z -> Zpos (Z2P z) = Zabs z.
Proof.
 simple destruct z; simpl in |- *; auto; intros; elim H; auto.
Qed.

(** A simple cancelation by powers of two *)

Fixpoint Pfactor_twos (p p':positive) {struct p} : (positive*positive) := 
 match p, p' with 
  | xO p, xO p' => Pfactor_twos p p'
  | _, _ => (p,p')
 end.

Definition Qfactor_twos (q:Q) := 
 let (p,q) := q in 
 match p with 
   | Z0 => 0
   | Zpos p => let (p,q) := Pfactor_twos p q in (Zpos p)#q
   | Zneg p => let (p,q) := Pfactor_twos p q in (Zneg p)#q
 end.

Lemma Pfactor_twos_correct : forall p p', 
   (p*(snd (Pfactor_twos p p')))%positive = 
   (p'*(fst (Pfactor_twos p p')))%positive.
Proof.
induction p; intros.
simpl snd; simpl fst; rewrite Pmult_comm; auto.
destruct p'.
simpl snd; simpl fst; rewrite Pmult_comm; auto.
simpl; f_equal; auto.
simpl snd; simpl fst; rewrite Pmult_comm; auto.
simpl snd; simpl fst; rewrite Pmult_comm; auto.
Qed.

Lemma Qfactor_twos_correct : forall q, Qfactor_twos q == q.
Proof.
intros (p,q).
destruct p.
red; simpl; auto.
simpl.
generalize (Pfactor_twos_correct p q); destruct (Pfactor_twos p q).
red; simpl.
intros; f_equal.
rewrite H; apply Pmult_comm.
simpl.
generalize (Pfactor_twos_correct p q); destruct (Pfactor_twos p q).
red; simpl.
intros; f_equal.
rewrite H; apply Pmult_comm.
Qed.
Hint Resolve Qfactor_twos_correct.

(** Simplification of fractions using [Zgcd].
  This version can compute within Coq. *)

Definition Qred (q:Q) := 
  let (q1,q2) := Qfactor_twos q in 
  let (r1,r2) := snd (Zggcd q1 (Zpos q2)) in r1#(Z2P r2).

Lemma Qred_correct : forall q, (Qred q) == q.
Proof.
intros; apply Qeq_trans with (Qfactor_twos q); auto.
unfold Qred.
destruct (Qfactor_twos q) as (n,d); red; simpl.
generalize (Zggcd_gcd n ('d)) (Zgcd_is_pos n ('d)) 
  (Zgcd_is_gcd n ('d)) (Zggcd_correct_divisors n ('d)).
destruct (Zggcd n (Zpos d)) as (g,(nn,dd)); simpl.
Open Scope Z_scope.
intuition.
rewrite <- H in H0,H1; clear H.
rewrite H3; rewrite H4.
assert (0 <> g).
  intro; subst g; discriminate.

assert (0 < dd).
  apply Zmult_gt_0_lt_0_reg_r with g.
  omega.
  rewrite Zmult_comm.
  rewrite <- H4; compute; auto.
rewrite Z2P_correct; auto.
ring.
Qed.

Lemma Qred_complete : forall p q,  p==q -> Qred p = Qred q.
Proof.
intros.
assert (Qfactor_twos p == Qfactor_twos q).
 apply Qeq_trans with p; auto.
 apply Qeq_trans with q; auto.
 symmetry; auto.
clear H.
unfold Qred.
destruct (Qfactor_twos p) as (a,b); 
destruct (Qfactor_twos q) as (c,d); clear p q.
unfold Qeq in *; simpl in *.
Open Scope Z_scope.
generalize (Zggcd_gcd a ('b)) (Zgcd_is_gcd a ('b)) 
 (Zgcd_is_pos a ('b)) (Zggcd_correct_divisors a ('b)).
destruct (Zggcd a (Zpos b)) as (g,(aa,bb)).
generalize (Zggcd_gcd c ('d)) (Zgcd_is_gcd c ('d)) 
 (Zgcd_is_pos c ('d)) (Zggcd_correct_divisors c ('d)).
destruct (Zggcd c (Zpos d)) as (g',(cc,dd)).
simpl.
intro H; rewrite <- H; clear H.
intros Hg'1 Hg'2 (Hg'3,Hg'4).
intro H; rewrite <- H; clear H.
intros Hg1 Hg2 (Hg3,Hg4).
intros.
assert (g <> 0).
  intro; subst g; discriminate.
assert (g' <> 0).
  intro; subst g'; discriminate.
elim (rel_prime_cross_prod aa bb cc dd).
congruence.
unfold rel_prime in |- *.
(*rel_prime*)
constructor.
exists aa; auto with zarith.
exists bb; auto with zarith.
intros.
inversion Hg1.
destruct (H6 (g*x)).
rewrite Hg3.
destruct H2 as (xa,Hxa); exists xa; rewrite Hxa; ring.
rewrite Hg4.
destruct H3 as (xb,Hxb); exists xb; rewrite Hxb; ring.
exists q.
apply Zmult_reg_l with g; auto.
pattern g at 1; rewrite H7; ring.
(* /rel_prime *)
unfold rel_prime in |- *.
(* rel_prime *)
constructor.
exists cc; auto with zarith.
exists dd; auto with zarith.
intros.
inversion Hg'1.
destruct (H6 (g'*x)).
rewrite Hg'3.
destruct H2 as (xc,Hxc); exists xc; rewrite Hxc; ring.
rewrite Hg'4.
destruct H3 as (xd,Hxd); exists xd; rewrite Hxd; ring.
exists q.
apply Zmult_reg_l with g'; auto.
pattern g' at 1; rewrite H7; ring.
(* /rel_prime *)
assert (0<bb); [|auto with zarith].
  apply Zmult_gt_0_lt_0_reg_r with g.
  omega.
  rewrite Zmult_comm.
  rewrite <- Hg4; compute; auto.
assert (0<dd); [|auto with zarith].
  apply Zmult_gt_0_lt_0_reg_r with g'.
  omega.
  rewrite Zmult_comm.
  rewrite <- Hg'4; compute; auto.
apply Zmult_reg_l with (g'*g).
intro H2; elim (Zmult_integral _ _ H2); auto.
replace (g'*g*(aa*dd)) with ((g*aa)*(g'*dd)); [|ring].
replace (g'*g*(bb*cc)) with ((g'*cc)*(g*bb)); [|ring].
rewrite <- Hg3; rewrite <- Hg4; rewrite <- Hg'3; rewrite <- Hg'4; auto.
Open Scope Q_scope.
Qed.

Add Morphism Qred : Qred_comp. 
Proof.
intros q q' H.
rewrite (Qred_correct q); auto.
rewrite (Qred_correct q'); auto.
Qed.

(** Another version, dedicated to extraction *)

Definition Qred_extr (q : Q) :=
  let (q1, q2) := Qfactor_twos q in
  let (p,_) := Zggcd_spec_pos (Zpos q2) (Zle_0_pos q2) q1 in  
  let (r2,r1) := snd p in r1#(Z2P r2).

Lemma Qred_extr_Qred : forall q, Qred_extr q = Qred q.
Proof.
unfold Qred, Qred_extr.
intro q; destruct (Qfactor_twos q) as (n,p); clear q.
Open Scope Z_scope.
destruct (Zggcd_spec_pos (' p) (Zle_0_pos p) n) as ((g,(pp,nn)),H).
generalize (H (Zle_0_pos p)); clear H; intros (Hg1,(Hg2,(Hg4,Hg3))).
simpl.
generalize (Zggcd_gcd n ('p)) (Zgcd_is_gcd n ('p)) 
 (Zgcd_is_pos n ('p)) (Zggcd_correct_divisors n ('p)).
destruct (Zggcd n (Zpos p)) as (g',(nn',pp')); simpl.
intro H; rewrite <- H; clear H.
intros Hg'1 Hg'2 (Hg'3,Hg'4).
assert (g<>0).
 intro; subst g; discriminate.
destruct (Zis_gcd_uniqueness_apart_sign n ('p) g g'); auto.
apply Zis_gcd_sym; auto.
subst g'.
f_equal.
apply Zmult_reg_l with g; auto; congruence.
f_equal.
apply Zmult_reg_l with g; auto; congruence.
elimtype False; omega.
Open Scope Q_scope.
Qed.

Add Morphism Qred_extr : Qred_extr_comp. 
Proof.
intros q q' H.
do 2 rewrite Qred_extr_Qred.
rewrite (Qred_correct q); auto.
rewrite (Qred_correct q'); auto.
Qed.

Definition Qplus' (p q : Q) := Qred (Qplus p q).
Definition Qmult' (p q : Q) := Qred (Qmult p q). 

Lemma Qplus'_correct : forall p q : Q, (Qplus' p q)==(Qplus p q).
Proof.
intros; unfold Qplus' in |- *; apply Qred_correct; auto.
Qed.

Lemma Qmult'_correct : forall p q : Q, (Qmult' p q)==(Qmult p q).
Proof.
intros; unfold Qmult' in |- *; apply Qred_correct; auto.
Qed.

Add Morphism Qplus' : Qplus'_comp.
Proof.
intros; unfold Qplus' in |- *.
rewrite H; rewrite H0; auto with qarith.
Qed.

Add Morphism Qmult' : Qmult'_comp.
intros; unfold Qmult' in |- *.
rewrite H; rewrite H0; auto with qarith.
Qed.

