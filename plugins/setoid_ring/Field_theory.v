(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Ring.
Import Ring_polynom Ring_tac Ring_theory InitialRing Setoid List Morphisms.
Require Import ZArith_base.
Set Implicit Arguments.
(* Set Universe Polymorphism. *)

Section MakeFieldPol.

(* Field elements : R *)

Variable R:Type.
Bind Scope R_scope with R.
Delimit Scope R_scope with ring.
Local Open Scope R_scope.

Variable (rO rI : R) (radd rmul rsub: R->R->R) (ropp : R->R).
Variable (rdiv : R->R->R) (rinv : R->R).
Variable req : R -> R -> Prop.

Notation "0" := rO : R_scope.
Notation "1" := rI : R_scope.
Infix "+" := radd : R_scope.
Infix "-" := rsub : R_scope.
Infix "*" := rmul : R_scope.
Infix "/" := rdiv : R_scope.
Notation "- x" := (ropp x) : R_scope.
Notation "/ x" := (rinv x) : R_scope.
Infix "==" := req (at level 70, no associativity) : R_scope.

(* Equality properties *)
Variable Rsth : Equivalence req.
Variable Reqe : ring_eq_ext radd rmul ropp req.
Variable SRinv_ext : forall p q, p == q ->  / p == / q.

(* Field properties *)
Record almost_field_theory : Prop := mk_afield {
 AF_AR : almost_ring_theory rO rI radd rmul rsub ropp req;
 AF_1_neq_0 : ~ 1 == 0;
 AFdiv_def : forall p q, p / q == p * / q;
 AFinv_l : forall p, ~ p == 0 ->  / p * p == 1
}.

Section AlmostField.

Variable AFth : almost_field_theory.
Let ARth := AFth.(AF_AR).
Let rI_neq_rO := AFth.(AF_1_neq_0).
Let rdiv_def := AFth.(AFdiv_def).
Let rinv_l := AFth.(AFinv_l).

Add Morphism radd with signature (req ==> req ==> req) as radd_ext.
Proof. exact (Radd_ext Reqe). Qed.
Add Morphism rmul with signature (req ==> req ==> req) as rmul_ext.
Proof. exact (Rmul_ext Reqe). Qed.
Add Morphism ropp with signature (req ==> req) as ropp_ext.
Proof. exact (Ropp_ext Reqe). Qed.
Add Morphism rsub with signature (req ==> req ==> req) as rsub_ext.
Proof. exact (ARsub_ext Rsth Reqe ARth). Qed.
Add Morphism rinv with signature (req ==> req) as rinv_ext.
Proof. exact SRinv_ext. Qed.

Let eq_trans := Setoid.Seq_trans _ _ Rsth.
Let eq_sym := Setoid.Seq_sym _ _ Rsth.
Let eq_refl := Setoid.Seq_refl _ _ Rsth.

Let radd_0_l := ARadd_0_l ARth.
Let radd_comm := ARadd_comm ARth.
Let radd_assoc := ARadd_assoc ARth.
Let rmul_1_l := ARmul_1_l ARth.
Let rmul_0_l := ARmul_0_l ARth.
Let rmul_comm := ARmul_comm ARth.
Let rmul_assoc := ARmul_assoc ARth.
Let rdistr_l := ARdistr_l ARth.
Let ropp_mul_l := ARopp_mul_l ARth.
Let ropp_add := ARopp_add ARth.
Let rsub_def := ARsub_def ARth.

Let radd_0_r := ARadd_0_r Rsth ARth.
Let rmul_0_r := ARmul_0_r Rsth ARth.
Let rmul_1_r := ARmul_1_r Rsth ARth.
Let ropp_0 := ARopp_zero Rsth Reqe ARth.
Let rdistr_r := ARdistr_r Rsth Reqe ARth.

(* Coefficients : C *)

Variable C: Type.
Bind Scope C_scope with C.
Delimit Scope C_scope with coef.

Variable (cO cI: C) (cadd cmul csub : C->C->C) (copp : C->C).
Variable ceqb : C->C->bool.
Variable phi : C -> R.

Variable CRmorph : ring_morph rO rI radd rmul rsub ropp req
                              cO cI cadd cmul csub copp ceqb phi.

Notation "0" := cO : C_scope.
Notation "1" := cI : C_scope.
Infix "+" := cadd : C_scope.
Infix "-" := csub : C_scope.
Infix "*" := cmul : C_scope.
Notation "- x" := (copp x) : C_scope.
Infix "=?" := ceqb : C_scope.
Notation "[ x ]" := (phi x) (at level 0).

Let phi_0 := CRmorph.(morph0).
Let phi_1 := CRmorph.(morph1).

Lemma ceqb_spec c c' : BoolSpec ([c] == [c']) True (c =? c')%coef.
Proof.
generalize (CRmorph.(morph_eq) c c').
destruct (c =? c')%coef; auto.
Qed.

(* Power coefficients : Cpow *)

Variable Cpow : Type.
Variable Cp_phi : N -> Cpow.
Variable rpow : R -> Cpow -> R.
Variable pow_th : power_theory rI rmul req Cp_phi rpow.
(* sign function *)
Variable get_sign : C -> option C.
Variable get_sign_spec : sign_theory copp ceqb get_sign.

Variable cdiv:C -> C -> C*C.
Variable cdiv_th : div_theory req cadd cmul phi cdiv.

Let rpow_pow := pow_th.(rpow_pow_N).

(* Polynomial expressions : (PExpr C) *)

Bind Scope PE_scope with PExpr.
Delimit Scope PE_scope with poly.

Notation NPEeval := (PEeval rO rI radd rmul rsub ropp phi Cp_phi rpow).
Notation "P @ l" := (NPEeval l P) (at level 10, no associativity).

Arguments PEc _ _%coef.

Notation "0" := (PEc 0) : PE_scope.
Notation "1" := (PEc 1) : PE_scope.
Infix "+" := PEadd : PE_scope.
Infix "-" := PEsub : PE_scope.
Infix "*" := PEmul : PE_scope.
Notation "- e" := (PEopp e) : PE_scope.
Infix "^" := PEpow : PE_scope.

Definition NPEequiv e e' := forall l, e@l == e'@l.
Infix "===" := NPEequiv (at level 70, no associativity) : PE_scope.

Instance NPEequiv_eq : Equivalence NPEequiv.
Proof.
 split; red; unfold NPEequiv; intros; [reflexivity|symmetry|etransitivity];
  eauto.
Qed.

Instance NPEeval_ext : Proper (eq ==> NPEequiv ==> req) NPEeval.
Proof.
 intros l l' <- e e' He. now rewrite (He l).
Qed.

Notation Nnorm :=
  (norm_subst cO cI cadd cmul csub copp ceqb cdiv).
Notation NPphi_dev :=
  (Pphi_dev rO rI radd rmul rsub ropp cO cI ceqb phi get_sign).
Notation NPphi_pow :=
  (Pphi_pow rO rI radd rmul rsub ropp cO cI ceqb phi Cp_phi rpow get_sign).

(* add abstract semi-ring to help with some proofs *)
Add Ring Rring : (ARth_SRth ARth).

(* additional ring properties *)

Lemma rsub_0_l r : 0 - r == - r.
Proof.
rewrite rsub_def; ring.
Qed.

Lemma rsub_0_r r : r - 0 == r.
Proof.
rewrite rsub_def, ropp_0; ring.
Qed.

(***************************************************************************

                       Properties of division

  ***************************************************************************)

Theorem rdiv_simpl p q : ~ q == 0 ->  q * (p / q) == p.
Proof.
intros.
rewrite rdiv_def.
transitivity (/ q * q * p); [ ring | ].
now rewrite rinv_l.
Qed.

Instance rdiv_ext: Proper (req ==> req ==> req) rdiv.
Proof.
intros p1 p2 Ep q1 q2 Eq. now rewrite !rdiv_def, Ep, Eq.
Qed.

Lemma rmul_reg_l p q1 q2 :
  ~ p == 0 -> p * q1 == p * q2 -> q1 == q2.
Proof.
intros H EQ.
assert (H' : p * (q1 / p) == p * (q2 / p)).
{ now rewrite !rdiv_def, !rmul_assoc, EQ. }
now rewrite !rdiv_simpl in H'.
Qed.

Theorem field_is_integral_domain r1 r2 :
  ~ r1 == 0 -> ~ r2 == 0 -> ~ r1 * r2 == 0.
Proof.
intros H1 H2. contradict H2.
transitivity (/r1 * r1 * r2).
- now rewrite rinv_l.
- now rewrite <- rmul_assoc, H2.
Qed.

Theorem ropp_neq_0 r :
  ~ -(1) == 0 -> ~ r == 0 -> ~ -r == 0.
Proof.
intros.
setoid_replace (- r) with (- (1) * r).
- apply field_is_integral_domain; trivial.
- now rewrite <- ropp_mul_l, rmul_1_l.
Qed.

Theorem rdiv_r_r r : ~ r == 0 -> r / r == 1.
Proof.
intros. rewrite rdiv_def, rmul_comm. now apply rinv_l.
Qed.

Theorem rdiv1 r : r == r / 1.
Proof.
transitivity (1 * (r / 1)).
- symmetry; apply rdiv_simpl. apply rI_neq_rO.
- apply rmul_1_l.
Qed.

Theorem rdiv2 a b c d :
 ~ b == 0 ->
 ~ d == 0 ->
 a / b + c / d == (a * d + c * b) / (b * d).
Proof.
intros H H0.
assert (~ b * d == 0) by now apply field_is_integral_domain.
apply rmul_reg_l with (b * d); trivial.
rewrite rdiv_simpl; trivial.
rewrite rdistr_r.
apply radd_ext.
- now rewrite <- rmul_assoc, (rmul_comm d), rmul_assoc, rdiv_simpl.
- now rewrite (rmul_comm c), <- rmul_assoc, rdiv_simpl.
Qed.


Theorem rdiv2b a b c d e :
 ~ (b*e) == 0 ->
 ~ (d*e) == 0 ->
 a / (b*e) + c / (d*e) == (a * d + c * b) / (b * (d * e)).
Proof.
intros H H0.
assert (~ b == 0) by (contradict H; rewrite H; ring).
assert (~ e == 0) by (contradict H; rewrite H; ring).
assert (~ d == 0) by (contradict H0; rewrite H0; ring).
assert (~ b * (d * e) == 0)
   by (repeat apply field_is_integral_domain; trivial).
apply rmul_reg_l with (b * (d * e)); trivial.
rewrite rdiv_simpl; trivial.
rewrite rdistr_r.
apply radd_ext.
- transitivity ((b * e) * (a / (b * e)) * d);
  [ ring | now rewrite rdiv_simpl ].
- transitivity ((d * e) * (c / (d * e)) * b);
  [ ring | now rewrite rdiv_simpl ].
Qed.

Theorem rdiv5 a b : - (a / b) == - a / b.
Proof.
now rewrite !rdiv_def, ropp_mul_l.
Qed.

Theorem rdiv3b a b c d e :
 ~ (b * e) == 0 ->
 ~ (d * e) == 0 ->
 a / (b*e) - c / (d*e) == (a * d - c * b) / (b * (d * e)).
Proof.
intros H H0.
rewrite !rsub_def, rdiv5, ropp_mul_l.
now apply rdiv2b.
Qed.

Theorem rdiv6 a b :
 ~ a == 0 -> ~ b == 0 ->  / (a / b) == b / a.
Proof.
intros H H0.
assert (Hk : ~ a / b == 0).
{ contradict H.
  transitivity (b * (a / b)).
  - now rewrite rdiv_simpl.
  - rewrite H. apply rmul_0_r. }
apply rmul_reg_l with (a / b); trivial.
rewrite (rmul_comm (a / b)), rinv_l; trivial.
rewrite !rdiv_def.
transitivity (/ a * a * (/ b * b)); [ | ring ].
now rewrite !rinv_l, rmul_1_l.
Qed.

Theorem rdiv4 a b c d :
 ~ b == 0 ->
 ~ d == 0 ->
 (a / b) * (c / d) == (a * c) / (b * d).
Proof.
intros H H0.
assert (~ b * d == 0) by now apply field_is_integral_domain.
apply rmul_reg_l with (b * d); trivial.
rewrite rdiv_simpl; trivial.
transitivity (b * (a / b) * (d * (c / d))); [ ring | ].
rewrite !rdiv_simpl; trivial.
Qed.

Theorem rdiv4b a b c d e f :
 ~ b * e == 0 ->
 ~ d * f == 0 ->
 ((a * f) / (b * e)) * ((c * e) / (d * f)) == (a * c) / (b * d).
Proof.
intros H H0.
assert (~ b == 0) by (contradict H; rewrite H; ring).
assert (~ e == 0) by (contradict H; rewrite H; ring).
assert (~ d == 0) by (contradict H0; rewrite H0; ring).
assert (~ f == 0) by (contradict H0; rewrite H0; ring).
assert (~ b*d == 0) by now apply field_is_integral_domain.
assert (~ e*f == 0) by now apply field_is_integral_domain.
rewrite rdiv4; trivial.
transitivity ((e * f) * (a * c) / ((e * f) * (b * d))).
- apply rdiv_ext; ring.
- rewrite <- rdiv4, rdiv_r_r; trivial.
Qed.

Theorem rdiv7 a b c d :
 ~ b == 0 ->
 ~ c == 0 ->
 ~ d == 0 ->
 (a / b) / (c / d) == (a * d) / (b * c).
Proof.
intros.
rewrite (rdiv_def (a / b)).
rewrite rdiv6; trivial.
apply rdiv4; trivial.
Qed.

Theorem rdiv7b a b c d e f :
 ~ b * f == 0 ->
 ~ c * e == 0 ->
 ~ d * f == 0 ->
 ((a * e) / (b * f)) / ((c * e) / (d * f)) == (a * d) / (b * c).
Proof.
intros Hbf Hce Hdf.
assert (~ c==0) by (contradict Hce; rewrite Hce; ring).
assert (~ e==0) by (contradict Hce; rewrite Hce; ring).
assert (~ b==0) by (contradict Hbf; rewrite Hbf; ring).
assert (~ f==0) by (contradict Hbf; rewrite Hbf; ring).
assert (~ b*c==0) by now apply field_is_integral_domain.
assert (~ e*f==0) by now apply field_is_integral_domain.
rewrite rdiv7; trivial.
transitivity ((e * f) * (a * d) / ((e * f) * (b * c))).
- apply rdiv_ext; ring.
- now rewrite <- rdiv4, rdiv_r_r.
Qed.

Theorem rinv_nz a : ~ a == 0 -> ~ /a == 0.
Proof.
intros H H0. apply rI_neq_rO.
rewrite <- (rdiv_r_r H), rdiv_def, H0. apply rmul_0_r.
Qed.

Theorem rdiv8 a b : ~ b == 0 -> a == 0 ->  a / b == 0.
Proof.
intros H H0.
now rewrite rdiv_def, H0, rmul_0_l.
Qed.

Theorem cross_product_eq a b c d :
  ~ b == 0 -> ~ d == 0 -> a * d == c * b -> a / b == c / d.
Proof.
intros.
transitivity (a / b * (d / d)).
- now rewrite rdiv_r_r, rmul_1_r.
- now rewrite rdiv4, H1, (rmul_comm b d), <- rdiv4, rdiv_r_r.
Qed.

(* Results about [pow_pos] and [pow_N] *)

Instance pow_ext : Proper (req ==> eq ==> req) (pow_pos rmul).
Proof.
intros x y H p p' <-.
induction p as [p IH| p IH|];simpl; trivial; now rewrite !IH, ?H.
Qed.

Instance pow_N_ext : Proper (req ==> eq ==> req) (pow_N rI rmul).
Proof.
intros x y H n n' <-. destruct n; simpl; trivial. now apply pow_ext.
Qed.

Lemma pow_pos_0 p : pow_pos rmul 0 p == 0.
Proof.
induction p;simpl;trivial; now rewrite !IHp.
Qed.

Lemma pow_pos_1 p : pow_pos rmul 1 p == 1.
Proof.
induction p;simpl;trivial; ring [IHp].
Qed.

Lemma pow_pos_cst c p : pow_pos rmul [c] p == [pow_pos cmul c p].
Proof.
induction p;simpl;trivial; now rewrite !CRmorph.(morph_mul), !IHp.
Qed.

Lemma pow_pos_mul_l x y p :
 pow_pos rmul (x * y) p == pow_pos rmul x p * pow_pos rmul y p.
Proof.
induction p;simpl;trivial; ring [IHp].
Qed.

Lemma pow_pos_add_r x p1 p2 :
 pow_pos rmul x (p1+p2) == pow_pos rmul x p1 * pow_pos rmul x p2.
Proof.
 exact (Ring_theory.pow_pos_add Rsth rmul_ext rmul_assoc x p1 p2).
Qed.

Lemma pow_pos_mul_r x p1 p2 :
  pow_pos rmul x (p1*p2) == pow_pos rmul (pow_pos rmul x p1) p2.
Proof.
induction p1;simpl;intros; rewrite ?pow_pos_mul_l, ?pow_pos_add_r;
 simpl; trivial; ring [IHp1].
Qed.

Lemma pow_pos_nz x p : ~x==0 -> ~pow_pos rmul x p == 0.
Proof.
 intros Hx. induction p;simpl;trivial;
  repeat (apply field_is_integral_domain; trivial).
Qed.

Lemma pow_pos_div a b p : ~ b == 0 ->
 pow_pos rmul (a / b) p == pow_pos rmul a p / pow_pos rmul b p.
Proof.
 intros.
 induction p; simpl; trivial.
 - rewrite IHp.
   assert (nz := pow_pos_nz p H).
   rewrite !rdiv4; trivial.
   apply field_is_integral_domain; trivial.
 - rewrite IHp.
   assert (nz := pow_pos_nz p H).
   rewrite !rdiv4; trivial.
Qed.

(* === is a morphism *)

Instance PEadd_ext : Proper (NPEequiv ==> NPEequiv ==> NPEequiv) (@PEadd C).
Proof. intros ? ? E ? ? E' l. simpl. now rewrite E, E'. Qed.
Instance PEsub_ext : Proper (NPEequiv ==> NPEequiv ==> NPEequiv) (@PEsub C).
Proof. intros ? ? E ? ? E' l. simpl. now rewrite E, E'. Qed.
Instance PEmul_ext : Proper (NPEequiv ==> NPEequiv ==> NPEequiv) (@PEmul C).
Proof. intros ? ? E ? ? E' l. simpl. now rewrite E, E'. Qed.
Instance PEopp_ext : Proper (NPEequiv ==> NPEequiv) (@PEopp C).
Proof. intros ? ? E l. simpl. now rewrite E. Qed.
Instance PEpow_ext : Proper (NPEequiv ==> eq ==> NPEequiv) (@PEpow C).
Proof.
 intros ? ? E ? ? <- l. simpl. rewrite !rpow_pow. apply pow_N_ext; trivial.
Qed.

Lemma PE_1_l (e : PExpr C) : (1 * e === e)%poly.
Proof.
 intros l. simpl. rewrite phi_1. apply rmul_1_l.
Qed.

Lemma PE_1_r (e : PExpr C) : (e * 1 === e)%poly.
Proof.
 intros l. simpl. rewrite phi_1. apply rmul_1_r.
Qed.

Lemma PEpow_0_r (e : PExpr C) : (e ^ 0 === 1)%poly.
Proof.
 intros l. simpl. now rewrite !rpow_pow.
Qed.

Lemma PEpow_1_r (e : PExpr C) : (e ^ 1 === e)%poly.
Proof.
 intros l. simpl. now rewrite !rpow_pow.
Qed.

Lemma PEpow_1_l n : (1 ^ n === 1)%poly.
Proof.
 intros l. simpl. rewrite rpow_pow. destruct n; simpl.
 - now rewrite phi_1.
 - now rewrite phi_1, pow_pos_1.
Qed.

Lemma PEpow_add_r (e : PExpr C) n n' :
 (e ^ (n+n') === e ^ n * e ^ n')%poly.
Proof.
 intros l. simpl. rewrite !rpow_pow.
 destruct n; simpl.
 - rewrite rmul_1_l. trivial.
 - destruct n'; simpl.
   + rewrite rmul_1_r. trivial.
   + apply pow_pos_add_r.
Qed.

Lemma PEpow_mul_l (e e' : PExpr C) n :
 ((e * e') ^ n === e ^ n * e' ^ n)%poly.
Proof.
 intros l. simpl. rewrite !rpow_pow. destruct n; simpl; trivial.
 - symmetry; apply rmul_1_l.
 - apply pow_pos_mul_l.
Qed.

Lemma PEpow_mul_r (e : PExpr C) n n' :
 (e ^ (n * n') === (e ^ n) ^ n')%poly.
Proof.
 intros l. simpl. rewrite !rpow_pow.
 destruct n, n'; simpl; trivial.
 - now rewrite pow_pos_1.
 - apply pow_pos_mul_r.
Qed.

Lemma PEpow_nz l e n : ~ e @ l == 0 -> ~ (e^n) @ l == 0.
Proof.
 intros. simpl. rewrite rpow_pow. destruct n; simpl.
 - apply rI_neq_rO.
 - now apply pow_pos_nz.
Qed.


(***************************************************************************

                       Some equality test

  ***************************************************************************)

Local Notation "a &&& b" := (if a then b else false)
 (at level 40, left associativity).

(* equality test *)
Fixpoint PExpr_eq (e e' : PExpr C) {struct e} : bool :=
 match e, e' with
  | PEc c, PEc c' => ceqb c c'
  | PEX _ p, PEX _ p' => Pos.eqb p p'
  | e1 + e2, e1' + e2' => PExpr_eq e1 e1' &&& PExpr_eq e2 e2'
  | e1 - e2, e1' - e2' => PExpr_eq e1 e1' &&& PExpr_eq e2 e2'
  | e1 * e2, e1' * e2' => PExpr_eq e1 e1' &&& PExpr_eq e2 e2'
  | - e, - e' => PExpr_eq e e'
  | e ^ n, e' ^ n' => N.eqb n n' &&& PExpr_eq e e'
  | _, _ => false
 end%poly.

Lemma if_true (a b : bool) : a &&& b = true -> a = true /\ b = true.
Proof.
 destruct a, b; split; trivial.
Qed.

Theorem PExpr_eq_semi_ok e e' :
 PExpr_eq e e' = true ->  (e === e')%poly.
Proof.
revert e'; induction e; destruct e'; simpl; try discriminate.
- intros H l. now apply (morph_eq CRmorph).
- case Pos.eqb_spec; intros; now subst.
- intros H; destruct (if_true _ _ H). now rewrite IHe1, IHe2.
- intros H; destruct (if_true _ _ H). now rewrite IHe1, IHe2.
- intros H; destruct (if_true _ _ H). now rewrite IHe1, IHe2.
- intros H. now rewrite IHe.
- intros H. destruct (if_true _ _ H).
  apply N.eqb_eq in H0. now rewrite IHe, H0.
Qed.

Lemma PExpr_eq_spec e e' : BoolSpec (e === e')%poly True (PExpr_eq e e').
Proof.
 assert (H := PExpr_eq_semi_ok e e').
 destruct PExpr_eq; constructor; intros; trivial. now apply H.
Qed.

(** Smart constructors for polynomial expression,
    with reduction of constants *)

Definition NPEadd e1 e2 :=
  match e1, e2 with
  | PEc c1, PEc c2 => PEc (c1 + c2)
  | PEc c, _ => if (c =? 0)%coef then e2 else e1 + e2
  |  _, PEc c => if (c =? 0)%coef then e1 else e1 + e2
    (* Peut t'on factoriser ici ??? *)
  | _, _ => (e1 + e2)
  end%poly.
Infix "++" := NPEadd (at level 60, right associativity).

Theorem NPEadd_ok e1 e2 : (e1 ++ e2 === e1 + e2)%poly.
Proof.
intros l.
destruct e1, e2; simpl; try reflexivity; try (case ceqb_spec);
try intro H; try rewrite H; simpl;
try apply eq_refl; try (ring [phi_0]).
apply (morph_add CRmorph).
Qed.

Definition NPEsub e1 e2 :=
  match e1, e2 with
  | PEc c1, PEc c2 => PEc (c1 - c2)
  | PEc c, _ => if (c =? 0)%coef then - e2 else e1 - e2
  |  _, PEc c => if (c =? 0)%coef then e1 else e1 - e2
     (* Peut-on factoriser ici *)
  | _, _ => e1 - e2
  end%poly.
Infix "--" := NPEsub (at level 50, left associativity).

Theorem NPEsub_ok e1 e2: (e1 -- e2 === e1 - e2)%poly.
Proof.
intros l.
destruct e1, e2; simpl; try reflexivity; try case ceqb_spec;
 try intro H; try rewrite H; simpl;
 try rewrite phi_0; try reflexivity;
 try (symmetry; apply rsub_0_l); try (symmetry; apply rsub_0_r).
apply (morph_sub CRmorph).
Qed.

Definition NPEopp e1 :=
  match e1 with PEc c1 => PEc (- c1) | _ => - e1 end%poly.

Theorem NPEopp_ok e : (NPEopp e === -e)%poly.
Proof.
intros l. destruct e; simpl; trivial. apply (morph_opp CRmorph).
Qed.

Definition NPEpow x n :=
  match n with
  | N0 => 1
  | Npos p =>
    if (p =? 1)%positive then x else
    match x with
    | PEc c =>
      if (c =? 1)%coef then 1
      else if (c =? 0)%coef then 0
      else PEc (pow_pos cmul c p)
    | _ => x ^ n
    end
  end%poly.
Infix "^^" := NPEpow (at level 35, right associativity).

Theorem NPEpow_ok e n : (e ^^ n === e ^ n)%poly.
Proof.
 intros l. unfold NPEpow; destruct n.
 - simpl; now rewrite rpow_pow.
 - case Pos.eqb_spec; [intro; subst | intros _].
   + simpl. now rewrite rpow_pow.
   + destruct e;simpl;trivial.
     repeat case ceqb_spec; intros; rewrite ?rpow_pow, ?H; simpl.
     * now rewrite phi_1, pow_pos_1.
     * now rewrite phi_0, pow_pos_0.
     * now rewrite pow_pos_cst.
Qed.

Fixpoint NPEmul (x y : PExpr C) {struct x} : PExpr C :=
  match x, y with
  | PEc c1, PEc c2 => PEc (c1 * c2)
  | PEc c, _ => if (c =? 1)%coef then y else if (c =? 0)%coef then 0 else x * y
  | _, PEc c => if (c =? 1)%coef then x else if (c =? 0)%coef then 0 else x * y
  | e1 ^ n1, e2 ^ n2 => if (n1 =? n2)%N then (NPEmul e1 e2)^^n1 else x * y
  | _, _ => x * y
  end%poly.
Infix "**" := NPEmul (at level 40, left associativity).

Theorem NPEmul_ok e1 e2 : (e1 ** e2 === e1 * e2)%poly.
Proof.
intros l.
revert e2; induction e1;destruct e2; simpl;try reflexivity;
 repeat (case ceqb_spec; intro H; try rewrite H; clear H);
 simpl; try reflexivity; try ring [phi_0 phi_1].
 apply (morph_mul CRmorph).
case N.eqb_spec; [intros <- | reflexivity].
rewrite NPEpow_ok. simpl.
rewrite !rpow_pow. rewrite IHe1.
destruct n; simpl; [ ring | apply pow_pos_mul_l ].
Qed.

(* simplification *)
Fixpoint PEsimp (e : PExpr C) : PExpr C :=
 match e with
  | e1 + e2 => (PEsimp e1) ++ (PEsimp e2)
  | e1 * e2 => (PEsimp e1) ** (PEsimp e2)
  | e1 - e2 => (PEsimp e1) -- (PEsimp e2)
  | - e1 => NPEopp (PEsimp e1)
  | e1 ^ n1 => (PEsimp e1) ^^ n1
  | _ => e
 end%poly.

Theorem PEsimp_ok e : (PEsimp e === e)%poly.
Proof.
induction e; simpl.
- reflexivity.
- reflexivity.
- intro l; trivial.
- intro l; trivial.
- rewrite NPEadd_ok. now f_equiv.
- rewrite NPEsub_ok. now f_equiv.
- rewrite NPEmul_ok. now f_equiv.
- rewrite NPEopp_ok. now f_equiv.
- rewrite NPEpow_ok. now f_equiv.
Qed.


(****************************************************************************

                               Datastructure

  ***************************************************************************)

(* The input: syntax of a field expression *)

Inductive FExpr : Type :=
 | FEO : FExpr
 | FEI : FExpr
 | FEc: C ->  FExpr
 | FEX: positive ->  FExpr
 | FEadd: FExpr -> FExpr ->  FExpr
 | FEsub: FExpr -> FExpr ->  FExpr
 | FEmul: FExpr -> FExpr ->  FExpr
 | FEopp: FExpr ->  FExpr
 | FEinv: FExpr ->  FExpr
 | FEdiv: FExpr -> FExpr ->  FExpr
 | FEpow: FExpr -> N -> FExpr .

Fixpoint FEeval (l : list R) (pe : FExpr) {struct pe} : R :=
  match pe with
  | FEO       => rO
  | FEI       => rI
  | FEc c     => phi c
  | FEX x     => BinList.nth 0 x l
  | FEadd x y => FEeval l x + FEeval l y
  | FEsub x y => FEeval l x - FEeval l y
  | FEmul x y => FEeval l x * FEeval l y
  | FEopp x   => - FEeval l x
  | FEinv x   => / FEeval l x
  | FEdiv x y => FEeval l x / FEeval l y
  | FEpow x n => rpow (FEeval l x) (Cp_phi n)
  end.

Strategy expand [FEeval].

(* The result of the normalisation *)

Record linear : Type := mk_linear {
   num : PExpr C;
   denum : PExpr C;
   condition : list (PExpr C) }.

(***************************************************************************

                Semantics and properties of side condition

  ***************************************************************************)

Fixpoint PCond (l : list R) (le : list (PExpr C)) {struct le} : Prop :=
  match le with
  | nil => True
  | e1 :: nil => ~ req (e1 @ l) rO
  | e1 :: l1 => ~ req (e1 @ l) rO /\ PCond l l1
  end.

Theorem PCond_cons l a l1 :
 PCond l (a :: l1) <-> ~ a @ l == 0 /\ PCond l l1.
Proof.
destruct l1.
- simpl. split; [split|destruct 1]; trivial.
- reflexivity.
Qed.

Theorem PCond_cons_inv_l l a l1 : PCond l (a::l1) ->  ~ a @ l == 0.
Proof.
rewrite PCond_cons. now destruct 1.
Qed.

Theorem PCond_cons_inv_r l a l1 : PCond l (a :: l1) ->  PCond l l1.
Proof.
rewrite PCond_cons. now destruct 1.
Qed.

Theorem PCond_app l l1 l2 :
 PCond l (l1 ++ l2) <-> PCond l l1 /\ PCond l l2.
Proof.
induction l1.
- simpl. split; [split|destruct 1]; trivial.
- simpl app. rewrite !PCond_cons, IHl1. symmetry; apply and_assoc.
Qed.


(* An unsatisfiable condition: issued when a division by zero is detected *)
Definition absurd_PCond := cons 0%poly nil.

Lemma absurd_PCond_bottom : forall l, ~ PCond l absurd_PCond.
Proof.
unfold absurd_PCond; simpl.
red; intros.
apply H.
apply phi_0.
Qed.

(***************************************************************************

                               Normalisation

  ***************************************************************************)

Definition default_isIn e1 p1 e2 p2 :=
  if PExpr_eq e1 e2 then
    match Z.pos_sub p1 p2 with
     | Zpos p => Some (Npos p, 1%poly)
     | Z0 => Some (N0, 1%poly)
     | Zneg p => Some (N0, e2 ^^ Npos p)
    end
  else None.

Fixpoint isIn e1 p1 e2 p2 {struct e2}: option (N * PExpr C) :=
  match e2 with
  | e3 * e4 =>
       match isIn e1 p1 e3 p2 with
       | Some (N0, e5) => Some (N0, e5 ** (e4 ^^ Npos p2))
       | Some (Npos p, e5) =>
          match isIn e1 p e4 p2 with
          | Some (n, e6) => Some (n, e5 ** e6)
          | None => Some (Npos p, e5 ** (e4 ^^ Npos p2))
          end
       | None =>
         match isIn e1 p1 e4 p2 with
         | Some (n, e5) => Some (n, (e3 ^^ Npos p2) ** e5)
         | None => None
         end
       end
  | e3 ^ N0 => None
  | e3 ^ Npos p3 => isIn e1 p1 e3 (Pos.mul p3 p2)
  | _ => default_isIn e1 p1 e2 p2
   end%poly.

 Definition ZtoN z := match z with Zpos p => Npos p | _ => N0 end.
 Definition NtoZ n := match n with Npos p => Zpos p | _ => Z0 end.

 Lemma Z_pos_sub_gt p q : (p > q)%positive ->
  Z.pos_sub p q = Zpos (p - q).
 Proof. intros; now apply Z.pos_sub_gt, Pos.gt_lt. Qed.

 Ltac simpl_pos_sub := rewrite ?Z_pos_sub_gt in * by assumption.

 Lemma default_isIn_ok e1 e2 p1 p2 :
  match default_isIn e1 p1 e2 p2 with
   | Some(n, e3) =>
       let n' := ZtoN (Zpos p1 - NtoZ n) in
       (e2 ^ N.pos p2 === e1 ^ n' * e3)%poly
       /\ (Zpos p1 > NtoZ n)%Z
   | _ => True
  end.
Proof.
  unfold default_isIn.
  case PExpr_eq_spec; trivial. intros EQ.
  rewrite Z.pos_sub_spec.
  case Pos.compare_spec;intros H; split; try reflexivity.
  - simpl. now rewrite PE_1_r, H, EQ.
  - rewrite NPEpow_ok, EQ, <- PEpow_add_r. f_equiv.
    simpl. f_equiv. now rewrite Pos.add_comm, Pos.sub_add.
  - simpl. rewrite PE_1_r, EQ. f_equiv.
    rewrite Z.pos_sub_gt by now apply Pos.sub_decr. simpl. f_equiv.
    rewrite Pos.sub_sub_distr, Pos.add_comm; trivial.
    rewrite Pos.add_sub; trivial.
    apply Pos.sub_decr; trivial.
  - simpl. now apply Z.lt_gt, Pos.sub_decr.
Qed.

Ltac npe_simpl := rewrite ?NPEmul_ok, ?NPEpow_ok, ?PEpow_mul_l.
Ltac npe_ring := intro l; simpl; ring.

Theorem isIn_ok e1 p1 e2 p2 :
  match isIn e1 p1 e2 p2 with
   | Some(n, e3) =>
       let n' := ZtoN (Zpos p1 - NtoZ n) in
       (e2 ^ N.pos p2 === e1 ^ n' * e3)%poly
       /\ (Zpos p1 > NtoZ n)%Z
   |  _ => True
  end.
Proof.
Opaque NPEpow.
revert p1 p2.
induction e2; intros p1 p2;
 try refine (default_isIn_ok e1 _ p1 p2); simpl isIn.
- specialize (IHe2_1 p1 p2).
  destruct isIn as [([|p],e)|].
  + split; [|reflexivity].
    clear IHe2_2.
    destruct IHe2_1 as (IH,_).
    npe_simpl. rewrite IH. npe_ring.
  + specialize (IHe2_2 p p2).
    destruct isIn as [([|p'],e')|].
    * destruct IHe2_1 as (IH1,GT1).
      destruct IHe2_2 as (IH2,GT2).
      split; [|simpl; apply Zgt_trans with (Z.pos p); trivial].
      npe_simpl. rewrite IH1, IH2. simpl. simpl_pos_sub. simpl.
      replace (N.pos p1) with (N.pos p + N.pos (p1 - p))%N.
      rewrite PEpow_add_r; npe_ring.
      { simpl. f_equal. rewrite Pos.add_comm, Pos.sub_add. trivial.
        now apply Pos.gt_lt. }
    * destruct IHe2_1 as (IH1,GT1).
      destruct IHe2_2 as (IH2,GT2).
      assert (Z.pos p1 > Z.pos p')%Z by (now apply Zgt_trans with (Zpos p)).
      split; [|simpl; trivial].
      npe_simpl. rewrite IH1, IH2. simpl. simpl_pos_sub. simpl.
      replace (N.pos (p1 - p')) with (N.pos (p1 - p) + N.pos (p - p'))%N.
      rewrite PEpow_add_r; npe_ring.
      { simpl. f_equal. rewrite Pos.add_sub_assoc, Pos.sub_add; trivial.
        now apply Pos.gt_lt.
        now apply Pos.gt_lt. }
    * destruct IHe2_1 as (IH,GT). split; trivial.
      npe_simpl. rewrite IH. npe_ring.
  + specialize (IHe2_2 p1 p2).
    destruct isIn as [(n,e)|]; trivial.
    destruct IHe2_2 as (IH,GT). split; trivial.
    set (d := ZtoN (Z.pos p1 - NtoZ n)) in *; clearbody d.
    npe_simpl. rewrite IH. npe_ring.
- destruct n; trivial.
  specialize (IHe2 p1 (p * p2)%positive).
  destruct isIn as [(n,e)|]; trivial.
  destruct IHe2 as (IH,GT). split; trivial.
  set (d := ZtoN (Z.pos p1 - NtoZ n)) in *; clearbody d.
  now rewrite <- PEpow_mul_r.
Qed.

Record rsplit : Type := mk_rsplit {
   rsplit_left : PExpr C;
   rsplit_common : PExpr C;
   rsplit_right : PExpr C}.

(* Stupid name clash *)
Notation left := rsplit_left.
Notation right := rsplit_right.
Notation common := rsplit_common.

Fixpoint split_aux e1 p e2 {struct e1}: rsplit :=
  match e1 with
  | e3 * e4 =>
      let r1 := split_aux e3 p e2 in
      let r2 := split_aux e4 p (right r1) in
      mk_rsplit (left r1 ** left r2)
                (common r1 ** common r2)
                (right r2)
  | e3 ^ N0 => mk_rsplit 1 1 e2
  | e3 ^ Npos p3 => split_aux e3 (Pos.mul p3 p) e2
  | _ =>
       match isIn e1 p e2 1 with
       | Some (N0,e3) => mk_rsplit 1 (e1 ^^ Npos p) e3
       | Some (Npos q, e3) => mk_rsplit (e1 ^^ Npos q) (e1 ^^ Npos (p - q)) e3
       | None => mk_rsplit (e1 ^^ Npos p) 1 e2
       end
  end%poly.

Lemma split_aux_ok1 e1 p e2 :
  (let res := match isIn e1 p e2 1 with
       | Some (N0,e3) => mk_rsplit 1 (e1 ^^ Npos p) e3
       | Some (Npos q, e3) => mk_rsplit (e1 ^^ Npos q) (e1 ^^ Npos (p - q)) e3
       | None => mk_rsplit (e1 ^^ Npos p) 1 e2
       end
  in
  e1 ^ Npos p === left res * common res
  /\ e2 === right res * common res)%poly.
Proof.
 Opaque NPEpow NPEmul.
 intros. unfold res;clear res; generalize (isIn_ok e1 p e2 xH).
 destruct (isIn e1 p e2 1) as [([|p'],e')|]; simpl.
 - intros (H1,H2); split; npe_simpl.
   + now rewrite PE_1_l.
   + rewrite PEpow_1_r in H1. rewrite H1. npe_ring.
 - intros (H1,H2); split; npe_simpl.
   + rewrite <- PEpow_add_r. f_equiv. simpl. f_equal.
     rewrite Pos.add_comm, Pos.sub_add; trivial.
     now apply Z.gt_lt in H2.
   + rewrite PEpow_1_r in H1. rewrite H1. simpl_pos_sub. simpl. npe_ring.
 - intros _; split; npe_simpl; now rewrite PE_1_r.
Qed.

Theorem split_aux_ok: forall e1 p e2,
  (e1 ^ Npos p === left (split_aux e1 p e2) * common (split_aux e1 p e2)
  /\ e2 === right (split_aux e1 p e2) * common (split_aux e1 p e2))%poly.
Proof.
induction e1;intros k e2; try refine (split_aux_ok1 _ k e2);simpl.
destruct (IHe1_1 k e2) as (H1,H2).
destruct (IHe1_2 k (right (split_aux e1_1 k e2))) as (H3,H4).
clear IHe1_1 IHe1_2.
- npe_simpl; split.
  * rewrite H1, H3. npe_ring.
  * rewrite H2 at 1. rewrite H4 at 1. npe_ring.
- destruct n; simpl.
  + rewrite PEpow_0_r, PEpow_1_l, !PE_1_r. now split.
  + rewrite <- PEpow_mul_r. simpl. apply IHe1.
Qed.

Definition split e1 e2 := split_aux e1 xH e2.

Theorem split_ok_l e1 e2 :
  (e1 === left (split e1 e2) * common (split e1 e2))%poly.
Proof.
destruct (split_aux_ok e1 xH e2) as (H,_). now rewrite <- H, PEpow_1_r.
Qed.

Theorem split_ok_r e1 e2 :
  (e2 === right (split e1 e2) * common (split e1 e2))%poly.
Proof.
destruct (split_aux_ok e1 xH e2) as (_,H). trivial.
Qed.

Lemma split_nz_l l e1 e2 :
 ~ e1 @ l == 0 -> ~ left (split e1 e2) @ l == 0.
Proof.
 intros H. contradict H. rewrite (split_ok_l e1 e2); simpl.
 now rewrite H, rmul_0_l.
Qed.

Lemma split_nz_r l e1 e2 :
 ~ e2 @ l == 0 -> ~ right (split e1 e2) @ l == 0.
Proof.
 intros H. contradict H. rewrite (split_ok_r e1 e2); simpl.
 now rewrite H, rmul_0_l.
Qed.

Fixpoint Fnorm (e : FExpr) : linear :=
  match e with
  | FEO => mk_linear 0 1 nil
  | FEI => mk_linear 1 1 nil
  | FEc c => mk_linear (PEc c) 1 nil
  | FEX x => mk_linear (PEX C x) 1 nil
  | FEadd e1 e2 =>
      let x := Fnorm e1 in
      let y := Fnorm e2 in
      let s := split (denum x) (denum y) in
      mk_linear
        ((num x ** right s) ++ (num y ** left s))
        (left s ** (right s ** common s))
        (condition x ++ condition y)%list
  | FEsub e1 e2 =>
      let x := Fnorm e1 in
      let y := Fnorm e2 in
      let s := split (denum x) (denum y) in
      mk_linear
        ((num x ** right s) -- (num y ** left s))
        (left s ** (right s ** common s))
        (condition x ++ condition y)%list
  | FEmul e1 e2 =>
      let x := Fnorm e1 in
      let y := Fnorm e2 in
      let s1 := split (num x) (denum y) in
      let s2 := split (num y) (denum x) in
      mk_linear (left s1 ** left s2)
        (right s2 ** right s1)
        (condition x ++ condition y)%list
  | FEopp e1 =>
      let x := Fnorm e1 in
      mk_linear (NPEopp (num x)) (denum x) (condition x)
  | FEinv e1 =>
      let x := Fnorm e1 in
      mk_linear (denum x) (num x) (num x :: condition x)
  | FEdiv e1 e2 =>
      let x := Fnorm e1 in
      let y := Fnorm e2 in
      let s1 := split (num x) (num y) in
      let s2 := split (denum x) (denum y) in
      mk_linear (left s1 ** right s2)
        (left s2 ** right s1)
        (num y :: condition x ++ condition y)%list
  | FEpow e1 n =>
      let x := Fnorm e1 in
      mk_linear ((num x)^^n) ((denum x)^^n) (condition x)
  end.

(* Example *)
(*
Eval compute
   in (Fnorm
        (FEdiv
          (FEc cI)
          (FEadd (FEinv (FEX xH%positive)) (FEinv (FEX (xO xH)%positive))))).
*)

Theorem Pcond_Fnorm l e :
 PCond l (condition (Fnorm e)) ->  ~ (denum (Fnorm e))@l == 0.
Proof.
induction e; simpl condition; rewrite ?PCond_cons, ?PCond_app;
 simpl denum; intros (Hc1,Hc2) || intros Hc; rewrite ?NPEmul_ok.
- simpl. rewrite phi_1; exact rI_neq_rO.
- simpl. rewrite phi_1; exact rI_neq_rO.
- simpl; intros. rewrite phi_1; exact rI_neq_rO.
- simpl; intros. rewrite phi_1; exact rI_neq_rO.
- rewrite <- split_ok_r. simpl. apply field_is_integral_domain.
  + apply split_nz_l, IHe1, Hc1.
  + apply IHe2, Hc2.
- rewrite <- split_ok_r. simpl. apply field_is_integral_domain.
  + apply split_nz_l, IHe1, Hc1.
  + apply IHe2, Hc2.
- simpl. apply field_is_integral_domain.
  + apply split_nz_r, IHe1, Hc1.
  + apply split_nz_r, IHe2, Hc2.
- now apply IHe.
- trivial.
- destruct Hc2 as (Hc2,_). simpl. apply field_is_integral_domain.
  + apply split_nz_l, IHe1, Hc2.
  + apply split_nz_r, Hc1.
- rewrite NPEpow_ok. apply PEpow_nz, IHe, Hc.
Qed.


(***************************************************************************

                       Main theorem

  ***************************************************************************)

Ltac uneval :=
 repeat match goal with
  | |- context [ ?x @ ?l * ?y @ ?l ] => change (x@l * y@l) with ((x*y)@l)
  | |- context [ ?x @ ?l + ?y @ ?l ] => change (x@l + y@l) with ((x+y)@l)
 end.

Theorem Fnorm_FEeval_PEeval l fe:
 PCond l (condition (Fnorm fe)) ->
 FEeval l fe == (num (Fnorm fe)) @ l / (denum (Fnorm fe)) @ l.
Proof.
induction fe; simpl condition; rewrite ?PCond_cons, ?PCond_app; simpl;
 intros (Hc1,Hc2) || intros Hc;
 try (specialize (IHfe1 Hc1);apply Pcond_Fnorm in Hc1);
 try (specialize (IHfe2 Hc2);apply Pcond_Fnorm in Hc2);
 try set (F1 := Fnorm fe1) in *; try set (F2 := Fnorm fe2) in *.

- now rewrite phi_1, phi_0, rdiv_def.
- now rewrite phi_1; apply rdiv1.
- rewrite phi_1; apply rdiv1.
- rewrite phi_1; apply rdiv1.
- rewrite NPEadd_ok, !NPEmul_ok. simpl.
  rewrite <- rdiv2b; uneval; rewrite <- ?split_ok_l, <- ?split_ok_r; trivial.
  now f_equiv.

- rewrite NPEsub_ok, !NPEmul_ok. simpl.
  rewrite <- rdiv3b; uneval; rewrite <- ?split_ok_l, <- ?split_ok_r; trivial.
  now f_equiv.

- rewrite !NPEmul_ok. simpl.
  rewrite IHfe1, IHfe2.
  rewrite (split_ok_l (num F1) (denum F2) l),
          (split_ok_r (num F1) (denum F2) l),
          (split_ok_l (num F2) (denum F1) l),
          (split_ok_r (num F2) (denum F1) l) in *.
  apply rdiv4b; trivial.

- rewrite NPEopp_ok; simpl; rewrite (IHfe Hc); apply rdiv5.

- rewrite (IHfe Hc2); apply rdiv6; trivial;
   apply Pcond_Fnorm; trivial.

- destruct Hc2 as (Hc2,Hc3).
  rewrite !NPEmul_ok. simpl.
  assert (U1 := split_ok_l (num F1) (num F2) l).
  assert (U2 := split_ok_r (num F1) (num F2) l).
  assert (U3 := split_ok_l (denum F1) (denum F2) l).
  assert (U4 := split_ok_r (denum F1) (denum F2) l).
  rewrite (IHfe1 Hc2), (IHfe2 Hc3), U1, U2, U3, U4.
  simpl in U2, U3, U4. apply rdiv7b;
   rewrite <- ?U2, <- ?U3, <- ?U4; try apply Pcond_Fnorm; trivial.

- rewrite !NPEpow_ok. simpl. rewrite !rpow_pow, (IHfe Hc).
  destruct n; simpl.
  + apply rdiv1.
  + apply pow_pos_div. apply Pcond_Fnorm; trivial.
Qed.

Theorem Fnorm_crossproduct l fe1 fe2 :
 let nfe1 := Fnorm fe1 in
 let nfe2 := Fnorm fe2 in
 (num nfe1 * denum nfe2) @ l == (num nfe2 * denum nfe1) @ l ->
 PCond l (condition nfe1 ++ condition nfe2) ->
 FEeval l fe1 == FEeval l fe2.
Proof.
simpl. rewrite PCond_app. intros Hcrossprod (Hc1,Hc2).
rewrite !Fnorm_FEeval_PEeval; trivial.
apply cross_product_eq; trivial;
 apply Pcond_Fnorm; trivial.
Qed.

(* Correctness lemmas of reflexive tactics *)
Notation Ninterp_PElist :=
  (interp_PElist rO rI radd rmul rsub ropp req phi Cp_phi rpow).
Notation Nmk_monpol_list :=
  (mk_monpol_list cO cI cadd cmul csub copp ceqb cdiv).

Theorem Fnorm_ok:
 forall n l lpe fe,
  Ninterp_PElist l lpe ->
  Peq ceqb (Nnorm n (Nmk_monpol_list lpe) (num (Fnorm fe))) (Pc cO) = true ->
  PCond l (condition (Fnorm fe)) ->  FEeval l fe == 0.
Proof.
intros n l lpe fe Hlpe H H1.
rewrite (Fnorm_FEeval_PEeval l fe H1).
apply rdiv8. apply Pcond_Fnorm; trivial.
transitivity (0@l); trivial.
rewrite (norm_subst_ok Rsth Reqe ARth CRmorph pow_th cdiv_th n l lpe); trivial.
change (0 @ l) with (Pphi 0 radd rmul phi l (Pc cO)).
apply (Peq_ok Rsth Reqe CRmorph); trivial.
Qed.

Notation ring_rw_correct :=
 (ring_rw_correct Rsth Reqe ARth CRmorph pow_th cdiv_th get_sign_spec).

Notation ring_rw_pow_correct :=
 (ring_rw_pow_correct Rsth Reqe ARth CRmorph pow_th cdiv_th get_sign_spec).

Notation ring_correct :=
 (ring_correct Rsth Reqe ARth CRmorph pow_th cdiv_th).

(* simplify a field expression into a fraction *)
(* TODO: simplify when den is constant... *)
Definition display_linear l num den :=
  NPphi_dev l num / NPphi_dev l den.

Definition display_pow_linear l num den :=
  NPphi_pow l num / NPphi_pow l den.

Theorem Field_rw_correct n lpe l :
   Ninterp_PElist l lpe ->
   forall lmp, Nmk_monpol_list lpe = lmp ->
   forall fe nfe, Fnorm fe = nfe ->
   PCond l (condition nfe) ->
   FEeval l fe ==
     display_linear l (Nnorm n lmp (num nfe)) (Nnorm n lmp (denum nfe)).
Proof.
  intros Hlpe lmp lmp_eq fe nfe eq_nfe H; subst nfe lmp.
  rewrite (Fnorm_FEeval_PEeval _ _ H).
  unfold display_linear; apply rdiv_ext;
  eapply ring_rw_correct; eauto.
Qed.

Theorem Field_rw_pow_correct n lpe l :
   Ninterp_PElist l lpe ->
   forall lmp, Nmk_monpol_list lpe = lmp ->
   forall fe nfe, Fnorm fe = nfe ->
   PCond l (condition nfe) ->
   FEeval l fe ==
     display_pow_linear l (Nnorm n lmp (num nfe)) (Nnorm n lmp (denum nfe)).
Proof.
  intros Hlpe lmp lmp_eq fe nfe eq_nfe H; subst nfe lmp.
  rewrite (Fnorm_FEeval_PEeval _ _ H).
  unfold display_pow_linear; apply rdiv_ext;
  eapply ring_rw_pow_correct;eauto.
Qed.

Theorem Field_correct n l lpe fe1 fe2 :
 Ninterp_PElist l lpe ->
 forall lmp, Nmk_monpol_list lpe = lmp ->
 forall nfe1, Fnorm fe1 = nfe1 ->
 forall nfe2, Fnorm fe2 = nfe2 ->
 Peq ceqb (Nnorm n lmp (num nfe1 * denum nfe2))
          (Nnorm n lmp (num nfe2 * denum nfe1)) = true ->
 PCond l (condition nfe1 ++ condition nfe2) ->
 FEeval l fe1 == FEeval l fe2.
Proof.
intros Hlpe lmp eq_lmp nfe1 eq1 nfe2 eq2 Hnorm Hcond; subst nfe1 nfe2 lmp.
apply Fnorm_crossproduct; trivial.
eapply ring_correct; eauto.
Qed.

(* simplify a field equation : generate the crossproduct and simplify
   polynomials *)

(** This allows rewriting modulo the simplification of PEeval on PMul *)
Declare Equivalent Keys PEeval rmul.

Theorem Field_simplify_eq_correct :
 forall n l lpe fe1 fe2,
    Ninterp_PElist l lpe ->
 forall lmp, Nmk_monpol_list lpe = lmp ->
 forall nfe1, Fnorm fe1 = nfe1 ->
 forall nfe2, Fnorm fe2 = nfe2 ->
 forall den, split (denum nfe1) (denum nfe2) = den ->
 NPphi_dev l (Nnorm n lmp (num nfe1 * right den)) ==
 NPphi_dev l (Nnorm n lmp (num nfe2 * left den)) ->
 PCond l (condition nfe1 ++ condition nfe2) ->
 FEeval l fe1 == FEeval l fe2.
Proof.
intros n l lpe fe1 fe2 Hlpe lmp Hlmp nfe1 eq1 nfe2 eq2 den eq3 Hcrossprod Hcond.
apply Fnorm_crossproduct; rewrite ?eq1, ?eq2; trivial.
simpl.
rewrite (split_ok_l (denum nfe1) (denum nfe2) l), eq3.
rewrite (split_ok_r (denum nfe1) (denum nfe2) l), eq3.
simpl.
rewrite !rmul_assoc.
apply rmul_ext; trivial.
rewrite (ring_rw_correct n lpe l Hlpe Logic.eq_refl (num nfe1 * right den) Logic.eq_refl),
 (ring_rw_correct n lpe l Hlpe Logic.eq_refl (num nfe2 * left den) Logic.eq_refl).
rewrite Hlmp.
apply Hcrossprod.
Qed.

Theorem Field_simplify_eq_pow_correct :
 forall n l lpe fe1 fe2,
    Ninterp_PElist l lpe ->
 forall lmp, Nmk_monpol_list lpe = lmp ->
 forall nfe1, Fnorm fe1 = nfe1 ->
 forall nfe2, Fnorm fe2 = nfe2 ->
 forall den, split (denum nfe1) (denum nfe2) = den ->
 NPphi_pow l (Nnorm n lmp (num nfe1 * right den)) ==
 NPphi_pow l (Nnorm n lmp (num nfe2 * left den)) ->
 PCond l (condition nfe1 ++ condition nfe2) ->
 FEeval l fe1 == FEeval l fe2.
Proof.
intros n l lpe fe1 fe2 Hlpe lmp Hlmp nfe1 eq1 nfe2 eq2 den eq3 Hcrossprod Hcond.
apply Fnorm_crossproduct; rewrite ?eq1, ?eq2; trivial.
simpl.
rewrite (split_ok_l (denum nfe1) (denum nfe2) l), eq3.
rewrite (split_ok_r (denum nfe1) (denum nfe2) l), eq3.
simpl.
rewrite !rmul_assoc.
apply rmul_ext; trivial.
rewrite
 (ring_rw_pow_correct n lpe l Hlpe Logic.eq_refl (num nfe1 * right den) Logic.eq_refl),
 (ring_rw_pow_correct n lpe l Hlpe Logic.eq_refl (num nfe2 * left den) Logic.eq_refl).
rewrite Hlmp.
apply Hcrossprod.
Qed.

Theorem Field_simplify_aux_ok l fe1 fe2 den :
 FEeval l fe1 == FEeval l fe2 ->
 split (denum (Fnorm fe1)) (denum (Fnorm fe2)) = den ->
 PCond l (condition (Fnorm fe1) ++ condition (Fnorm fe2)) ->
 (num (Fnorm fe1) * right den) @ l == (num (Fnorm fe2) * left den) @ l.
Proof.
 rewrite PCond_app; intros Hfe Hden (Hc1,Hc2); simpl.
 assert (Hc1' := Pcond_Fnorm _ _ Hc1).
 assert (Hc2' := Pcond_Fnorm _ _ Hc2).
 set (N1 := num (Fnorm fe1)) in *. set (N2 := num (Fnorm fe2)) in *.
 set (D1 := denum (Fnorm fe1)) in *. set (D2 := denum (Fnorm fe2)) in *.
 assert (~ (common den) @ l == 0).
 { intro H. apply Hc1'.
   rewrite (split_ok_l D1 D2 l).
   rewrite Hden. simpl. ring [H]. }
 apply (@rmul_reg_l ((common den) @ l)); trivial.
 rewrite !(rmul_comm ((common den) @ l)), <- !rmul_assoc.
 change
  (N1@l * (right den * common den) @ l ==
   N2@l * (left den * common den) @ l).
 rewrite <- Hden, <- split_ok_l, <- split_ok_r.
 apply (@rmul_reg_l (/ D2@l)). { apply rinv_nz; trivial. }
 rewrite (rmul_comm (/ D2 @ l)), <- !rmul_assoc.
 rewrite <- rdiv_def, rdiv_r_r, rmul_1_r by trivial.
 apply (@rmul_reg_l (/ (D1@l))). { apply rinv_nz; trivial. }
 rewrite !(rmul_comm  (/ D1@l)), <- !rmul_assoc.
 rewrite <- !rdiv_def, rdiv_r_r, rmul_1_r by trivial.
 rewrite (rmul_comm (/ D2@l)), <- rdiv_def.
 unfold N1,N2,D1,D2; rewrite <- !Fnorm_FEeval_PEeval; trivial.
Qed.

Theorem Field_simplify_eq_pow_in_correct :
 forall n l lpe fe1 fe2,
    Ninterp_PElist l lpe ->
 forall lmp, Nmk_monpol_list lpe = lmp ->
 forall nfe1, Fnorm fe1 = nfe1 ->
 forall nfe2, Fnorm fe2 = nfe2 ->
 forall den, split (denum nfe1) (denum nfe2) = den ->
 forall np1, Nnorm n lmp (num nfe1 * right den) = np1 ->
 forall np2, Nnorm n lmp (num nfe2 * left den) = np2 ->
 FEeval l fe1 == FEeval l fe2 ->
 PCond l (condition nfe1 ++ condition nfe2) ->
 NPphi_pow l np1 ==
 NPphi_pow l np2.
Proof.
 intros. subst nfe1 nfe2 lmp np1 np2.
 rewrite !(Pphi_pow_ok Rsth Reqe ARth CRmorph pow_th get_sign_spec).
 repeat (rewrite <- (norm_subst_ok Rsth Reqe ARth CRmorph pow_th);trivial).
 simpl. apply Field_simplify_aux_ok; trivial.
Qed.

Theorem Field_simplify_eq_in_correct :
forall n l lpe fe1 fe2,
    Ninterp_PElist l lpe ->
 forall lmp, Nmk_monpol_list lpe = lmp ->
 forall nfe1, Fnorm fe1 = nfe1 ->
 forall nfe2, Fnorm fe2 = nfe2 ->
 forall den, split (denum nfe1) (denum nfe2) = den ->
 forall np1, Nnorm n lmp (num nfe1 * right den) = np1 ->
 forall np2, Nnorm n lmp (num nfe2 * left den) = np2 ->
 FEeval l fe1 == FEeval l fe2 ->
 PCond l (condition nfe1 ++ condition nfe2) ->
 NPphi_dev l np1 == NPphi_dev l np2.
Proof.
 intros. subst nfe1 nfe2 lmp np1 np2.
 rewrite !(Pphi_dev_ok Rsth Reqe ARth CRmorph  get_sign_spec).
 repeat (rewrite <- (norm_subst_ok Rsth Reqe ARth CRmorph pow_th);trivial).
 apply Field_simplify_aux_ok; trivial.
Qed.


Section Fcons_impl.

Variable Fcons : PExpr C -> list (PExpr C) -> list (PExpr C).

Hypothesis PCond_fcons_inv : forall l a l1,
  PCond l (Fcons a l1) ->  ~ a @ l == 0 /\ PCond l l1.

Fixpoint Fapp (l m:list (PExpr C)) {struct l} : list (PExpr C) :=
  match l with
  | nil => m
  | cons a l1 => Fcons a (Fapp l1 m)
  end.

Lemma fcons_ok : forall l l1,
  (forall lock, lock = PCond l -> lock (Fapp l1 nil)) -> PCond l l1.
Proof.
intros l l1 h1; assert (H := h1 (PCond l) (refl_equal _));clear h1.
induction l1; simpl; intros.
 trivial.
 elim PCond_fcons_inv with (1 := H); intros.
 destruct l1; trivial. split; trivial. apply IHl1; trivial.
Qed.

End Fcons_impl.

Section Fcons_simpl.

(* Some general simpifications of the condition: eliminate duplicates,
   split multiplications *)

Fixpoint Fcons (e:PExpr C) (l:list (PExpr C)) {struct l} : list (PExpr C) :=
 match l with
   nil       => cons e nil
 | cons a l1 => if PExpr_eq e a then l else cons a (Fcons e l1)
 end.

Theorem PFcons_fcons_inv:
 forall l a l1, PCond l (Fcons a l1) ->  ~ a @ l == 0 /\ PCond l l1.
Proof.
induction l1 as [|e l1]; simpl Fcons.
- simpl; now split.
- case PExpr_eq_spec; intros H; rewrite !PCond_cons; intros (H1,H2);
   repeat split; trivial.
  + now rewrite H.
  + now apply IHl1.
  + now apply IHl1.
Qed.

(* equality of normal forms rather than syntactic equality *)
Fixpoint Fcons0 (e:PExpr C) (l:list (PExpr C)) {struct l} : list (PExpr C) :=
 match l with
   nil       => cons e nil
 | cons a l1 =>
     if Peq ceqb (Nnorm O nil e) (Nnorm O nil a) then l
     else cons a (Fcons0 e l1)
 end.

Theorem PFcons0_fcons_inv:
 forall l a l1, PCond l (Fcons0 a l1) ->  ~ a @ l == 0 /\ PCond l l1.
Proof.
induction l1 as [|e l1]; simpl Fcons0.
- simpl; now split.
- generalize (ring_correct O l nil a e). lazy zeta; simpl Peq.
  case Peq; intros H; rewrite !PCond_cons; intros (H1,H2);
   repeat split; trivial.
  + now rewrite H.
  + now apply IHl1.
  + now apply IHl1.
Qed.

(* split factorized denominators *)
Fixpoint Fcons00 (e:PExpr C) (l:list (PExpr C)) {struct e} : list (PExpr C) :=
 match e with
   PEmul e1 e2 => Fcons00 e1 (Fcons00 e2 l)
 | PEpow e1 _ => Fcons00 e1 l
 | _ => Fcons0 e l
 end.

Theorem PFcons00_fcons_inv:
  forall l a l1, PCond l (Fcons00 a l1) -> ~ a @ l == 0 /\ PCond l l1.
Proof.
intros l a; elim a; try (intros; apply PFcons0_fcons_inv; trivial; fail).
- intros p H p0 H0 l1 H1.
  simpl in H1.
  destruct (H _ H1) as (H2,H3).
  destruct (H0 _ H3) as (H4,H5). split; trivial.
  simpl.
  apply field_is_integral_domain; trivial.
- intros. destruct (H _ H0). split; trivial.
  apply PEpow_nz; trivial.
Qed.

Definition Pcond_simpl_gen :=
  fcons_ok _ PFcons00_fcons_inv.


(* Specific case when the equality test of coefs is complete w.r.t. the
   field equality: non-zero coefs can be eliminated, and opposite can
   be simplified (if -1 <> 0) *)

Hypothesis ceqb_complete : forall c1 c2, [c1] == [c2] -> ceqb c1 c2 = true.

Lemma ceqb_spec' c1 c2 : Bool.reflect ([c1] == [c2]) (ceqb c1 c2).
Proof.
assert (H := morph_eq CRmorph c1 c2).
assert (H' := @ceqb_complete c1 c2).
destruct (ceqb c1 c2); constructor.
- now apply H.
- intro E. specialize (H' E). discriminate.
Qed.

Fixpoint Fcons1 (e:PExpr C) (l:list (PExpr C)) {struct e} : list (PExpr C) :=
 match e with
 | PEmul e1 e2 => Fcons1 e1 (Fcons1 e2 l)
 | PEpow e _ => Fcons1 e l
 | PEopp e => if (-(1) =? 0)%coef then absurd_PCond else Fcons1 e l
 | PEc c => if (c =? 0)%coef then absurd_PCond else l
 | _ => Fcons0 e l
 end.

Theorem PFcons1_fcons_inv:
  forall l a l1, PCond l (Fcons1 a l1) -> ~ a @ l == 0 /\ PCond l l1.
Proof.
intros l a; elim a; try (intros; apply PFcons0_fcons_inv; trivial; fail).
- simpl; intros c l1.
  case ceqb_spec'; intros H H0.
  + elim (@absurd_PCond_bottom l H0).
  + split; trivial. rewrite <- phi_0; trivial.
- intros p H p0 H0 l1 H1. simpl in H1.
  destruct (H _ H1) as (H2,H3).
  destruct (H0 _ H3) as (H4,H5).
  split; trivial. simpl. apply field_is_integral_domain; trivial.
- simpl; intros p H l1.
  case ceqb_spec'; intros H0 H1.
  + elim (@absurd_PCond_bottom l H1).
  + destruct (H _ H1).
    split; trivial.
    apply ropp_neq_0; trivial.
    rewrite (morph_opp CRmorph), phi_0, phi_1 in H0. trivial.
- intros. destruct (H _ H0);split;trivial. apply PEpow_nz; trivial.
Qed.

Definition Fcons2 e l := Fcons1 (PEsimp e) l.

Theorem PFcons2_fcons_inv:
 forall l a l1, PCond l (Fcons2 a l1) -> ~ a @ l == 0 /\ PCond l l1.
Proof.
unfold Fcons2; intros l a l1 H; split;
 case (PFcons1_fcons_inv l (PEsimp a) l1); trivial.
intros H1 H2 H3; case H1.
transitivity (a@l); trivial.
apply PEsimp_ok.
Qed.

Definition Pcond_simpl_complete :=
  fcons_ok _ PFcons2_fcons_inv.

End Fcons_simpl.

End AlmostField.

Section FieldAndSemiField.

  Record field_theory : Prop := mk_field {
    F_R : ring_theory rO rI radd rmul rsub ropp req;
    F_1_neq_0 : ~ 1 == 0;
    Fdiv_def : forall p q, p / q == p * / q;
    Finv_l : forall p, ~ p == 0 ->  / p * p == 1
  }.

  Definition F2AF f :=
    mk_afield
      (Rth_ARth Rsth Reqe f.(F_R)) f.(F_1_neq_0) f.(Fdiv_def) f.(Finv_l).

  Record semi_field_theory : Prop := mk_sfield {
    SF_SR : semi_ring_theory rO rI radd rmul req;
    SF_1_neq_0 : ~ 1 == 0;
    SFdiv_def : forall p q, p / q == p * / q;
    SFinv_l : forall p, ~ p == 0 ->  / p * p == 1
  }.

End FieldAndSemiField.

End MakeFieldPol.

  Definition SF2AF R (rO rI:R) radd rmul rdiv rinv req Rsth
    (sf:semi_field_theory rO rI radd rmul rdiv rinv req)  :=
    mk_afield _ _
      (SRth_ARth Rsth sf.(SF_SR))
      sf.(SF_1_neq_0)
      sf.(SFdiv_def)
      sf.(SFinv_l).


Section Complete.
 Variable R : Type.
 Variable (rO rI : R) (radd rmul rsub: R->R->R) (ropp : R -> R).
 Variable (rdiv : R -> R ->  R) (rinv : R ->  R).
 Variable req : R -> R -> Prop.
  Notation "0" := rO.  Notation "1" := rI.
  Notation "x + y" := (radd x y).  Notation "x * y " := (rmul x y).
  Notation "x - y " := (rsub x y).  Notation "- x" := (ropp x).
  Notation "x / y " := (rdiv x y).  Notation "/ x" := (rinv x).
  Notation "x == y" := (req x y) (at level 70, no associativity).
 Variable Rsth : Setoid_Theory R req.
   Add Parametric Relation : R req
     reflexivity  proved by Rsth.(@Equivalence_Reflexive _ _)
     symmetry     proved by Rsth.(@Equivalence_Symmetric _ _)
     transitivity proved by Rsth.(@Equivalence_Transitive _ _)
    as R_setoid3.
 Variable Reqe : ring_eq_ext radd rmul ropp req.
   Add Morphism radd with signature (req ==> req ==> req) as radd_ext3.
   Proof. exact (Radd_ext Reqe). Qed.
   Add Morphism rmul with signature (req ==> req ==> req) as rmul_ext3.
   Proof. exact (Rmul_ext Reqe). Qed.
   Add Morphism ropp with signature (req ==> req) as ropp_ext3.
   Proof. exact (Ropp_ext Reqe). Qed.

Section AlmostField.

 Variable AFth : almost_field_theory rO rI radd rmul rsub ropp rdiv rinv req.
 Let ARth := AFth.(AF_AR).
 Let rI_neq_rO := AFth.(AF_1_neq_0).
 Let rdiv_def := AFth.(AFdiv_def).
 Let rinv_l := AFth.(AFinv_l).

Hypothesis S_inj : forall x y, 1+x==1+y -> x==y.

Hypothesis gen_phiPOS_not_0 : forall p, ~ gen_phiPOS1 rI radd rmul p == 0.

Lemma add_inj_r p x y :
   gen_phiPOS1 rI radd rmul p + x == gen_phiPOS1 rI radd rmul p + y -> x==y.
Proof.
elim p using Pos.peano_ind; simpl; intros.
 apply S_inj; trivial.
 apply H.
   apply S_inj.
   rewrite !(ARadd_assoc ARth).
   rewrite <- (ARgen_phiPOS_Psucc Rsth Reqe ARth); trivial.
Qed.

Lemma gen_phiPOS_inj x y :
  gen_phiPOS rI radd rmul x == gen_phiPOS rI radd rmul y ->
  x = y.
Proof.
rewrite <- !(same_gen Rsth Reqe ARth).
case (Pos.compare_spec x y).
 intros.
   trivial.
 intros.
   elim gen_phiPOS_not_0 with (y - x)%positive.
   apply add_inj_r with x.
   symmetry.
   rewrite (ARadd_0_r Rsth ARth).
   rewrite <- (ARgen_phiPOS_add Rsth Reqe ARth).
   now rewrite Pos.add_comm, Pos.sub_add.
 intros.
   elim gen_phiPOS_not_0 with (x - y)%positive.
   apply add_inj_r with y.
   rewrite (ARadd_0_r Rsth ARth).
   rewrite <- (ARgen_phiPOS_add Rsth Reqe ARth).
   now rewrite Pos.add_comm, Pos.sub_add.
Qed.


Lemma gen_phiN_inj x y :
  gen_phiN rO rI radd rmul x == gen_phiN rO rI radd rmul y ->
  x = y.
Proof.
destruct x; destruct y; simpl; intros; trivial.
 elim gen_phiPOS_not_0 with p.
   symmetry .
   rewrite (same_gen Rsth Reqe ARth); trivial.
 elim gen_phiPOS_not_0 with p.
   rewrite (same_gen Rsth Reqe ARth); trivial.
 rewrite gen_phiPOS_inj with (1 := H); trivial.
Qed.

Lemma gen_phiN_complete x y :
  gen_phiN rO rI radd rmul x == gen_phiN rO rI radd rmul y ->
  N.eqb x y = true.
Proof.
intros. now apply N.eqb_eq, gen_phiN_inj.
Qed.

End AlmostField.

Section Field.

 Variable Fth : field_theory rO rI radd rmul rsub ropp rdiv rinv req.
 Let Rth := Fth.(F_R).
 Let rI_neq_rO := Fth.(F_1_neq_0).
 Let rdiv_def := Fth.(Fdiv_def).
 Let rinv_l := Fth.(Finv_l).
 Let AFth := F2AF Rsth Reqe Fth.
 Let ARth := Rth_ARth Rsth Reqe Rth.

Lemma ring_S_inj x y : 1+x==1+y -> x==y.
Proof.
intros.
rewrite <- (ARadd_0_l ARth x), <- (ARadd_0_l ARth y).
rewrite <- (Ropp_def Rth 1), (ARadd_comm ARth 1).
rewrite <- !(ARadd_assoc ARth). now apply (Radd_ext Reqe).
Qed.

Hypothesis gen_phiPOS_not_0 : forall p, ~ gen_phiPOS1 rI radd rmul p == 0.

Let gen_phiPOS_inject :=
   gen_phiPOS_inj AFth ring_S_inj gen_phiPOS_not_0.

Lemma gen_phiPOS_discr_sgn x y :
  ~ gen_phiPOS rI radd rmul x == - gen_phiPOS rI radd rmul y.
Proof.
red; intros.
apply gen_phiPOS_not_0 with (y + x)%positive.
rewrite (ARgen_phiPOS_add Rsth Reqe ARth).
transitivity (gen_phiPOS1 1 radd rmul y + - gen_phiPOS1 1 radd rmul y).
 apply (Radd_ext Reqe); trivial.
  reflexivity.
  rewrite (same_gen Rsth Reqe ARth).
    rewrite (same_gen Rsth Reqe ARth).
    trivial.
 apply (Ropp_def Rth).
Qed.

Lemma gen_phiZ_inj x y :
  gen_phiZ rO rI radd rmul ropp x == gen_phiZ rO rI radd rmul ropp y ->
  x = y.
Proof.
destruct x; destruct y; simpl; intros.
 trivial.
 elim gen_phiPOS_not_0 with p.
   rewrite (same_gen Rsth Reqe ARth).
   symmetry ; trivial.
 elim gen_phiPOS_not_0 with p.
   rewrite (same_gen Rsth Reqe ARth).
   rewrite <- (Ropp_opp Rsth Reqe Rth (gen_phiPOS 1 radd rmul p)).
   rewrite <- H.
   apply (ARopp_zero Rsth Reqe ARth).
 elim gen_phiPOS_not_0 with p.
   rewrite (same_gen Rsth Reqe ARth).
   trivial.
 rewrite gen_phiPOS_inject  with (1 := H); trivial.
 elim gen_phiPOS_discr_sgn with (1 := H).
 elim gen_phiPOS_not_0 with p.
   rewrite (same_gen Rsth Reqe ARth).
   rewrite <- (Ropp_opp Rsth Reqe Rth (gen_phiPOS 1 radd rmul p)).
   rewrite H.
   apply (ARopp_zero Rsth Reqe ARth).
 elim gen_phiPOS_discr_sgn with p0 p.
   symmetry ; trivial.
 replace p0 with p; trivial.
   apply gen_phiPOS_inject.
   rewrite <- (Ropp_opp Rsth Reqe Rth (gen_phiPOS 1 radd rmul p)).
   rewrite <- (Ropp_opp Rsth Reqe Rth (gen_phiPOS 1 radd rmul p0)).
   rewrite H; trivial.
   reflexivity.
Qed.

Lemma gen_phiZ_complete x y :
  gen_phiZ rO rI radd rmul ropp x == gen_phiZ rO rI radd rmul ropp y ->
  Zeq_bool x y = true.
Proof.
intros.
 replace y with x.
 unfold Zeq_bool.
   rewrite Z.compare_refl; trivial.
 apply gen_phiZ_inj; trivial.
Qed.

End Field.

End Complete.

Arguments FEO [C].
Arguments FEI [C].
