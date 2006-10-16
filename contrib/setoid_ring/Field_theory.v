(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Ring.
Import Ring_polynom Ring_theory InitialRing Setoid List.
Require Import ZArith_base.
Set Implicit Arguments.

Section MakeFieldPol.

(* Field elements *)     
 Variable R:Type.
 Variable (rO rI : R) (radd rmul rsub: R->R->R) (ropp : R->R).
 Variable (rdiv : R -> R ->  R) (rinv : R ->  R).
 Variable req : R -> R -> Prop.

 Notation "0" := rO. Notation "1" := rI.
 Notation "x + y" := (radd x y).  Notation "x * y " := (rmul x y).
 Notation "x - y " := (rsub x y). Notation "x / y" := (rdiv x y).
 Notation "- x" := (ropp x). Notation "/ x" := (rinv x).
 Notation "x == y" := (req x y) (at level 70, no associativity).

 (* Equality properties *)
 Variable Rsth : Setoid_Theory R req.
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

 (* Coefficients *) 
 Variable C: Type.
 Variable (cO cI: C) (cadd cmul csub : C->C->C) (copp : C->C).
 Variable ceqb : C->C->bool. 
 Variable phi : C -> R.

 Variable CRmorph : ring_morph rO rI radd rmul rsub ropp req
                               cO cI cadd cmul csub copp ceqb phi.

Lemma ceqb_rect : forall c1 c2 (A:Type) (x y:A) (P:A->Type),
  (phi c1 == phi c2 -> P x) -> P y -> P (if ceqb c1 c2 then x else y).
Proof.
intros.
generalize (fun h => X (morph_eq CRmorph c1 c2 h)).
case (ceqb c1 c2); auto.
Qed.


 (* C notations *)		 
 Notation "x +! y" := (cadd x y) (at level 50).
 Notation "x *! y " := (cmul x y) (at level 40).
 Notation "x -! y " := (csub x y) (at level 50).
 Notation "-! x" := (copp x) (at level 35).
 Notation " x ?=! y" := (ceqb x y) (at level 70, no associativity).
 Notation "[ x ]" := (phi x) (at level 0).


 (* Usefull tactics *)		  
  Add Setoid R req Rsth as R_set1.
  Add Morphism radd : radd_ext.  exact (Radd_ext Reqe). Qed.
  Add Morphism rmul : rmul_ext.  exact (Rmul_ext Reqe). Qed.
  Add Morphism ropp : ropp_ext.  exact (Ropp_ext Reqe). Qed.
  Add Morphism rsub : rsub_ext. exact (ARsub_ext Rsth Reqe ARth). Qed.
  Add Morphism rinv : rinv_ext. exact SRinv_ext. Qed.
 
Let eq_trans := Setoid.Seq_trans _ _ Rsth.
Let eq_sym := Setoid.Seq_sym _ _ Rsth.
Let eq_refl := Setoid.Seq_refl _ _ Rsth.

Hint Resolve eq_refl rdiv_def rinv_l rI_neq_rO CRmorph.(morph1) .
Hint Resolve (Rmul_ext Reqe) (Rmul_ext Reqe) (Radd_ext Reqe)
             (ARsub_ext Rsth Reqe ARth) (Ropp_ext Reqe) SRinv_ext.
Hint Resolve (ARadd_0_l  ARth) (ARadd_sym  ARth) (ARadd_assoc ARth)
             (ARmul_1_l  ARth) (ARmul_0_l  ARth) 
             (ARmul_sym  ARth) (ARmul_assoc ARth) (ARdistr_l  ARth)
             (ARopp_mul_l ARth) (ARopp_add  ARth) 
             (ARsub_def  ARth) .

Notation NPEeval := (PEeval rO radd rmul rsub ropp phi).
Notation Nnorm := (norm cO cI cadd cmul csub copp ceqb).
Notation NPphi_dev := (Pphi_dev rO rI radd rmul cO cI ceqb phi).

(* add abstract semi-ring to help with some proofs *)
Add Ring Rring : (ARth_SRth ARth).


(* additional ring properties *)

Lemma rsub_0_l : forall r, 0 - r == - r.
intros; rewrite (ARsub_def ARth) in |- *; ring.
Qed.

Lemma rsub_0_r : forall r, r - 0 == r.
intros; rewrite (ARsub_def ARth) in |- *.
rewrite (ARopp_zero Rsth Reqe ARth) in |- *;  ring.
Qed.

(***************************************************************************
                                                                          
                       Properties of division                             
                                                                          
  ***************************************************************************)
 
Theorem rdiv_simpl: forall p q, ~ q == 0 ->  q * (p / q) == p.
intros p q H.
rewrite rdiv_def in |- *.
transitivity (/ q * q * p); [  ring | idtac ].
rewrite rinv_l in |- *; auto.
Qed.
Hint Resolve rdiv_simpl .
 
Theorem SRdiv_ext:
 forall p1 p2, p1 == p2 -> forall q1 q2, q1 == q2 ->  p1 / q1 == p2 / q2.
intros p1 p2 H q1 q2 H0.
transitivity (p1 * / q1); auto.
transitivity (p2 * / q2); auto.
Qed.
Hint Resolve SRdiv_ext .

 Add Morphism rdiv : rdiv_ext. exact SRdiv_ext. Qed.

Lemma rmul_reg_l : forall p q1 q2,
  ~ p == 0 -> p * q1 == p * q2 -> q1 == q2.
intros.
rewrite <- (@rdiv_simpl q1 p) in |- *; trivial.
rewrite <- (@rdiv_simpl q2 p) in |- *; trivial.
repeat rewrite rdiv_def in |- *.
repeat rewrite (ARmul_assoc ARth) in |- *.
auto.
Qed.

Theorem field_is_integral_domain : forall r1 r2,
  ~ r1 == 0 -> ~ r2 == 0 -> ~ r1 * r2 == 0.
Proof.
red in |- *; intros.
apply H0.
transitivity (1 * r2); auto.
transitivity (/ r1 * r1 * r2); auto.
rewrite <- (ARmul_assoc ARth) in |- *.
rewrite H1 in |- *.
apply ARmul_0_r with (1 := Rsth) (2 := ARth).
Qed.

Theorem ropp_neq_0 : forall r,
  ~ -(1) == 0 -> ~ r == 0 -> ~ -r == 0.
intros.
setoid_replace (- r) with (- (1) * r).
 apply field_is_integral_domain; trivial.
 rewrite <- (ARopp_mul_l ARth) in |- *.
   rewrite (ARmul_1_l ARth) in |- *.
   reflexivity.
Qed.

Theorem rdiv_r_r : forall r, ~ r == 0 -> r / r == 1.
intros.
rewrite (AFdiv_def AFth) in |- *.
rewrite (ARmul_sym ARth) in |- *.
apply (AFinv_l AFth).
trivial.
Qed.

Theorem rdiv1: forall r,  r == r / 1.
intros r; transitivity (1 * (r / 1)); auto.
Qed.
 
Theorem rdiv2:
 forall r1 r2 r3 r4,
 ~ r2 == 0 ->
 ~ r4 == 0 ->
 r1 / r2 + r3 / r4 == (r1 * r4 + r3 * r2) / (r2 * r4).
Proof.
intros r1 r2 r3 r4 H H0.
assert (~ r2 * r4 == 0) by complete (apply field_is_integral_domain; trivial).
apply rmul_reg_l with (r2 * r4); trivial.
rewrite rdiv_simpl in |- *; trivial.
rewrite (ARdistr_r Rsth Reqe ARth) in |- *.
apply (Radd_ext Reqe).
 transitivity (r2 * (r1 / r2) * r4); [  ring | auto ].
 transitivity (r2 * (r4 * (r3 / r4))); auto.
   transitivity (r2 * r3); auto.
Qed.


Theorem rdiv2b:
 forall r1 r2 r3 r4 r5,
 ~ (r2*r5) == 0 ->
 ~ (r4*r5) == 0 ->
 r1 / (r2*r5) + r3 / (r4*r5) == (r1 * r4 + r3 * r2) / (r2 * (r4 * r5)).
Proof.
intros r1 r2 r3 r4 r5 H H0.
assert (HH1: ~ r2 == 0) by (intros HH; case H; rewrite HH; ring).
assert (HH2: ~ r5 == 0) by (intros HH; case H; rewrite HH; ring).
assert (HH3: ~ r4 == 0) by (intros HH; case H0; rewrite HH; ring).
assert (HH4: ~ r2 * (r4 * r5) == 0) 
   by complete (repeat apply field_is_integral_domain; trivial).
apply rmul_reg_l with (r2 * (r4 * r5)); trivial.
rewrite rdiv_simpl in |- *; trivial.
rewrite (ARdistr_r Rsth Reqe ARth) in |- *.
apply (Radd_ext Reqe).
 transitivity ((r2 * r5) * (r1 / (r2 * r5)) * r4); [  ring | auto ].
 transitivity ((r4 * r5) * (r3 / (r4 * r5)) * r2); [  ring | auto ].
Qed.

Theorem rdiv5: forall r1 r2,  - (r1 / r2) == - r1 / r2.
intros r1 r2.
transitivity (- (r1 * / r2)); auto.
transitivity (- r1 * / r2); auto.
Qed.
Hint Resolve rdiv5 .

Theorem rdiv3:
 forall r1 r2 r3 r4,
 ~ r2 == 0 ->
 ~ r4 == 0 ->
 r1 / r2 - r3 / r4 == (r1 * r4 -  r3 * r2) / (r2 * r4).
intros r1 r2 r3 r4 H H0.
assert (~ r2 * r4 == 0) by (apply field_is_integral_domain; trivial).
transitivity (r1 / r2 + - (r3 / r4)); auto.
transitivity (r1 / r2 + - r3 / r4); auto.
transitivity ((r1 * r4 + - r3 * r2) / (r2 * r4)); auto.
apply rdiv2; auto.
apply SRdiv_ext; auto.
transitivity (r1 * r4 + - (r3 * r2)); symmetry; auto.
Qed.


Theorem rdiv3b:
 forall r1 r2 r3 r4 r5,
 ~ (r2 * r5) == 0 ->
 ~ (r4 * r5) == 0 ->
 r1 / (r2*r5) - r3 / (r4*r5) == (r1 * r4 - r3 * r2) / (r2 * (r4 * r5)).
Proof.
intros r1 r2 r3 r4 r5 H H0.
transitivity (r1 / (r2 * r5) + - (r3 / (r4 * r5))); auto.
transitivity (r1 / (r2 * r5) + - r3 / (r4 * r5)); auto.
transitivity ((r1 * r4 + - r3 * r2) / (r2 * (r4 * r5))).
apply rdiv2b; auto; try ring.
apply (SRdiv_ext); auto.
transitivity (r1 * r4 + - (r3 * r2)); symmetry; auto.
Qed.

Theorem rdiv6:
 forall r1 r2,
 ~ r1 == 0 -> ~ r2 == 0 ->  / (r1 / r2) == r2 / r1.
intros r1 r2 H H0.
assert (~ r1 / r2 == 0) as Hk.
 intros H1; case H.
   transitivity (r2 * (r1 / r2)); auto.
   rewrite H1 in |- *;  ring.
 apply rmul_reg_l with (r1 / r2); auto.
   transitivity (/ (r1 / r2) * (r1 / r2)); auto.
   transitivity 1; auto.
   repeat rewrite rdiv_def in |- *.
   transitivity (/ r1 * r1 * (/ r2 * r2)); [ idtac |  ring ].
   repeat rewrite rinv_l in |- *; auto.
Qed.
Hint Resolve rdiv6 .
 
 Theorem rdiv4:
 forall r1 r2 r3 r4,
 ~ r2 == 0 ->
 ~ r4 == 0 ->
 (r1 / r2) * (r3 / r4) == (r1 * r3) / (r2 * r4).
Proof.
intros r1 r2 r3 r4 H H0.
assert (~ r2 * r4 == 0) by complete (apply field_is_integral_domain; trivial).
apply rmul_reg_l with (r2 * r4); trivial.
rewrite rdiv_simpl in |- *; trivial.
transitivity (r2 * (r1 / r2) * (r4 * (r3 / r4))); [  ring | idtac ].
repeat rewrite rdiv_simpl in |- *; trivial.
Qed.

 Theorem rdiv7:
 forall r1 r2 r3 r4,
 ~ r2 == 0 ->
 ~ r3 == 0 ->
 ~ r4 == 0 ->
 (r1 / r2) / (r3 / r4) == (r1 * r4) / (r2 * r3).
Proof.
intros.
rewrite (rdiv_def (r1 / r2)) in |- *.
rewrite rdiv6 in |- *; trivial.
apply rdiv4; trivial.
Qed.

Theorem rdiv8: forall r1 r2, ~ r2 == 0 -> r1 == 0 ->  r1 / r2 == 0.
intros r1 r2 H H0.
transitivity (r1 * / r2); auto.
transitivity (0 * / r2); auto.
Qed.


Theorem cross_product_eq : forall r1 r2 r3 r4,
  ~ r2 == 0 -> ~ r4 == 0 -> r1 * r4 == r3 * r2 -> r1 / r2 == r3 / r4.
intros.
transitivity (r1 / r2 * (r4 / r4)).
 rewrite rdiv_r_r in |- *; trivial.
   symmetry  in |- *.
   apply (ARmul_1_r Rsth ARth).
 rewrite rdiv4 in |- *; trivial.
   rewrite H1 in |- *.
   rewrite (ARmul_sym ARth r2 r4) in |- *.
   rewrite <- rdiv4 in |- *; trivial.
   rewrite rdiv_r_r in |- *.
  trivial.
  apply (ARmul_1_r Rsth ARth).
Qed.

(***************************************************************************
                                                                          
                       Some equality test                             
                                                                          
  ***************************************************************************)

Fixpoint positive_eq (p1 p2 : positive) {struct p1} : bool :=
 match p1, p2 with
   xH, xH => true
  | xO p3, xO p4 => positive_eq p3 p4
  | xI p3, xI p4 => positive_eq p3 p4
  | _, _ => false
 end.
 
Theorem positive_eq_correct:
 forall p1 p2,  if positive_eq p1 p2 then p1 = p2 else p1 <> p2.
intros p1; elim p1;
 (try (intros p2; case p2; simpl; auto; intros; discriminate)).
intros p3 rec p2; case p2; simpl; auto; (try (intros; discriminate)); intros p4.
generalize (rec p4); case (positive_eq p3 p4); auto.
intros H1; apply f_equal with ( f := xI ); auto.
intros H1 H2; case H1; injection H2; auto.
intros p3 rec p2; case p2; simpl; auto; (try (intros; discriminate)); intros p4.
generalize (rec p4); case (positive_eq p3 p4); auto.
intros H1; apply f_equal with ( f := xO ); auto.
intros H1 H2; case H1; injection H2; auto.
Qed.
 
(* equality test *)
Fixpoint PExpr_eq (e1 e2 : PExpr C) {struct e1} : bool :=
 match e1, e2 with
   PEc c1, PEc c2 => ceqb c1 c2
  | PEX p1, PEX p2 => positive_eq p1 p2
  | PEadd e3 e5, PEadd e4 e6 => if PExpr_eq e3 e4 then PExpr_eq e5 e6 else false
  | PEsub e3 e5, PEsub e4 e6 => if PExpr_eq e3 e4 then PExpr_eq e5 e6 else false
  | PEmul e3 e5, PEmul e4 e6 => if PExpr_eq e3 e4 then PExpr_eq e5 e6 else false
  | PEopp e3, PEopp e4 => PExpr_eq e3 e4
  | _, _ => false
 end.
 
Theorem PExpr_eq_semi_correct:
 forall l e1 e2, PExpr_eq e1 e2 = true ->  NPEeval l e1 == NPEeval l e2.
intros l e1; elim e1.
intros c1; intros e2; elim e2; simpl; (try (intros; discriminate)).
intros c2; apply (morph_eq CRmorph).
intros p1; intros e2; elim e2; simpl; (try (intros; discriminate)).
intros p2; generalize (positive_eq_correct p1 p2); case (positive_eq p1 p2);
 (try (intros; discriminate)); intros H; rewrite H; auto.
intros e3 rec1 e5 rec2 e2; case e2; simpl; (try (intros; discriminate)).
intros e4 e6; generalize (rec1 e4); case (PExpr_eq e3 e4);
 (try (intros; discriminate)); generalize (rec2 e6); case (PExpr_eq e5 e6);
 (try (intros; discriminate)); auto.
intros e3 rec1 e5 rec2 e2; case e2; simpl; (try (intros; discriminate)).
intros e4 e6; generalize (rec1 e4); case (PExpr_eq e3 e4);
 (try (intros; discriminate)); generalize (rec2 e6); case (PExpr_eq e5 e6);
 (try (intros; discriminate)); auto.
intros e3 rec1 e5 rec2 e2; case e2; simpl; (try (intros; discriminate)).
intros e4 e6; generalize (rec1 e4); case (PExpr_eq e3 e4);
 (try (intros; discriminate)); generalize (rec2 e6); case (PExpr_eq e5 e6);
 (try (intros; discriminate)); auto.
intros e3 rec e2; (case e2; simpl; (try (intros; discriminate))).
intros e4; generalize (rec e4); case (PExpr_eq e3 e4);
 (try (intros; discriminate)); auto.
Qed.

(* add *)
Definition NPEadd e1 e2 :=
  match e1, e2 with
    PEc c1, PEc c2 => PEc (cadd c1 c2)
  | PEc c, _ => if ceqb c cO then e2 else PEadd e1 e2
  |  _, PEc c => if ceqb c cO then e1 else PEadd e1 e2
  | _, _ => PEadd e1 e2
  end.

Theorem NPEadd_correct:
 forall l e1 e2, NPEeval l (NPEadd e1 e2) == NPEeval l (PEadd e1 e2).
Proof.
intros l e1 e2.
destruct e1; destruct e2; simpl in |- *; try reflexivity; try apply ceqb_rect;
 try (intro eq_c; rewrite eq_c in |- *); simpl in |- *;
 try rewrite (morph0 CRmorph) in |- *; try ring.
apply (morph_add CRmorph).
Qed.

(* mul *) 
Definition NPEmul x y :=
  match x, y with
    PEc c1, PEc c2 => PEc (cmul c1 c2)
  | PEc c, _ =>
      if ceqb c cI then y else if ceqb c cO then PEc cO else PEmul x y
  |  _, PEc c =>
      if ceqb c cI then x else if ceqb c cO then PEc cO else PEmul x y
  |  _, _ => PEmul x y
  end.
             
Theorem NPEmul_correct : forall l e1 e2,
  NPEeval l (NPEmul e1 e2) == NPEeval l (PEmul e1 e2).
intros l e1 e2.
destruct e1; destruct e2; simpl in |- *; try reflexivity;
 repeat apply ceqb_rect;
 try (intro eq_c; rewrite eq_c in |- *); simpl in |- *;
 try rewrite (morph0 CRmorph) in |- *;
 try rewrite (morph1 CRmorph) in |- *;
 try ring.
apply (morph_mul CRmorph).
Qed.

(* sub *)
Definition NPEsub e1 e2 :=
  match e1, e2 with
    PEc c1, PEc c2 => PEc (csub c1 c2)
  | PEc c, _ => if ceqb c cO then PEopp e2 else PEsub e1 e2
  |  _, PEc c => if ceqb c cO then e1 else PEsub e1 e2
  | _, _ => PEsub e1 e2
  end.

Theorem NPEsub_correct:
 forall l e1 e2,  NPEeval l (NPEsub e1 e2) == NPEeval l (PEsub e1 e2).
intros l e1 e2.
destruct e1; destruct e2; simpl in |- *; try reflexivity; try apply ceqb_rect;
 try (intro eq_c; rewrite eq_c in |- *); simpl in |- *;
 try rewrite (morph0 CRmorph) in |- *; try reflexivity;
 try (symmetry; apply rsub_0_l); try (symmetry; apply rsub_0_r).
apply (morph_sub CRmorph).
Qed.
 
(* opp *)
Definition NPEopp e1 :=
  match e1 with PEc c1 => PEc (copp c1) | _ => PEopp e1 end.
 
Theorem NPEopp_correct:
 forall l e1,  NPEeval l (NPEopp e1) == NPEeval l (PEopp e1).
intros l e1; case e1; simpl; auto.
intros; apply (morph_opp CRmorph).
Qed.
 
(* simplification *)
Fixpoint PExpr_simp (e : PExpr C) : PExpr C :=
 match e with
   PEadd e1 e2 => NPEadd (PExpr_simp e1) (PExpr_simp e2)
  | PEmul e1 e2 => NPEmul (PExpr_simp e1) (PExpr_simp e2)
  | PEsub e1 e2 => NPEsub (PExpr_simp e1) (PExpr_simp e2)
  | PEopp e1 => NPEopp (PExpr_simp e1)
  | _ => e
 end.
 
Theorem PExpr_simp_correct:
 forall l e,  NPEeval l (PExpr_simp e) == NPEeval l e.
intros l e; elim e; simpl; auto.
intros e1 He1 e2 He2.
transitivity (NPEeval l (PEadd (PExpr_simp e1) (PExpr_simp e2))); auto.
apply NPEadd_correct.
simpl; auto.
intros e1 He1 e2 He2.
transitivity (NPEeval l (PEsub (PExpr_simp e1) (PExpr_simp e2))); auto.
apply NPEsub_correct.
simpl; auto.
intros e1 He1 e2 He2.
transitivity (NPEeval l (PEmul (PExpr_simp e1) (PExpr_simp e2))); auto.
apply NPEmul_correct.
simpl; auto.
intros e1 He1.
transitivity (NPEeval l (PEopp (PExpr_simp e1))); auto.
apply NPEopp_correct.
simpl; auto.
Qed.


(****************************************************************************
                                                                          
                               Datastructure                              
                                                                          
  ***************************************************************************)

(* The input: syntax of a field expression *)

Inductive FExpr : Type :=
   FEc: C ->  FExpr
 | FEX: positive ->  FExpr
 | FEadd: FExpr -> FExpr ->  FExpr
 | FEsub: FExpr -> FExpr ->  FExpr
 | FEmul: FExpr -> FExpr ->  FExpr
 | FEopp: FExpr ->  FExpr
 | FEinv: FExpr ->  FExpr
 | FEdiv: FExpr -> FExpr ->  FExpr .

Fixpoint FEeval (l : list R) (pe : FExpr) {struct pe} : R :=
  match pe with
  | FEc c     => phi c
  | FEX x     => BinList.nth 0 x l
  | FEadd x y => FEeval l x + FEeval l y
  | FEsub x y => FEeval l x - FEeval l y
  | FEmul x y => FEeval l x * FEeval l y
  | FEopp x   => - FEeval l x
  | FEinv x   => / FEeval l x
  | FEdiv x y => FEeval l x / FEeval l y
  end.

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
  | e1 :: nil => ~ req (PEeval rO radd rmul rsub ropp phi l e1) rO
  | e1 :: l1 => ~ req (PEeval rO radd rmul rsub ropp phi l e1) rO /\ PCond l l1
  end.

Theorem PCond_cons_inv_l :
   forall l a l1, PCond l (a::l1) ->  ~ NPEeval l a == 0.
intros l a l1 H.
destruct l1; simpl in H |- *; trivial.
destruct H; trivial.
Qed.
 
Theorem PCond_cons_inv_r : forall l a l1, PCond l (a :: l1) ->  PCond l l1.
intros l a l1 H.
destruct l1; simpl in H |- *; trivial.
destruct H; trivial.
Qed.

Theorem PCond_app_inv_l: forall l l1 l2, PCond l (l1 ++ l2) ->  PCond l l1.
intros l l1 l2; elim l1; simpl app in |- *.
 simpl in |- *; auto.
 destruct l0; simpl in *.
  destruct l2; firstorder.
  firstorder.
Qed.
 
Theorem PCond_app_inv_r: forall l l1 l2, PCond l (l1 ++ l2) ->  PCond l l2.
intros l l1 l2; elim l1; simpl app; auto.
intros a l0 H H0; apply H; apply PCond_cons_inv_r with ( 1 := H0 ).
Qed.
 
(* An unsatisfiable condition: issued when a division by zero is detected *)
Definition absurd_PCond := cons (PEc cO) nil.

Lemma absurd_PCond_bottom : forall l, ~ PCond l absurd_PCond.
unfold absurd_PCond in |- *; simpl in |- *.
red in |- *; intros.
apply H.
apply (morph0 CRmorph).
Qed.

(***************************************************************************
                                                                          
                               Normalisation                              
                                                                          
  ***************************************************************************)


Fixpoint isIn (e1 e2: PExpr C) {struct e2}: option (PExpr C) :=
  match e2 with
  | PEmul e3 e4 =>
       match isIn e1 e3 with
         Some e5 => Some (NPEmul e5 e4)
       | None => match isIn e1 e4 with
                 | Some e5 => Some (NPEmul e3 e5)
                 | None => None
                 end
       end
  | _ =>
       if PExpr_eq e1 e2 then Some (PEc cI) else None
   end.

Theorem isIn_correct: forall l e1 e2,
  match isIn e1 e2 with 
    (Some e3) => NPEeval l e2 == NPEeval l (NPEmul e1 e3)
  |  _ => True
  end.
Proof.
intros l e1 e2; elim e2; simpl; auto.
  intros c;
   generalize (PExpr_eq_semi_correct l e1 (PEc c));
   case (PExpr_eq e1 (PEc c)); simpl; auto; intros H.
   rewrite NPEmul_correct; simpl; auto.
   rewrite H; auto; simpl. 
   rewrite (morph1 CRmorph); rewrite (ARmul_1_r Rsth ARth); auto.
  intros p;
   generalize (PExpr_eq_semi_correct l e1 (PEX C p));
   case (PExpr_eq e1 (PEX C p)); simpl; auto; intros H.
   rewrite NPEmul_correct; simpl; auto.
   rewrite H; auto; simpl. 
   rewrite (morph1 CRmorph); rewrite (ARmul_1_r Rsth ARth); auto.
 intros p Hrec p1 Hrec1.
   generalize (PExpr_eq_semi_correct l e1 (PEadd p p1));
   case (PExpr_eq e1 (PEadd p p1)); simpl; auto; intros H.
   rewrite NPEmul_correct; simpl; auto.
   rewrite H; auto; simpl. 
   rewrite (morph1 CRmorph); rewrite (ARmul_1_r Rsth ARth); auto.
 intros p Hrec p1 Hrec1.
   generalize (PExpr_eq_semi_correct l e1 (PEsub p p1));
   case (PExpr_eq e1 (PEsub p p1)); simpl; auto; intros H.
   rewrite NPEmul_correct; simpl; auto.
   rewrite H; auto; simpl. 
   rewrite (morph1 CRmorph); rewrite (ARmul_1_r Rsth ARth); auto.
 intros p; case (isIn e1 p).
   intros p2 Hrec p1 Hrec1.
   rewrite Hrec; auto; simpl. 
   repeat (rewrite NPEmul_correct; simpl; auto).
   intros _ p1; case (isIn e1 p1); auto.
   intros p2 H; rewrite H.
   repeat (rewrite NPEmul_correct; simpl; auto).
   ring.
  intros p;
   generalize (PExpr_eq_semi_correct l e1 (PEopp p));
   case (PExpr_eq e1 (PEopp p)); simpl; auto; intros H.
   rewrite NPEmul_correct; simpl; auto.
   rewrite H; auto; simpl. 
   rewrite (morph1 CRmorph); rewrite (ARmul_1_r Rsth ARth); auto.
Qed.

Record rsplit : Type := mk_rsplit {
   rsplit_left : PExpr C;
   rsplit_common : PExpr C;
   rsplit_right : PExpr C}.

(* Stupid name clash *)
Let left := rsplit_left.
Let right := rsplit_right.
Let common := rsplit_common.

Fixpoint split (e1 e2: PExpr C) {struct e1}: rsplit :=
  match e1 with
  | PEmul e3 e4 =>
      let r1 := split e3 e2 in
      let r2 := split e4 (right r1) in
          mk_rsplit (NPEmul (left r1) (left r2))
                    (NPEmul (common r1) (common r2))
                    (right r2)
  | _ => 
       match isIn e1 e2 with
         Some e3 => mk_rsplit (PEc cI) e1 e3
       | None => mk_rsplit e1 (PEc cI) e2
       end
  end. 

Theorem split_correct: forall l e1 e2,
  NPEeval l e1 == NPEeval l (NPEmul (left (split e1 e2))
                                   (common (split e1 e2)))
/\
  NPEeval l e2 == NPEeval l (NPEmul (right (split e1 e2))
                                   (common (split e1 e2))).
Proof.
intros l e1; elim e1; simpl; auto.
  intros c e2; generalize (isIn_correct l (PEc c) e2);
    case (isIn (PEc c) e2); auto; intros p;
    [intros Hp1; rewrite Hp1 | idtac];
    simpl left; simpl common;  simpl right; auto;
    repeat rewrite NPEmul_correct; simpl; split; 
    try rewrite  (morph1 CRmorph); ring.
  intros p e2; generalize (isIn_correct l (PEX C p) e2);
    case (isIn (PEX C p) e2); auto; intros p1;
    [intros Hp1; rewrite Hp1 | idtac];
    simpl left; simpl common;  simpl right; auto;
    repeat rewrite NPEmul_correct; simpl; split; 
    try rewrite  (morph1 CRmorph); ring.
  intros p1 _ p2 _ e2; generalize (isIn_correct l (PEadd p1 p2) e2);
    case (isIn (PEadd p1 p2) e2); auto; intros p;
    [intros Hp1; rewrite Hp1 | idtac];
    simpl left; simpl common;  simpl right; auto;
    repeat rewrite NPEmul_correct; simpl; split; 
    try rewrite  (morph1 CRmorph); ring.
  intros p1 _ p2 _ e2; generalize (isIn_correct l (PEsub p1 p2) e2);
    case (isIn (PEsub p1 p2) e2); auto; intros p;
    [intros Hp1; rewrite Hp1 | idtac];
    simpl left; simpl common;  simpl right; auto;
    repeat rewrite NPEmul_correct; simpl; split; 
    try rewrite  (morph1 CRmorph); ring.
  intros p1 Hp1 p2 Hp2 e2.
    repeat rewrite NPEmul_correct; simpl; split.
    case (Hp1 e2); case (Hp2 (right (split p1 e2))).
    intros tmp1 _ tmp2 _; rewrite tmp1; rewrite tmp2.
    repeat rewrite NPEmul_correct; simpl.
    ring.
    case (Hp1 e2); case (Hp2 (right (split p1 e2))).
    intros _ tmp1 _ tmp2; rewrite tmp2;
    repeat rewrite NPEmul_correct; simpl.
    rewrite tmp1.
    repeat rewrite NPEmul_correct; simpl.
    ring.
  intros p _ e2; generalize (isIn_correct l (PEopp p) e2);
    case (isIn (PEopp p) e2); auto; intros p1;
    [intros Hp1; rewrite Hp1 | idtac];
    simpl left; simpl common;  simpl right; auto;
    repeat rewrite NPEmul_correct; simpl; split; 
    try rewrite  (morph1 CRmorph); ring.
Qed.


Theorem split_correct_l: forall l e1 e2,
  NPEeval l e1 == NPEeval l (NPEmul (left (split e1 e2))
                                   (common (split e1 e2))).
Proof.
intros l e1 e2; case (split_correct l e1 e2); auto.
Qed.

Theorem split_correct_r: forall l e1 e2,
  NPEeval l e2 == NPEeval l (NPEmul (right (split e1 e2))
                                   (common (split e1 e2))).
Proof.
intros l e1 e2; case (split_correct l e1 e2); auto.
Qed.

Fixpoint Fnorm (e : FExpr) : linear := 
  match e with
  | FEc c => mk_linear (PEc c) (PEc cI) nil
  | FEX x => mk_linear (PEX C x) (PEc cI) nil
  | FEadd e1 e2 =>
      let x := Fnorm e1 in
      let y := Fnorm e2 in
      let s := split (denum x) (denum y) in
      mk_linear
        (NPEadd (NPEmul (num x) (right s)) (NPEmul (num y) (left s)))
        (NPEmul (left s) (NPEmul (right s) (common s)))
        (condition x ++ condition y)
 
  | FEsub e1 e2 =>
      let x := Fnorm e1 in
      let y := Fnorm e2 in
      let s := split (denum x) (denum y) in
      mk_linear
        (NPEsub (NPEmul (num x) (right s)) (NPEmul (num y) (left s)))
        (NPEmul (left s) (NPEmul (right s) (common s)))
        (condition x ++ condition y)
  | FEmul e1 e2 =>
      let x := Fnorm e1 in
      let y := Fnorm e2 in
      mk_linear (NPEmul (num x) (num y))
        (NPEmul (denum x) (denum y))
        (condition x ++ condition y)
  | FEopp e1 =>
      let x := Fnorm e1 in
      mk_linear (NPEopp (num x)) (denum x) (condition x)
  | FEinv e1 =>
      let x := Fnorm e1 in
      mk_linear (denum x) (num x) (num x :: condition x)
  | FEdiv e1 e2 =>
      let x := Fnorm e1 in
      let y := Fnorm e2 in
      mk_linear (NPEmul (num x) (denum y))
        (NPEmul (denum x) (num y))
        (num y :: condition x ++ condition y)
  end.


(* Example *)
(*
Eval compute
   in (Fnorm
        (FEdiv
          (FEc cI)
          (FEadd (FEinv (FEX xH%positive)) (FEinv (FEX (xO xH)%positive))))).
*)

Theorem Pcond_Fnorm:
 forall l e,
 PCond l (condition (Fnorm e)) ->  ~ NPEeval l (denum (Fnorm e)) == 0.
intros l e; elim e.
 simpl in |- *; intros _ _; rewrite (morph1 CRmorph) in |- *; exact rI_neq_rO.
 simpl in |- *; intros _ _; rewrite (morph1 CRmorph) in |- *; exact rI_neq_rO.
 intros e1 Hrec1 e2 Hrec2 Hcond.
   simpl condition in Hcond.
   simpl denum in |- *.
   rewrite NPEmul_correct in |- *.
   simpl in |- *.
   apply field_is_integral_domain.
   intros HH; case Hrec1; auto.
     apply PCond_app_inv_l with (1 := Hcond).
   rewrite (split_correct_l l (denum (Fnorm e1)) (denum (Fnorm e2))).
   rewrite NPEmul_correct; simpl; rewrite HH; ring.
   intros HH; case Hrec2; auto.
     apply PCond_app_inv_r with (1 := Hcond).
   rewrite (split_correct_r l (denum (Fnorm e1)) (denum (Fnorm e2))); auto.
 intros e1 Hrec1 e2 Hrec2 Hcond.
   simpl condition in Hcond.
   simpl denum in |- *.
   rewrite NPEmul_correct in |- *.
   simpl in |- *.
   apply field_is_integral_domain.
   intros HH; case Hrec1; auto.
     apply PCond_app_inv_l with (1 := Hcond).
   rewrite (split_correct_l l (denum (Fnorm e1)) (denum (Fnorm e2))).
   rewrite NPEmul_correct; simpl; rewrite HH; ring.
   intros HH; case Hrec2; auto.
     apply PCond_app_inv_r with (1 := Hcond).
   rewrite (split_correct_r l (denum (Fnorm e1)) (denum (Fnorm e2))); auto.
 intros e1 Hrec1 e2 Hrec2 Hcond.
   simpl condition in Hcond.
   simpl denum in |- *.
   rewrite NPEmul_correct in |- *.
   simpl in |- *.
   apply field_is_integral_domain.
  apply Hrec1.
    apply PCond_app_inv_l with (1 := Hcond).
  apply Hrec2.
    apply PCond_app_inv_r with (1 := Hcond).
 intros e1 Hrec1 Hcond.
   simpl condition in Hcond.
   simpl denum in |- *.
   auto.
 intros e1 Hrec1 Hcond.
   simpl condition in Hcond.
   simpl denum in |- *.
   apply PCond_cons_inv_l with (1:=Hcond).
 intros e1 Hrec1 e2 Hrec2 Hcond.
   simpl condition in Hcond.
   simpl denum in |- *.
   rewrite NPEmul_correct in |- *.
   simpl in |- *.
   apply field_is_integral_domain.
  apply Hrec1.
    specialize PCond_cons_inv_r with (1:=Hcond); intro Hcond1.
    apply PCond_app_inv_l with (1 := Hcond1).
   apply PCond_cons_inv_l with (1:=Hcond).
Qed.
Hint Resolve Pcond_Fnorm.


(***************************************************************************
                                                                          
                       Main theorem                                       
                                                                          
  ***************************************************************************)

Theorem Fnorm_FEeval_PEeval:
 forall l fe,
 PCond l (condition (Fnorm fe)) ->
 FEeval l fe == NPEeval l (num (Fnorm fe)) / NPEeval l (denum (Fnorm fe)).
Proof.
intros l fe; elim fe; simpl.
intros c H; rewrite CRmorph.(morph1); apply rdiv1.
intros p H; rewrite CRmorph.(morph1); apply rdiv1.
intros e1 He1 e2 He2 HH.
assert (HH1: PCond l (condition (Fnorm e1))).
apply PCond_app_inv_l with ( 1 := HH ).
assert (HH2: PCond l (condition (Fnorm e2))).
apply PCond_app_inv_r with ( 1 := HH ).
rewrite (He1 HH1); rewrite (He2 HH2).
rewrite NPEadd_correct; simpl.
repeat rewrite NPEmul_correct; simpl.
generalize (split_correct_l l (denum (Fnorm e1)) (denum (Fnorm e2)))
   (split_correct_r l (denum (Fnorm e1)) (denum (Fnorm e2))).
repeat rewrite NPEmul_correct; simpl.
intros U1 U2; rewrite U1; rewrite U2.
apply rdiv2b; auto.
  rewrite <- U1; auto.
  rewrite <- U2; auto.

intros e1 He1 e2 He2 HH.
assert (HH1: PCond l (condition (Fnorm e1))).
apply PCond_app_inv_l with ( 1 := HH ).
assert (HH2: PCond l (condition (Fnorm e2))).
apply PCond_app_inv_r with ( 1 := HH ).
rewrite (He1 HH1); rewrite (He2 HH2).
rewrite NPEsub_correct; simpl.
repeat rewrite NPEmul_correct; simpl.
generalize (split_correct_l l (denum (Fnorm e1)) (denum (Fnorm e2)))
   (split_correct_r l (denum (Fnorm e1)) (denum (Fnorm e2))).
repeat rewrite NPEmul_correct; simpl.
intros U1 U2; rewrite U1; rewrite U2.
apply rdiv3b; auto.
  rewrite <- U1; auto.
  rewrite <- U2; auto.

intros e1 He1 e2 He2 HH.
assert (HH1: PCond l (condition (Fnorm e1))).
apply PCond_app_inv_l with ( 1 := HH ).
assert (HH2: PCond l (condition (Fnorm e2))).
apply PCond_app_inv_r with ( 1 := HH ).
rewrite (He1 HH1); rewrite (He2 HH2).
repeat rewrite NPEmul_correct; simpl.
apply rdiv4; auto.

intros e1 He1 HH.
rewrite NPEopp_correct; simpl; rewrite (He1 HH); apply rdiv5; auto.

intros e1 He1 HH.
assert (HH1: PCond l (condition (Fnorm e1))).
apply PCond_cons_inv_r with ( 1 := HH ).
rewrite (He1 HH1); apply rdiv6; auto.
apply PCond_cons_inv_l with ( 1 := HH ).

intros e1 He1 e2 He2 HH.
assert (HH1: PCond l (condition (Fnorm e1))).
apply PCond_app_inv_l with (condition (Fnorm e2)).
apply PCond_cons_inv_r with ( 1 := HH ).
assert (HH2: PCond l (condition (Fnorm e2))).
apply PCond_app_inv_r with (condition (Fnorm e1)).
apply PCond_cons_inv_r with ( 1 := HH ).
rewrite (He1 HH1); rewrite (He2 HH2).
repeat rewrite NPEmul_correct;simpl.
apply rdiv7; auto.
apply PCond_cons_inv_l with ( 1 := HH ).
Qed.

Theorem Fnorm_crossproduct:
 forall l fe1 fe2,
 let nfe1 := Fnorm fe1 in
 let nfe2 := Fnorm fe2 in
 NPEeval l (PEmul (num nfe1) (denum nfe2)) ==
 NPEeval l (PEmul (num nfe2) (denum nfe1)) ->
 PCond l (condition nfe1 ++ condition nfe2) ->
 FEeval l fe1 == FEeval l fe2.
intros l fe1 fe2 nfe1 nfe2 Hcrossprod Hcond; subst nfe1 nfe2.
rewrite Fnorm_FEeval_PEeval in |- *.
 apply PCond_app_inv_l with (1 := Hcond).
 rewrite Fnorm_FEeval_PEeval in |- *.
  apply PCond_app_inv_r with (1 := Hcond).
  apply cross_product_eq; trivial.
   apply Pcond_Fnorm.
     apply PCond_app_inv_l with (1 := Hcond).
   apply Pcond_Fnorm.
     apply PCond_app_inv_r with (1 := Hcond).
Qed.

(* Correctness lemmas of reflexive tactics *)

Theorem Fnorm_correct:
 forall l fe,
 Peq ceqb (Nnorm (num (Fnorm fe))) (Pc cO) = true ->
 PCond l (condition (Fnorm fe)) ->  FEeval l fe == 0.
intros l fe H H1;
 apply eq_trans with (1 := Fnorm_FEeval_PEeval l fe H1).
apply rdiv8; auto.
transitivity (NPEeval l (PEc cO)); auto.
apply (ring_correct Rsth Reqe ARth CRmorph); auto.
simpl; apply (morph0 CRmorph); auto.
Qed.

(* simplify a field expression into a fraction *)
(* TODO: simplify when den is constant... *)
Definition display_linear l num den :=
  NPphi_dev l num / NPphi_dev l den.

Theorem Pphi_dev_div_ok:
 forall l fe nfe,
 Fnorm fe = nfe ->
 PCond l (condition nfe) ->
 FEeval l fe == display_linear l (Nnorm (num nfe)) (Nnorm (denum nfe)).
Proof.
  intros l fe nfe eq_nfe H; subst nfe.
  apply eq_trans with (1 := Fnorm_FEeval_PEeval _ _ H).
  unfold display_linear; apply SRdiv_ext;
  apply (Pphi_dev_ok Rsth Reqe ARth CRmorph); reflexivity.
Qed.

(* solving a field equation *)
Theorem Fnorm_correct2:
 forall l fe1 fe2 nfe1 nfe2,
 Fnorm fe1 = nfe1 ->
 Fnorm fe2 = nfe2 ->
 Peq ceqb (Nnorm (PEmul (num nfe1) (denum nfe2)))
          (Nnorm (PEmul (num nfe2) (denum nfe1))) = true ->
 PCond l (condition nfe1 ++ condition nfe2) ->
 FEeval l fe1 == FEeval l fe2.
Proof.
intros l fe1 fe2 nfe1 nfe2 eq1 eq2 Hnorm Hcond; subst nfe1 nfe2.
apply Fnorm_crossproduct; trivial.
apply (ring_correct Rsth Reqe ARth CRmorph); trivial.
Qed.

(* simplify a field equation : generate the crossproduct and simplify
   polynomials *)
Theorem Field_simplify_eq_correct :
 forall l fe1 fe2 nfe1 nfe2,
 Fnorm fe1 = nfe1 ->
 Fnorm fe2 = nfe2 ->
 NPphi_dev l (Nnorm (PEmul (num nfe1) (denum nfe2))) ==
 NPphi_dev l (Nnorm (PEmul (num nfe2) (denum nfe1))) ->
 PCond l (condition nfe1 ++ condition nfe2) ->
 FEeval l fe1 == FEeval l fe2.
Proof.
intros l fe1 fe2 nfe1 nfe2 eq1 eq2 Hcrossprod Hcond;  subst nfe1 nfe2.
apply Fnorm_crossproduct; trivial.
rewrite (Pphi_dev_gen_ok Rsth Reqe ARth CRmorph) in |- *.
rewrite (Pphi_dev_gen_ok Rsth Reqe ARth CRmorph) in |- *.
trivial.
Qed.

Section Fcons_impl.

Variable Fcons : PExpr C -> list (PExpr C) -> list (PExpr C).

Hypothesis PCond_fcons_inv : forall l a l1,
  PCond l (Fcons a l1) ->  ~ NPEeval l a == 0 /\ PCond l l1.

Fixpoint Fapp (l m:list (PExpr C)) {struct l} : list (PExpr C) :=
  match l with
  | nil => m
  | cons a l1 => Fcons a (Fapp l1 m)
  end.

Lemma fcons_correct : forall l l1,
  PCond l (Fapp l1 nil) -> PCond l l1.
induction l1; simpl in |- *; intros.
 trivial.
 elim PCond_fcons_inv with (1 := H); intros.
   destruct l1; auto.
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
 forall l a l1, PCond l (Fcons a l1) ->  ~ NPEeval l a == 0 /\ PCond l l1.
intros l a l1; elim l1; simpl Fcons; auto.
simpl; auto.
intros a0 l0.
generalize (PExpr_eq_semi_correct l a a0); case (PExpr_eq a a0).
intros H H0 H1; split; auto.
rewrite H; auto.
generalize (PCond_cons_inv_l _ _ _ H1); simpl; auto.
intros H H0 H1;
 assert (Hp: ~ NPEeval l a0 == 0 /\ (~ NPEeval l a == 0 /\ PCond l l0)).
split.
generalize (PCond_cons_inv_l _ _ _ H1); simpl; auto.
apply H0.
generalize (PCond_cons_inv_r _ _ _ H1); simpl; auto.
generalize Hp; case l0; simpl; intuition.
Qed.

(* equality of normal forms rather than syntactic equality *)
Fixpoint Fcons0 (e:PExpr C) (l:list (PExpr C)) {struct l} : list (PExpr C) :=
 match l with
   nil       => cons e nil
 | cons a l1 =>
     if Peq ceqb (Nnorm e) (Nnorm a) then l else cons a (Fcons0 e l1)
 end.
 
Theorem PFcons0_fcons_inv:
 forall l a l1, PCond l (Fcons0 a l1) ->  ~ NPEeval l a == 0 /\ PCond l l1.
intros l a l1; elim l1; simpl Fcons0; auto.
simpl; auto.
intros a0 l0.
generalize (ring_correct Rsth Reqe ARth CRmorph l a a0);
  case (Peq ceqb (Nnorm a) (Nnorm a0)).
intros H H0 H1; split; auto.
rewrite H; auto.
generalize (PCond_cons_inv_l _ _ _ H1); simpl; auto.
intros H H0 H1;
 assert (Hp: ~ NPEeval l a0 == 0 /\ (~ NPEeval l a == 0 /\ PCond l l0)).
split.
generalize (PCond_cons_inv_l _ _ _ H1); simpl; auto.
apply H0.
generalize (PCond_cons_inv_r _ _ _ H1); simpl; auto.
generalize Hp; case l0; simpl; intuition.
Qed.

Fixpoint Fcons00 (e:PExpr C) (l:list (PExpr C)) {struct e} : list (PExpr C) :=
 match e with
   PEmul e1 e2 => Fcons00 e1 (Fcons00 e2 l)
 | _ => Fcons0 e l
 end.

Theorem PFcons00_fcons_inv:
  forall l a l1, PCond l (Fcons00 a l1) -> ~ NPEeval l a == 0 /\ PCond l l1.
intros l a; elim a; try (intros; apply PFcons0_fcons_inv; auto; fail).
 intros p H p0 H0 l1 H1.
   simpl in H1.
   case (H _ H1); intros H2 H3.
   case (H0 _ H3); intros H4 H5; split; auto.
   simpl in |- *.
   apply field_is_integral_domain; trivial.
Qed.


Definition Pcond_simpl_gen := 
  fcons_correct _ PFcons00_fcons_inv.


(* Specific case when the equality test of coefs is complete w.r.t. the
   field equality: non-zero coefs can be eliminated, and opposite can
   be simplified (if -1 <> 0) *)

Hypothesis ceqb_complete : forall c1 c2, phi c1 == phi c2 -> ceqb c1 c2 = true.

Lemma ceqb_rect_complete : forall c1 c2 (A:Type) (x y:A) (P:A->Type),
  (phi c1 == phi c2 -> P x) ->
  (~ phi c1 == phi c2 -> P y) ->
  P (if ceqb c1 c2 then x else y).
Proof.
intros.
generalize (fun h => X (morph_eq CRmorph c1 c2 h)).
generalize (@ceqb_complete c1 c2).
case (c1 ?=! c2); auto; intros.
apply X0.
red in |- *; intro.
absurd (false = true); auto;  discriminate.
Qed.

Fixpoint Fcons1 (e:PExpr C) (l:list (PExpr C)) {struct e} : list (PExpr C) :=
 match e with
   PEmul e1 e2 => Fcons1 e1 (Fcons1 e2 l)
 | PEopp e => if ceqb (copp cI) cO then absurd_PCond else Fcons1 e l
 | PEc c => if ceqb c cO then absurd_PCond else l
 | _ => Fcons0 e l
 end.

Theorem PFcons1_fcons_inv:
  forall l a l1, PCond l (Fcons1 a l1) -> ~ NPEeval l a == 0 /\ PCond l l1.
intros l a; elim a; try (intros; apply PFcons0_fcons_inv; auto; fail).
 simpl in |- *; intros c l1.
   apply ceqb_rect_complete; intros.
  elim (@absurd_PCond_bottom l H0).
  split; trivial.
    rewrite <- (morph0 CRmorph) in |- *; trivial.
 intros p H p0 H0 l1 H1.
   simpl in H1.
   case (H _ H1); intros H2 H3.
   case (H0 _ H3); intros H4 H5; split; auto.
   simpl in |- *.
   apply field_is_integral_domain; trivial.
 simpl in |- *; intros p H l1.
   apply ceqb_rect_complete; intros.
  elim (@absurd_PCond_bottom l H1).
  destruct (H _ H1).
    split; trivial.
    apply ropp_neq_0; trivial.
    rewrite (morph_opp CRmorph) in H0.
    rewrite (morph1 CRmorph) in H0.
    rewrite (morph0 CRmorph) in H0.
    trivial.
Qed.

Definition Fcons2 e l := Fcons1 (PExpr_simp e) l.
 
Theorem PFcons2_fcons_inv:
 forall l a l1, PCond l (Fcons2 a l1) -> ~ NPEeval l a == 0 /\ PCond l l1.
unfold Fcons2 in |- *; intros l a l1 H; split;
 case (PFcons1_fcons_inv l (PExpr_simp a) l1); auto.
intros H1 H2 H3; case H1.
transitivity (NPEeval l a); trivial.
apply PExpr_simp_correct.
Qed.

Definition Pcond_simpl_complete := 
  fcons_correct _ PFcons2_fcons_inv.

End Fcons_simpl.

Let Mpc := MPcond_map cO cI cadd cmul csub copp ceqb.
Let Mp := MPcond_dev rO rI radd rmul req cO cI ceqb phi.
Let Subst := PNSubstL cO cI cadd cmul ceqb.

(* simplification + rewriting *)
Theorem Field_subst_correct :
forall l ul fe m n,
 PCond l (Fapp Fcons00 (condition (Fnorm fe)) nil) ->
 Mp (Mpc ul) l ->
 Peq ceqb (Subst (Nnorm (num (Fnorm fe))) (Mpc ul) m n) (Pc cO) = true ->
 FEeval l fe == 0.
intros l ul fe m n H H1 H2.
assert (H3 := (Pcond_simpl_gen _ _ H)).
apply eq_trans with (1 := Fnorm_FEeval_PEeval l fe 
                           (Pcond_simpl_gen _ _ H)).
apply rdiv8; auto.
rewrite (PNSubstL_dev_ok Rsth Reqe ARth CRmorph m n
              _ (num (Fnorm fe)) l H1).
rewrite <-(Ring_polynom.Pphi_Pphi_dev Rsth Reqe ARth CRmorph).
rewrite (fun x => Peq_ok Rsth Reqe CRmorph x (Pc cO)); auto.
simpl; apply (morph0 CRmorph); auto.
Qed.


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
   Add Setoid R req Rsth as R_setoid3.
 Variable Reqe : ring_eq_ext radd rmul ropp req.
   Add Morphism radd : radd_ext3.  exact (Radd_ext Reqe). Qed.
   Add Morphism rmul : rmul_ext3.  exact (Rmul_ext Reqe). Qed.
   Add Morphism ropp : ropp_ext3.  exact (Ropp_ext Reqe). Qed.

Section AlmostField.

 Variable AFth : almost_field_theory rO rI radd rmul rsub ropp rdiv rinv req.
 Let ARth := AFth.(AF_AR).
 Let rI_neq_rO := AFth.(AF_1_neq_0).
 Let rdiv_def := AFth.(AFdiv_def).
 Let rinv_l := AFth.(AFinv_l).

Hypothesis S_inj : forall x y, 1+x==1+y -> x==y.

Hypothesis gen_phiPOS_not_0 : forall p, ~ gen_phiPOS1 rI radd rmul p == 0.

Lemma add_inj_r : forall p x y,
   gen_phiPOS1 rI radd rmul p + x == gen_phiPOS1 rI radd rmul p + y -> x==y.
intros p x y.
elim p using Pind; simpl in |- *; intros.
 apply S_inj; trivial.
 apply H.
   apply S_inj.
   repeat rewrite (ARadd_assoc ARth) in |- *.
   rewrite <- (ARgen_phiPOS_Psucc Rsth Reqe ARth) in |- *; trivial.
Qed.

Lemma gen_phiPOS_inj : forall x y,
  gen_phiPOS rI radd rmul x == gen_phiPOS rI radd rmul y ->
  x = y.
intros x y.
repeat rewrite <- (same_gen Rsth Reqe ARth) in |- *.
ElimPcompare x y; intro.
 intros.
   apply Pcompare_Eq_eq; trivial.
 intro.
   elim gen_phiPOS_not_0 with (y - x)%positive.
   apply add_inj_r with x.
   symmetry  in |- *.
   rewrite (ARadd_0_r Rsth ARth) in |- *.
   rewrite <- (ARgen_phiPOS_add Rsth Reqe ARth) in |- *.
   rewrite Pplus_minus in |- *; trivial.
   change Eq with (CompOpp Eq) in |- *.
   rewrite <- Pcompare_antisym in |- *; trivial.
   rewrite H in |- *; trivial.
 intro.
   elim gen_phiPOS_not_0 with (x - y)%positive.
   apply add_inj_r with y.
   rewrite (ARadd_0_r Rsth ARth) in |- *.
   rewrite <- (ARgen_phiPOS_add Rsth Reqe ARth) in |- *.
   rewrite Pplus_minus in |- *; trivial.
Qed.


Lemma gen_phiN_inj : forall x y,
  gen_phiN rO rI radd rmul x == gen_phiN rO rI radd rmul y ->
  x = y.
destruct x; destruct y; simpl in |- *; intros; trivial.
 elim gen_phiPOS_not_0 with p.
   symmetry  in |- *.
   rewrite (same_gen Rsth Reqe ARth) in |- *; trivial.
 elim gen_phiPOS_not_0 with p.
   rewrite (same_gen Rsth Reqe ARth) in |- *; trivial.
 rewrite gen_phiPOS_inj with (1 := H) in |- *; trivial.
Qed.

Lemma gen_phiN_complete : forall x y,
  gen_phiN rO rI radd rmul x == gen_phiN rO rI radd rmul y ->
  Neq_bool x y = true.
intros.
 replace y with x.
 unfold Neq_bool in |- *.
   rewrite Ncompare_refl in |- *; trivial.
 apply gen_phiN_inj; trivial.
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

Lemma ring_S_inj : forall x y, 1+x==1+y -> x==y.
intros.
transitivity (x + (1 + - (1))).
 rewrite (Ropp_def Rth) in |- *.
   symmetry  in |- *.
   apply (ARadd_0_r Rsth ARth).
 transitivity (y + (1 + - (1))).
  repeat rewrite <- (ARplus_assoc ARth) in |- *.
    repeat rewrite (ARadd_assoc ARth) in |- *.
    apply (Radd_ext Reqe).
   repeat rewrite <- (ARadd_sym ARth 1) in |- *.
     trivial.
   reflexivity.
  rewrite (Ropp_def Rth) in |- *.
    apply (ARadd_0_r Rsth ARth).
Qed.


 Hypothesis gen_phiPOS_not_0 : forall p, ~ gen_phiPOS1 rI radd rmul p == 0.

Let gen_phiPOS_inject :=
   gen_phiPOS_inj AFth ring_S_inj gen_phiPOS_not_0.

Lemma gen_phiPOS_discr_sgn : forall x y,
  ~ gen_phiPOS rI radd rmul x == - gen_phiPOS rI radd rmul y.
red in |- *; intros.
apply gen_phiPOS_not_0 with (y + x)%positive.
rewrite (ARgen_phiPOS_add Rsth Reqe ARth) in |- *.
transitivity (gen_phiPOS1 1 radd rmul y + - gen_phiPOS1 1 radd rmul y).
 apply (Radd_ext Reqe); trivial.
  reflexivity.
  rewrite (same_gen Rsth Reqe ARth) in |- *.
    rewrite (same_gen Rsth Reqe ARth) in |- *.
    trivial.
 apply (Ropp_def Rth).
Qed.

Lemma gen_phiZ_inj : forall x y,
  gen_phiZ rO rI radd rmul ropp x == gen_phiZ rO rI radd rmul ropp y ->
  x = y.
destruct x; destruct y; simpl in |- *; intros.
 trivial.
 elim gen_phiPOS_not_0 with p.
   rewrite (same_gen Rsth Reqe ARth) in |- *.
   symmetry  in |- *; trivial.
 elim gen_phiPOS_not_0 with p.
   rewrite (same_gen Rsth Reqe ARth) in |- *.
   rewrite <- (Ropp_opp Rsth Reqe Rth (gen_phiPOS 1 radd rmul p)) in |- *.
   rewrite <- H in |- *.
   apply (ARopp_zero Rsth Reqe ARth).
 elim gen_phiPOS_not_0 with p.
   rewrite (same_gen Rsth Reqe ARth) in |- *.
   trivial.
 rewrite gen_phiPOS_inject  with (1 := H) in |- *; trivial.
 elim gen_phiPOS_discr_sgn with (1 := H).
 elim gen_phiPOS_not_0 with p.
   rewrite (same_gen Rsth Reqe ARth) in |- *.
   rewrite <- (Ropp_opp Rsth Reqe Rth (gen_phiPOS 1 radd rmul p)) in |- *.
   rewrite H in |- *.
   apply (ARopp_zero Rsth Reqe ARth).
 elim gen_phiPOS_discr_sgn with p0 p.
   symmetry  in |- *; trivial.
 replace p0 with p; trivial.
   apply gen_phiPOS_inject.
   rewrite <- (Ropp_opp Rsth Reqe Rth (gen_phiPOS 1 radd rmul p)) in |- *.
   rewrite <- (Ropp_opp Rsth Reqe Rth (gen_phiPOS 1 radd rmul p0)) in |- *.
   rewrite H in |- *; trivial.
   reflexivity.
Qed.

Lemma gen_phiZ_complete : forall x y,
  gen_phiZ rO rI radd rmul ropp x == gen_phiZ rO rI radd rmul ropp y ->
  Zeq_bool x y = true.
intros.
 replace y with x.
 unfold Zeq_bool in |- *.
   rewrite Zcompare_refl in |- *; trivial.
 apply gen_phiZ_inj; trivial.
Qed.

End Field.

End Complete.

