Require Import Ring_polynom InitialRing Field Field_tac Ring.

Require Export Rdefinitions.
Require Export Raxioms.
Require Export RIneq.

Section RField.

Notation NPEeval := (PEeval 0%R Rplus Rmult Rminus Ropp
   (gen_phiZ 0%R 1%R Rplus Rmult Ropp)).
Notation NPCond :=
 (PCond _ 0%R Rplus Rmult Rminus Ropp (@eq R) _
   (gen_phiZ 0%R 1%R Rplus Rmult Ropp)).
(*
Lemma RTheory : ring_theory 0%R 1%R Rplus Rmult Rminus Ropp (eq (A:=R)).
Proof.
constructor.
 intro; apply Rplus_0_l.
 exact Rplus_comm.
 symmetry  in |- *; apply Rplus_assoc.
 intro; apply Rmult_1_l.
 exact Rmult_comm.
 symmetry  in |- *; apply Rmult_assoc.
 intros m n p.
   rewrite Rmult_comm in |- *.
   rewrite (Rmult_comm n p) in |- *.
   rewrite (Rmult_comm m p) in |- *.
   apply Rmult_plus_distr_l.
 reflexivity.
 exact Rplus_opp_r.
Qed.
Add Ring Rring : RTheory Abstract.
*)
Notation Rset := (Eqsth R).
Notation Rext := (Eq_ext Rplus Rmult Ropp).
Notation Rmorph := (gen_phiZ_morph Rset Rext RTheory).

(*
Adds Field RF : Rfield Abstract.
*)

Lemma Rlt_n_Sn : forall x, (x < x + 1)%R.
Proof.
intro.
elim archimed with x; intros.
destruct H0.
 apply Rlt_trans with (IZR (up x)); trivial.
    replace (IZR (up x)) with (x + (IZR (up x) - x))%R.
  apply Rplus_lt_compat_l; trivial.
  unfold Rminus in |- *.
    rewrite (Rplus_comm (IZR (up x)) (- x)) in |- *.
    rewrite <- Rplus_assoc in |- *.
    rewrite Rplus_opp_r in |- *.
    apply Rplus_0_l.
 elim H0.
   unfold Rminus in |- *.
   rewrite (Rplus_comm (IZR (up x)) (- x)) in |- *.
   rewrite <- Rplus_assoc in |- *.
   rewrite Rplus_opp_r in |- *.
   rewrite Rplus_0_l in |- *; trivial.
Qed.


(*
Lemma Rdiscr_0_2 : (2 <> 0)%R.
red in |- *; intro.
assert (0 < 1)%R.
 elim (archimed 0); intros.
   unfold Rminus in H1.
   rewrite (ARopp_zero Rset Rext (Rth_ARth Rset Rext RTheory)) in H1.
   rewrite (ARadd_0_r Rset (Rth_ARth Rset Rext RTheory)) in H1.
   destruct H1.
  apply Rlt_trans with (IZR (up 0)); trivial.
  elim H1; trivial.
 assert (1 < 2)%R.
  pattern 1%R at 1 in |- *.
     replace 1%R with (1 + 0)%R.
   apply Rplus_lt_compat_l.
     trivial.
   rewrite (ARadd_0_r Rset (Rth_ARth Rset Rext RTheory)) in |- *.
     trivial.
  apply (Rlt_asym 0 1); trivial.
    elim H; trivial.
Qed.
*)

Lemma Rgen_phiPOS : forall x, (gen_phiPOS1 1 Rplus Rmult x > 0)%R.
unfold Rgt in |- *.
induction x; simpl in |- *; intros.
 apply Rlt_trans with (1 + 0)%R.
  rewrite Rplus_comm in |- *.
    apply Rlt_n_Sn.
  apply Rplus_lt_compat_l.
    rewrite <- (Rmul_0_l Rset Rext RTheory 2%R) in |- *.
    rewrite Rmult_comm in |- *.
    apply Rmult_lt_compat_l.
   apply Rlt_trans with (0 + 1)%R.
    apply Rlt_n_Sn.
    rewrite Rplus_comm in |- *.
      apply Rplus_lt_compat_l.
       replace 1%R with (0 + 1)%R; auto with real.
   trivial.
 rewrite <- (Rmul_0_l Rset Rext RTheory 2%R) in |- *.
   rewrite Rmult_comm in |- *.
   apply Rmult_lt_compat_l.
  apply Rlt_trans with (0 + 1)%R.
   apply Rlt_n_Sn.
   rewrite Rplus_comm in |- *.
     apply Rplus_lt_compat_l.
      replace 1%R with (0 + 1)%R; auto with real.
  trivial.
 auto with real.
Qed.
(*
unfold Rgt in |- *.
induction x; simpl in |- *; intros.
 apply Rplus_lt_0_compat; auto with real.
   apply Rmult_lt_0_compat; auto with real.
 apply Rmult_lt_0_compat; auto with real.
 auto with real.
*)

Lemma Rgen_phiPOS_not_0 : forall x, (gen_phiPOS1 1 Rplus Rmult x <> 0)%R.
red in |- *; intros.
specialize (Rgen_phiPOS x).
rewrite H in |- *; intro.
apply (Rlt_asym 0 0); trivial.
Qed.



Let ARfield :=
  F2AF _ _ _ _ _ _ _ _ _ _ Rset Rext Rfield.

(*Let Rring := AF_AR _ _ _ _ _ _ _ _ _ _ ARfield.*)

Notation NPFcons_inv :=
  (PFcons_fcons_inv
    _ _ _ _ _ _ _ _ Rset Rext ARfield _ _ _ _ _ _ _ _ _ Rmorph).


(*
Theorem SRinv_ext: forall p q:R, p=q -> (/p = /q)%R.
intros p q; apply f_equal with ( f := Rinv ); auto.
Qed.

Add Morphism Rinv : Rinv_morph.
Proof.
exact SRinv_ext.
Qed.
*)
Notation Rphi := (gen_phiZ 0%R 1%R Rplus Rmult Ropp).

Theorem gen_phiPOS1_IZR :
 forall p, gen_phiPOS 1%R Rplus Rmult p = IZR (Zpos p).
intros p; elim p; simpl gen_phiPOS.
intros p0; case p0.
intros p1 H; rewrite H.
unfold IZR; rewrite (nat_of_P_xI (xI p1)); (try rewrite S_INR);
 (try rewrite plus_INR); (try rewrite mult_INR).
pose (x:= INR (nat_of_P (xI p1))); fold x; simpl; ring.
intros p1 H; rewrite H.
unfold IZR; rewrite (nat_of_P_xI (xO p1)); (try rewrite S_INR);
 (try rewrite plus_INR); (try rewrite mult_INR).
pose (x:= INR (nat_of_P (xO p1))); fold x; simpl; ring.
simpl; intros; ring.
intros p0; case p0.
intros p1 H; rewrite H.
unfold IZR; rewrite (nat_of_P_xO (xI p1)); (try rewrite S_INR);
 (try rewrite plus_INR); (try rewrite mult_INR).
pose (x:= INR (nat_of_P (xO p1))); fold x; simpl; ring.
intros p1 H; rewrite H.
unfold IZR; rewrite (nat_of_P_xO (xO p1)); (try rewrite S_INR);
 (try rewrite plus_INR); (try rewrite mult_INR).
pose (x:= INR (nat_of_P (xO p1))); fold x; simpl; ring.
simpl; intros; ring.
simpl; trivial.
Qed.
 
Theorem gen_phiZ1_IZR: forall p, Rphi p = IZR p.
intros p; case p; simpl; auto.
intros p0; rewrite gen_phiPOS1_IZR; auto.
intros p0; rewrite gen_phiPOS1_IZR; auto.
Qed.

Lemma Zeq_bool_complete : forall x y, Rphi x = Rphi y -> Zeq_bool x y = true.
Proof.
intros.
 replace y with x.
 unfold Zeq_bool in |- *.
   rewrite Zcompare_refl in |- *; trivial.
 assert (IZR x = IZR y); auto.
  repeat rewrite <- gen_phiZ1_IZR in |- *; trivial.
  apply eq_IZR; trivial.
Qed.


Section Complete.
Import Setoid.
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
     Ltac rrefl := gen_reflexivity Rsth.
 Variable Reqe : ring_eq_ext radd rmul ropp req.
   Add Morphism radd : radd_ext3.  exact (Radd_ext Reqe). Qed.
   Add Morphism rmul : rmul_ext3.  exact (Rmul_ext Reqe). Qed.
   Add Morphism ropp : ropp_ext3.  exact (Ropp_ext Reqe). Qed.

Section AlmostField.

 Variable AFth : almost_field_theory R rO rI radd rmul rsub ropp rdiv rinv req.
 Let ARth := AFth.(AF_AR _ _ _ _ _ _ _ _ _ _).
 Let rI_neq_rO := AFth.(AF_1_neq_0 _ _ _ _ _ _ _ _ _ _).
 Let rdiv_def := AFth.(AFdiv_def _ _ _ _ _ _ _ _ _ _).
 Let rinv_l := AFth.(AFinv_l _ _ _ _ _ _ _ _ _ _).

Hypothesis S_inj : forall x y, 1+x==1+y -> x==y.

Hypothesis gen_phiPOS_not_0 : forall p, ~ gen_phiPOS1 rI radd rmul p == 0.

Lemma discr_0_2 : ~ 1+1 == 0.
change (~ gen_phiPOS 1 radd rmul 2 == 0) in |- *.
rewrite <- (same_gen Rsth Reqe ARth) in |- *.
apply gen_phiPOS_not_0.
Qed.
Hint Resolve discr_0_2.


Lemma double_inj : forall x y, (1+1)*x==(1+1)*y -> x==y.
intros.
assert (/ (1 + 1) * ((1 + 1) * x) == / (1 + 1) * ((1 + 1) * y)).
 rewrite H in |- *; trivial.
   reflexivity.
 generalize H0; clear H0.
   repeat rewrite (ARmul_assoc ARth) in |- *.
   repeat rewrite (AFinv_l _ _ _ _ _ _ _ _ _ _ AFth) in |- *; trivial.
   repeat rewrite (ARmul_1_l ARth) in |- *; trivial.
Qed.

Lemma discr_even_1 : forall x,
  ~ (1+1) * gen_phiPOS1 rI radd rmul x == 1.
intros.
rewrite (same_gen Rsth Reqe ARth) in |- *.
elim x using Pcase; simpl in |- *; intros.
 rewrite (ARmul_1_r Rsth ARth) in |- *.
   red in |- *; intro.
   apply rI_neq_rO.
   apply S_inj.
   rewrite H in |- *.
   rewrite (ARadd_0_r Rsth ARth) in |- *; reflexivity.
 rewrite <- (same_gen Rsth Reqe ARth) in |- *.
   rewrite (ARgen_phiPOS_Psucc Rsth Reqe ARth) in |- *.
   rewrite (ARdistr_r Rsth Reqe ARth) in |- *.
   rewrite (ARmul_1_r Rsth ARth) in |- *.
   red in |- *; intro.
   apply (gen_phiPOS_not_0 (xI n)).
   apply S_inj; simpl in |- *.
   rewrite (ARadd_assoc ARth) in |- *.
   rewrite H in |- *.
   rewrite (ARadd_0_r Rsth ARth) in |- *; reflexivity.
Qed.

Lemma discr_odd_0 : forall x,
  ~ 1 + (1+1) * gen_phiPOS1 rI radd rmul x == 0.
red in |- *; intros.
apply discr_even_1 with (Psucc x).
rewrite (ARgen_phiPOS_Psucc Rsth Reqe ARth) in |- *.
rewrite (ARdistr_r Rsth Reqe ARth) in |- *.
rewrite (ARmul_1_r Rsth ARth) in |- *.
rewrite <- (ARadd_assoc ARth) in |- *.
rewrite H in |- *.
apply (ARadd_0_r Rsth ARth).
Qed.


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

Lemma discr_0_1: ~ 1 == 0.
red in |- *; intro.
apply (discr_even_1 1).
simpl in |- *.
rewrite H in |- *.
apply (ARmul_0_r Rsth ARth).
Qed.


Lemma discr_diag : forall x,
  ~ 1 + gen_phiPOS1 rI radd rmul x == gen_phiPOS1 rI radd rmul x.
intro.
elim x using Pind; simpl in |- *; intros.
 red in |- *; intro; apply discr_0_1.
   apply S_inj.
   rewrite (ARadd_0_r Rsth ARth) in |- *.
   trivial.
 rewrite (ARgen_phiPOS_Psucc Rsth Reqe ARth) in |- *.
   red in |- *; intro; apply H.
   apply S_inj; trivial.
Qed.

Lemma even_odd_discr : forall x y,
  ~ 1 + (1+1) * gen_phiPOS1 rI radd rmul x == 
   (1+1) * gen_phiPOS1 rI radd rmul y.
intros.
ElimPcompare x y; intro.
  replace y with x.
  apply (discr_diag (xO x)).
  apply Pcompare_Eq_eq; trivial.
  replace y with (x + (y - x))%positive.
  rewrite (ARgen_phiPOS_add Rsth Reqe ARth) in |- *.
    rewrite (ARadd_sym ARth) in |- *.
    rewrite (ARdistr_r Rsth Reqe ARth) in |- *.
    red in |- *; intros.
    apply discr_even_1 with (y - x)%positive.
    symmetry  in |- *.
    apply add_inj_r with (xO x); trivial.
  apply Pplus_minus.
    change Eq with (CompOpp Eq) in |- *.
    rewrite <- Pcompare_antisym in |- *; trivial.
    simpl in |- *.
    rewrite H in |- *; trivial.
  replace x with (y + (x - y))%positive.
  rewrite (ARgen_phiPOS_add Rsth Reqe ARth) in |- *.
    rewrite (ARdistr_r Rsth Reqe ARth) in |- *.
    rewrite (ARadd_assoc ARth) in |- *.
    red in |- *; intro.
    apply discr_odd_0 with (x - y)%positive.
    apply add_inj_r with (xO y).
    simpl in |- *.
    rewrite (ARadd_0_r Rsth ARth) in |- *.
    rewrite (ARadd_assoc ARth) in |- *.
    rewrite (ARadd_sym ARth ((1 + 1) * gen_phiPOS1 1 radd rmul y)) in |- *.
    trivial.
  apply Pplus_minus; trivial.
Qed.

(* unused fact *)
Lemma even_0_inv : forall x, (1+1) * x == 0 -> x == 0.
Proof.
intros.
apply double_inj.
rewrite (ARmul_0_r Rsth ARth) in |- *.
trivial.
Qed.

Lemma gen_phiPOS_inj : forall x y,
  gen_phiPOS rI radd rmul x == gen_phiPOS rI radd rmul y ->
  x = y.
intros x y.
repeat rewrite <- (same_gen Rsth Reqe ARth) in |- *.
generalize y; clear y.
induction x; destruct y; simpl in |- *; intros.
  replace y with x; trivial.
   apply IHx.
   apply double_inj; apply S_inj; trivial.
 elim even_odd_discr with (1 := H).
 elim gen_phiPOS_not_0 with (xO x).
   apply S_inj.
   rewrite (ARadd_0_r Rsth ARth) in |- *.
   trivial.
 elim even_odd_discr with y x.
   symmetry  in |- *.
   trivial.
  replace y with x; trivial.
   apply IHx.
   apply double_inj; trivial.
 elim discr_even_1 with x.
   trivial.
 elim gen_phiPOS_not_0 with (xO y).
   apply S_inj.
   rewrite (ARadd_0_r Rsth ARth) in |- *.
   symmetry  in |- *; trivial.
 elim discr_even_1 with y.
   symmetry  in |- *; trivial.
 trivial.
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

End AlmostField.

Section Field.

 Variable Fth : field_theory R rO rI radd rmul rsub ropp rdiv rinv req.
 Let Rth := Fth.(F_R _ _ _ _ _ _ _ _ _ _).
 Let rI_neq_rO := Fth.(F_1_neq_0 _ _ _ _ _ _ _ _ _ _).
 Let rdiv_def := Fth.(Fdiv_def _ _ _ _ _ _ _ _ _ _).
 Let rinv_l := Fth.(Finv_l _ _ _ _ _ _ _ _ _ _).
 Let AFth := F2AF _ _ _ _ _ _ _ _ _ _ Rsth Reqe Fth.
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
   rewrite <- (Ropp_opp Rsth Reqe Rth (gen_phiPOS1 1 radd rmul p)) in |- *.
   rewrite (same_gen Rsth Reqe ARth) in |- *.
   rewrite <- H in |- *.
   apply (ARopp_zero Rsth Reqe ARth).
 elim gen_phiPOS_not_0 with p.
   rewrite (same_gen Rsth Reqe ARth) in |- *.
   trivial.
 rewrite gen_phiPOS_inject  with (1 := H) in |- *; trivial.
 elim gen_phiPOS_discr_sgn with (1 := H).
 elim gen_phiPOS_not_0 with p.
   rewrite <- (Ropp_opp Rsth Reqe Rth (gen_phiPOS1 1 radd rmul p)) in |- *.
   rewrite (same_gen Rsth Reqe ARth) in |- *.
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





(*
Definition Rlemma1 :=
  (Pphi_dev_div_ok_compl _ _ _ _ _ _ _ _ _ _ Rset Rext SRinv_ext ARfield
    _ _ _ _ _ _ _ _ _ Rmorph Zeq_bool_complete).

Definition Rlemma2 :=
  (Fnorm_correct_gen _ _ _ _ _ _ _ _ _ _ Rset Rext SRinv_ext ARfield
    _ _ _ _ _ _ _ _ _ Rmorph).

Definition Rlemma2' :=
  (Fnorm_correct_compl _ _ _ _ _ _ _ _ _ _ Rset Rext SRinv_ext ARfield
    _ _ _ _ _ _ _ _ _ Rmorph Zeq_bool_complete).

Definition Rlemma3 :=
  (Field_simplify_eq_correct_compl
    _ _ _ _ _ _ _ _ _ _ Rset Rext SRinv_ext ARfield
    _ _ _ _ _ _ _ _ _ Rmorph Zeq_bool_complete).

Notation Fcons := (Fcons2 Z 0%Z Zplus Zmult Zminus Zopp Zeq_bool).
*)

End RField.
(*
Ltac newfield :=
  Make_field_tac
    Rlemma2' (eq (A:=R)) ltac:(inv_gen_phiZ 0%R 1%R Rplus Rmult Ropp).

Section Compat.
Open Scope R_scope.

(** Inverse *)
Lemma Rinv_1 : / 1 = 1.
newfield; auto with real.
Qed.

(*********)
Lemma Rinv_involutive : forall r, r <> 0 -> / / r = r.
intros; newfield; auto with real.
Qed.

(*********)
Lemma Rinv_mult_distr :
 forall r1 r2, r1 <> 0 -> r2 <> 0 -> / (r1 * r2) = / r1 * / r2.
intros; newfield; auto with real.
Qed.

(*********)
Lemma Ropp_inv_permute : forall r, r <> 0 -> - / r = / - r.
intros; newfield; auto with real.
Qed.
End Compat.

Ltac field := newfield.
Ltac field_simplify_eq :=
   Make_field_simplify_eq_tac
     Rlemma3 (eq (A:=R)) ltac:(inv_gen_phiZ 0%R 1%R Rplus Rmult Ropp).
Ltac field_simplify :=
   Field_rewrite_list
     Rlemma1 (eq (A:=R)) ltac:(inv_gen_phiZ 0%R 1%R Rplus Rmult Ropp).
*)
(*
Ltac newfield_rewrite r :=
  let T := Rfield.Make_field_rewrite in
  T Rplus Rmult Rminus Ropp Rinv Rdiv Fcons2 PFcons2_fcons_inv RCst r;
  unfold_field.
*)

