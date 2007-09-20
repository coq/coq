(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)


Require Import BinPos.
Require Import BinNat.
Require Import ZArith_base.

Definition Ngeb a b :=
  match a with
   N0 => false
 | Npos na => match Pcompare na b Eq with Lt => false | _ => true end end.

Fixpoint pdiv_eucl (a b:positive) {struct a} : N * N :=
  match a with
    | xH => 
       match b with xH => (1, 0)%N | _ => (0, 1)%N end
    | xO a' =>
       let (q, r) := pdiv_eucl a' b in
       let r' := (2 * r)%N in
        if (Ngeb r' b) then(2 * q + 1, (Nminus r'  (Npos b)))%N
        else  (2 * q, r')%N
    | xI a' =>
       let (q, r) := pdiv_eucl a' b in
       let r' := (2 * r + 1)%N in
        if (Ngeb r' b) then(2 * q + 1, (Nminus r' (Npos b)))%N
        else  (2 * q, r')%N
  end.


Theorem Ngeb_correct: forall a b, 
  if Ngeb a b then a = ((Nminus a (Npos b)) + Npos b)%N else True.
destruct a; intros; simpl; auto.
  case_eq (Pcompare p b Eq); intros; auto.
  rewrite (Pcompare_Eq_eq _ _ H).
  assert (HH: forall p, Pminus p p = xH).
    intro p0; unfold Pminus; rewrite Pminus_mask_diag; auto.
  apply Pcompare_Eq_eq in H. now rewrite Pminus_mask_diag.
  pose proof (Pminus_mask_Gt p b H) as H1. destruct H1 as [d [H2 [H3 _]]].
  rewrite H2. rewrite <- H3. unfold Nplus. now rewrite Pplus_comm.
Qed.

Theorem Z_of_N_plus: 
  forall a b, Z_of_N (a + b) = (Z_of_N a + Z_of_N b)%Z.
destruct a; destruct b; simpl; auto.
Qed.

Theorem Z_of_N_mult: 
  forall a b, Z_of_N (a * b) = (Z_of_N a * Z_of_N b)%Z.
destruct a; destruct b; simpl; auto.
Qed.

Ltac z_of_n_tac := repeat (rewrite Z_of_N_plus || rewrite Z_of_N_mult).

Ltac ztac := repeat (rewrite Zmult_plus_distr_l || 
                     rewrite Zmult_plus_distr_r || 
                     rewrite <- Zplus_assoc ||
                     rewrite Zmult_assoc || rewrite Zmult_1_l ).


Theorem pdiv_eucl_correct: forall a b,
  let (q,r) := pdiv_eucl a b in Zpos a = (Z_of_N q * Zpos b + Z_of_N r)%Z.
induction a; cbv beta iota delta [pdiv_eucl]; fold pdiv_eucl; cbv zeta.
  intros b; generalize (IHa b); case pdiv_eucl.
    intros q1 r1 Hq1.
     generalize (Ngeb_correct (2 * r1 + 1) b); case Ngeb; intros H.
     set (u := Nminus (2 * r1 + 1) (Npos b)) in * |- *.
     assert (HH: Z_of_N u = (Z_of_N (2 * r1 + 1) - Zpos b)%Z).
        rewrite H; z_of_n_tac; simpl.
        rewrite Zplus_comm; rewrite Zminus_plus; trivial.
     rewrite HH; z_of_n_tac; simpl Z_of_N.
     rewrite Zpos_xI; rewrite Hq1.
     ztac; apply f_equal2 with (f := Zplus); auto.
     rewrite Zplus_minus; trivial.
     rewrite Zpos_xI; rewrite Hq1; z_of_n_tac; ztac; auto.
  intros b; generalize (IHa b); case pdiv_eucl.
    intros q1 r1 Hq1.
     generalize (Ngeb_correct (2 * r1) b); case Ngeb; intros H.
     set (u := Nminus (2 * r1) (Npos b)) in * |- *.
     assert (HH: Z_of_N u = (Z_of_N (2 * r1) - Zpos b)%Z).
        rewrite H; z_of_n_tac; simpl.
        rewrite Zplus_comm; rewrite Zminus_plus; trivial.
     rewrite HH; z_of_n_tac; simpl Z_of_N.
     rewrite Zpos_xO; rewrite Hq1.
     ztac; apply f_equal2 with (f := Zplus); auto.
     rewrite Zplus_minus; trivial.
     rewrite Zpos_xO; rewrite Hq1; z_of_n_tac; ztac; auto.
  destruct b; auto.
Qed.

Definition zdiv_eucl (a b:Z) := 
  match a, b with
    Z0,  _ => (Z0, Z0)
  | _, Z0  => (Z0, a)
  | Zpos na, Zpos nb => 
         let (nq, nr) := pdiv_eucl na nb in (Z_of_N nq, Z_of_N nr)
  | Zneg na, Zpos nb => 
         let (nq, nr) := pdiv_eucl na nb in (Zopp (Z_of_N nq), Zopp (Z_of_N nr))
  | Zpos na, Zneg nb => 
         let (nq, nr) := pdiv_eucl na nb in (Zopp(Z_of_N nq), Z_of_N nr)
  | Zneg na, Zneg nb => 
         let (nq, nr) := pdiv_eucl na nb in (Z_of_N nq, Zopp (Z_of_N nr))
  end.


Theorem zdiv_eucl_correct: forall a b,
  let (q,r) := zdiv_eucl a b in a = (q * b + r)%Z.
destruct a; destruct b; simpl; auto;
  generalize (pdiv_eucl_correct p p0); case pdiv_eucl; auto; intros;
  try change (Zneg p) with (Zopp (Zpos p)); rewrite H.
    destruct n; auto.
  repeat (rewrite Zopp_plus_distr || rewrite Zopp_mult_distr_l); trivial.
  repeat (rewrite Zopp_plus_distr || rewrite Zopp_mult_distr_r); trivial.
Qed.

Definition ndiv_eucl (a b:N) := 
  match a, b with
    N0,  _ => (N0, N0)
  | _, N0  => (N0, a)
  | Npos na, Npos nb => 
         let (nq, nr) := pdiv_eucl na nb in (nq, nr)
  end.


Theorem ndiv_eucl_correct: forall a b,
  let (q,r) := ndiv_eucl a b in a = (q * b + r)%N.
destruct a; destruct b; simpl; auto;
  generalize (pdiv_eucl_correct p p0); case pdiv_eucl; auto; intros;
  destruct n; destruct n0; simpl; simpl in H; try
    discriminate;
  injection H; intros; subst; trivial.
Qed.


