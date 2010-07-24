(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)


Require Import BinPos BinNat Nnat ZArith_base.

Open Scope Z_scope.

Definition NPgeb (a:N)(b:positive) :=
  match a with
   | N0 => false
   | Npos na => match Pcompare na b Eq with Lt => false | _ => true end
  end.

Fixpoint Pdiv_eucl (a b:positive) : N * N :=
  match a with
    | xH =>
       match b with xH => (1, 0)%N | _ => (0, 1)%N end
    | xO a' =>
       let (q, r) := Pdiv_eucl a' b in
       let r' := (2 * r)%N in
        if (NPgeb r' b) then (2 * q + 1, (Nminus r'  (Npos b)))%N
        else  (2 * q, r')%N
    | xI a' =>
       let (q, r) := Pdiv_eucl a' b in
       let r' := (2 * r + 1)%N in
        if (NPgeb r' b) then (2 * q + 1, (Nminus r' (Npos b)))%N
        else  (2 * q, r')%N
  end.

Definition ZOdiv_eucl (a b:Z) : Z * Z :=
  match a, b with
   | Z0,  _ => (Z0, Z0)
   | _, Z0  => (Z0, a)
   | Zpos na, Zpos nb =>
         let (nq, nr) := Pdiv_eucl na nb in
         (Z_of_N nq, Z_of_N nr)
   | Zneg na, Zpos nb =>
         let (nq, nr) := Pdiv_eucl na nb in
         (Zopp (Z_of_N nq), Zopp (Z_of_N nr))
   | Zpos na, Zneg nb =>
         let (nq, nr) := Pdiv_eucl na nb in
         (Zopp (Z_of_N nq), Z_of_N nr)
   | Zneg na, Zneg nb =>
         let (nq, nr) := Pdiv_eucl na nb in
         (Z_of_N nq, Zopp (Z_of_N nr))
  end.

Definition ZOdiv a b := fst (ZOdiv_eucl a b).
Definition ZOmod a b := snd (ZOdiv_eucl a b).


Definition Ndiv_eucl (a b:N) : N * N :=
  match a, b with
   | N0,  _ => (N0, N0)
   | _, N0  => (N0, a)
   | Npos na, Npos nb => Pdiv_eucl na nb
  end.

Definition Ndiv a b := fst (Ndiv_eucl a b).
Definition Nmod a b := snd (Ndiv_eucl a b).


(* Proofs of specifications for these euclidean divisions. *)

Theorem NPgeb_correct: forall (a:N)(b:positive),
  if NPgeb a b then a = (Nminus a (Npos b) + Npos b)%N else True.
Proof.
  destruct a; intros; simpl; auto.
  generalize (Pcompare_Eq_eq p b).
  case_eq (Pcompare p b Eq); intros; auto.
  rewrite H0; auto.
  now rewrite Pminus_mask_diag.
  destruct (Pminus_mask_Gt p b H) as [d [H2 [H3 _]]].
  rewrite H2. rewrite <- H3.
  simpl; f_equal; apply Pplus_comm.
Qed.

Hint Rewrite Z_of_N_plus Z_of_N_mult Z_of_N_minus Zmult_1_l Zmult_assoc
 Zmult_plus_distr_l Zmult_plus_distr_r : zdiv.
Hint Rewrite <- Zplus_assoc : zdiv.

Theorem Pdiv_eucl_correct: forall a b,
  let (q,r) := Pdiv_eucl a b in
  Zpos a = Z_of_N q * Zpos b + Z_of_N r.
Proof.
  induction a; cbv beta iota delta [Pdiv_eucl]; fold Pdiv_eucl; cbv zeta.
  intros b; generalize (IHa b); case Pdiv_eucl.
    intros q1 r1 Hq1.
     generalize (NPgeb_correct (2 * r1 + 1) b); case NPgeb; intros H.
     set (u := Nminus (2 * r1 + 1) (Npos b)) in * |- *.
     assert (HH: Z_of_N u = (Z_of_N (2 * r1 + 1) - Zpos b)%Z).
        rewrite H; autorewrite with zdiv; simpl.
        rewrite Zplus_comm, Zminus_plus; trivial.
     rewrite HH; autorewrite with zdiv; simpl Z_of_N.
     rewrite Zpos_xI, Hq1.
     autorewrite with zdiv; f_equal; rewrite Zplus_minus; trivial.
     rewrite Zpos_xI, Hq1; autorewrite with zdiv; auto.
  intros b; generalize (IHa b); case Pdiv_eucl.
    intros q1 r1 Hq1.
     generalize (NPgeb_correct (2 * r1) b); case NPgeb; intros H.
     set (u := Nminus (2 * r1) (Npos b)) in * |- *.
     assert (HH: Z_of_N u = (Z_of_N (2 * r1) - Zpos b)%Z).
        rewrite H; autorewrite with zdiv; simpl.
        rewrite Zplus_comm, Zminus_plus; trivial.
     rewrite HH; autorewrite with zdiv; simpl Z_of_N.
     rewrite Zpos_xO, Hq1.
     autorewrite with zdiv; f_equal; rewrite Zplus_minus; trivial.
     rewrite Zpos_xO, Hq1; autorewrite with zdiv; auto.
  destruct b; auto.
Qed.

Theorem ZOdiv_eucl_correct: forall a b,
  let (q,r) := ZOdiv_eucl a b in a = q * b + r.
Proof.
  destruct a; destruct b; simpl; auto;
  generalize (Pdiv_eucl_correct p p0); case Pdiv_eucl; auto; intros;
  try change (Zneg p) with (Zopp (Zpos p)); rewrite H.
    destruct n; auto.
  repeat (rewrite Zopp_plus_distr || rewrite Zopp_mult_distr_l); trivial.
  repeat (rewrite Zopp_plus_distr || rewrite Zopp_mult_distr_r); trivial.
Qed.

Theorem Ndiv_eucl_correct: forall a b,
  let (q,r) := Ndiv_eucl a b in a = (q * b + r)%N.
Proof.
  destruct a; destruct b; simpl; auto;
  generalize (Pdiv_eucl_correct p p0); case Pdiv_eucl; auto; intros;
  destruct n; destruct n0; simpl; simpl in H; try discriminate;
  injection H; intros; subst; trivial.
Qed.
