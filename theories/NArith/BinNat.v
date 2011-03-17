(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinPos.

(**********************************************************************)
(** Binary natural numbers *)

Inductive N : Set :=
  | N0 : N
  | Npos : positive -> N.

(** Declare binding key for scope positive_scope *)

Delimit Scope N_scope with N.

(** Automatically open scope positive_scope for the constructors of N *)

Bind Scope N_scope with N.
Arguments Scope Npos [positive_scope].

Local Open Scope N_scope.

(** Some local ad-hoc notation, since no interpretation of numerical
  constants is available yet. *)

Local Notation "0" := N0 : N_scope.
Local Notation "1" := (Npos 1) : N_scope.
Local Notation "2" := (Npos 2) : N_scope.

Definition Ndiscr : forall n:N, { p:positive | n = Npos p } + { n = N0 }.
Proof.
 destruct n; auto.
 left; exists p; auto.
Defined.

(** Operation x -> 2*x+1 *)

Definition Ndouble_plus_one x :=
  match x with
  | 0 => Npos 1
  | Npos p => Npos p~1
  end.

(** Operation x -> 2*x *)

Definition Ndouble n :=
  match n with
  | 0 => 0
  | Npos p => Npos p~0
  end.

(** Successor *)

Definition Nsucc n :=
  match n with
  | 0 => Npos 1
  | Npos p => Npos (Psucc p)
  end.

(** Predecessor *)

Definition Npred (n : N) := match n with
| 0 => 0
| Npos p => match p with
  | xH => 0
  | _ => Npos (Ppred p)
  end
end.

(** The successor of a N can be seen as a positive *)

Definition Nsucc_pos (n : N) : positive :=
 match n with
   | N0 => 1%positive
   | Npos p => Psucc p
 end.

(** Similarly, the predecessor of a positive, seen as a N *)

Definition Ppred_N (p:positive) : N :=
 match p with
   | 1 => N0
   | p~1 => Npos (p~0)
   | p~0 => Npos (Pdouble_minus_one p)
 end%positive.

(** Addition *)

Definition Nplus n m :=
  match n, m with
  | 0, _ => m
  | _, 0 => n
  | Npos p, Npos q => Npos (p + q)
  end.

Infix "+" := Nplus : N_scope.

(** Subtraction *)

Definition Nminus (n m : N) :=
match n, m with
| 0, _ => 0
| n, 0 => n
| Npos n', Npos m' =>
  match Pminus_mask n' m' with
  | IsPos p => Npos p
  | _ => 0
  end
end.

Infix "-" := Nminus : N_scope.

(** Multiplication *)

Definition Nmult n m :=
  match n, m with
  | 0, _ => 0
  | _, 0 => 0
  | Npos p, Npos q => Npos (p * q)
  end.

Infix "*" := Nmult : N_scope.

(** Boolean Equality *)

Definition Neqb n m :=
 match n, m with
  | 0, 0 => true
  | Npos n, Npos m => Peqb n m
  | _,_ => false
 end.

(** Order *)

Definition Ncompare n m :=
  match n, m with
  | 0, 0 => Eq
  | 0, Npos m' => Lt
  | Npos n', 0 => Gt
  | Npos n', Npos m' => (n' ?= m')%positive Eq
  end.

Infix "?=" := Ncompare (at level 70, no associativity) : N_scope.

Definition Nlt (x y:N) := (x ?= y) = Lt.
Definition Ngt (x y:N) := (x ?= y) = Gt.
Definition Nle (x y:N) := (x ?= y) <> Gt.
Definition Nge (x y:N) := (x ?= y) <> Lt.

Infix "<=" := Nle : N_scope.
Infix "<" := Nlt : N_scope.
Infix ">=" := Nge : N_scope.
Infix ">" := Ngt : N_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : N_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : N_scope.
Notation "x < y < z" := (x < y /\ y < z) : N_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : N_scope.

(** Min and max *)

Definition Nmin (n n' : N) := match Ncompare n n' with
 | Lt | Eq => n
 | Gt => n'
 end.

Definition Nmax (n n' : N) := match Ncompare n n' with
 | Lt | Eq => n'
 | Gt => n
 end.

(** Translation from [N] to [nat] and back. *)

Definition nat_of_N (a:N) :=
  match a with
  | N0 => O
  | Npos p => nat_of_P p
  end.

Definition N_of_nat (n:nat) :=
  match n with
  | O => 0
  | S n' => Npos (P_of_succ_nat n')
  end.

(** Decidability of equality. *)

Definition N_eq_dec : forall n m : N, { n = m } + { n <> m }.
Proof.
 decide equality.
 apply positive_eq_dec.
Defined.

(** convenient induction principles *)

Lemma N_ind_double :
 forall (a:N) (P:N -> Prop),
   P 0 ->
   (forall a, P a -> P (Ndouble a)) ->
   (forall a, P a -> P (Ndouble_plus_one a)) -> P a.
Proof.
 intros a P P0 P2 PS2. destruct a as [|p]. trivial.
 induction p as [p IHp|p IHp| ].
 now apply (PS2 (Npos p)).
 now apply (P2 (Npos p)).
 now apply (PS2 0).
Qed.

Lemma N_rec_double :
 forall (a:N) (P:N -> Set),
   P 0 ->
   (forall a, P a -> P (Ndouble a)) ->
   (forall a, P a -> P (Ndouble_plus_one a)) -> P a.
Proof.
 intros a P P0 P2 PS2. destruct a as [|p]. trivial.
 induction p as [p IHp|p IHp| ].
 now apply (PS2 (Npos p)).
 now apply (P2 (Npos p)).
 now apply (PS2 0).
Qed.

(** Peano induction on binary natural numbers *)

Definition Nrect
  (P : N -> Type) (a : P 0)
    (f : forall n : N, P n -> P (Nsucc n)) (n : N) : P n :=
let f' (p : positive) (x : P (Npos p)) := f (Npos p) x in
let P' (p : positive) := P (Npos p) in
match n return (P n) with
| 0 => a
| Npos p => Prect P' (f 0 a) f' p
end.

Theorem Nrect_base : forall P a f, Nrect P a f 0 = a.
Proof.
intros P a f; simpl; reflexivity.
Qed.

Theorem Nrect_step : forall P a f n, Nrect P a f (Nsucc n) = f n (Nrect P a f n).
Proof.
intros P a f; destruct n as [| p]; simpl;
[rewrite Prect_base | rewrite Prect_succ]; reflexivity.
Qed.

Definition Nind (P : N -> Prop) := Nrect P.

Definition Nrec (P : N -> Set) := Nrect P.

Theorem Nrec_base : forall P a f, Nrec P a f 0 = a.
Proof.
intros P a f; unfold Nrec; apply Nrect_base.
Qed.

Theorem Nrec_step : forall P a f n, Nrec P a f (Nsucc n) = f n (Nrec P a f n).
Proof.
intros P a f; unfold Nrec; apply Nrect_step.
Qed.

(** Properties of successor and predecessor *)

Theorem Npred_succ : forall n : N, Npred (Nsucc n) = n.
Proof.
intros [| p]; simpl. reflexivity.
case_eq (Psucc p); try (intros q H; rewrite <- H; now rewrite Ppred_succ).
intro H; false_hyp H Psucc_not_one.
Qed.

Theorem Npred_minus : forall n, Npred n = Nminus n (Npos 1).
Proof.
 intros [|[p|p|]]; trivial.
Qed.

Lemma Nsucc_pred : forall n, n<>0 -> Nsucc (Npred n) = n.
Proof.
 intros [|n] H; (now destruct H) || clear H.
 rewrite Npred_minus. simpl. destruct n; simpl; trivial.
 f_equal; apply Psucc_o_double_minus_one_eq_xO.
Qed.

(** Properties of mixed successor and predecessor. *)

Lemma Ppred_N_spec : forall p, Ppred_N p = Npred (Npos p).
Proof.
 now destruct p.
Qed.

Lemma Nsucc_pos_spec : forall n, Npos (Nsucc_pos n) = Nsucc n.
Proof.
 now destruct n.
Qed.

Lemma Ppred_Nsucc : forall n, Ppred_N (Nsucc_pos n) = n.
Proof.
 intros. now rewrite Ppred_N_spec, Nsucc_pos_spec, Npred_succ.
Qed.

(** Properties of addition *)

Theorem Nplus_0_l : forall n:N, 0 + n = n.
Proof.
reflexivity.
Qed.

Theorem Nplus_0_r : forall n:N, n + 0 = n.
Proof.
destruct n; reflexivity.
Qed.

Theorem Nplus_comm : forall n m:N, n + m = m + n.
Proof.
intros.
destruct n; destruct m; simpl; try reflexivity.
rewrite Pplus_comm; reflexivity.
Qed.

Theorem Nplus_assoc : forall n m p:N, n + (m + p) = n + m + p.
Proof.
intros.
destruct n; try reflexivity.
destruct m; try reflexivity.
destruct p; try reflexivity.
simpl; rewrite Pplus_assoc; reflexivity.
Qed.

Theorem Nplus_succ : forall n m:N, Nsucc n + m = Nsucc (n + m).
Proof.
destruct n, m.
  simpl; reflexivity.
  unfold Nsucc, Nplus; rewrite <- Pplus_one_succ_l; reflexivity.
  simpl; reflexivity.
  simpl; rewrite Pplus_succ_permute_l; reflexivity.
Qed.

Theorem Nsucc_0 : forall n : N, Nsucc n <> 0.
Proof.
now destruct n.
Qed.

Theorem Nsucc_inj : forall n m:N, Nsucc n = Nsucc m -> n = m.
Proof.
intros [|p] [|q] H; simpl in *; trivial; injection H; clear H; intro H.
  now elim (Psucc_not_one q).
  now elim (Psucc_not_one p).
  apply Psucc_inj in H. now f_equal.
Qed.

Theorem Nplus_reg_l : forall n m p:N, n + m = n + p -> m = p.
Proof.
 induction n using Nind.
  trivial.
  intros m p H; rewrite 2 Nplus_succ in H.
  apply Nsucc_inj in H. now apply IHn.
Qed.

(** Properties of subtraction. *)

Lemma Nminus_N0_Nle : forall n n' : N, n - n' = 0 <-> n <= n'.
Proof.
intros [| p] [| q]; unfold Nle; simpl;
split; intro H; try easy.
now elim H.
contradict H. now destruct (Pminus_mask_Gt _ _ H) as (h & -> & _).
destruct (Pcompare_spec p q); try now elim H.
subst. now rewrite Pminus_mask_diag.
now rewrite Pminus_mask_Lt.
Qed.

Theorem Nminus_0_r : forall n : N, n - 0 = n.
Proof.
now destruct n.
Qed.

Theorem Nminus_succ_r : forall n m : N, n - (Nsucc m) = Npred (n - m).
Proof.
intros [|p] [|q]; trivial.
now destruct p.
simpl. rewrite Pminus_mask_succ_r, Pminus_mask_carry_spec.
now destruct (Pminus_mask p q) as [|[r|r|]|].
Qed.

(** Properties of multiplication *)

Theorem Nmult_0_l : forall n:N, 0 * n = 0.
Proof.
reflexivity.
Qed.

Theorem Nmult_1_l : forall n:N, Npos 1 * n = n.
Proof.
destruct n; reflexivity.
Qed.

Theorem Nmult_Sn_m : forall n m : N, (Nsucc n) * m = m + n * m.
Proof.
intros [|n] [|m]; simpl; trivial. now rewrite Pmult_Sn_m.
Qed.

Theorem Nmult_1_r : forall n:N, n * Npos 1%positive = n.
Proof.
intros [|n]; simpl; trivial. now rewrite Pmult_1_r.
Qed.

Theorem Nmult_comm : forall n m:N, n * m = m * n.
Proof.
intros [|n] [|m]; simpl; trivial. now rewrite Pmult_comm.
Qed.

Theorem Nmult_assoc : forall n m p:N, n * (m * p) = n * m * p.
Proof.
intros.
destruct n; try reflexivity.
destruct m; try reflexivity.
destruct p; try reflexivity.
simpl; rewrite Pmult_assoc; reflexivity.
Qed.

Theorem Nmult_plus_distr_r : forall n m p:N, (n + m) * p = n * p + m * p.
Proof.
intros.
destruct n; try reflexivity.
destruct m; destruct p; try reflexivity.
simpl; rewrite Pmult_plus_distr_r; reflexivity.
Qed.

Theorem Nmult_plus_distr_l : forall n m p:N, p * (n + m) = p * n + p * m.
Proof.
intros. rewrite ! (Nmult_comm p); apply Nmult_plus_distr_r.
Qed.

Theorem Nmult_reg_r : forall n m p:N, p <> 0 -> n * p = m * p -> n = m.
Proof.
destruct p; intros Hp H.
contradiction Hp; reflexivity.
destruct n; destruct m; reflexivity || (try discriminate H).
injection H; clear H; intro H; rewrite Pmult_reg_r with (1 := H); reflexivity.
Qed.

(** Properties of boolean order. *)

Lemma Neqb_eq : forall n m, Neqb n m = true <-> n=m.
Proof.
destruct n as [|n], m as [|m]; simpl; split; auto; try discriminate.
intros; f_equal. apply (Peqb_eq n m); auto.
intros. apply (Peqb_eq n m). congruence.
Qed.

(** Properties of comparison *)

Lemma Nle_0 : forall n, 0<=n.
Proof.
 now destruct n.
Qed.

Lemma Ncompare_refl : forall n, (n ?= n) = Eq.
Proof.
destruct n; simpl; auto.
apply Pcompare_refl.
Qed.

Theorem Ncompare_Eq_eq : forall n m:N, (n ?= m) = Eq -> n = m.
Proof.
destruct n as [| n]; destruct m as [| m]; simpl; intro H;
 reflexivity || (try discriminate H).
  rewrite (Pcompare_Eq_eq n m H); reflexivity.
Qed.

Theorem Ncompare_eq_correct : forall n m:N, (n ?= m) = Eq <-> n = m.
Proof.
split; intros;
 [ apply Ncompare_Eq_eq; auto | subst; apply Ncompare_refl ].
Qed.

Lemma Ncompare_antisym : forall n m, CompOpp (n ?= m) = (m ?= n).
Proof.
destruct n; destruct m; simpl; auto.
exact (Pcompare_antisym p p0 Eq).
Qed.

Lemma Ngt_Nlt : forall n m, n > m -> m < n.
Proof.
unfold Ngt, Nlt; intros n m GT.
rewrite <- Ncompare_antisym, GT; reflexivity.
Qed.

Theorem Nlt_irrefl : forall n : N, ~ n < n.
Proof.
intro n; unfold Nlt; now rewrite Ncompare_refl.
Qed.

Theorem Nlt_trans : forall n m q, n < m -> m < q -> n < q.
Proof.
destruct n;
 destruct m; try discriminate;
 destruct q; try discriminate; auto.
eapply Plt_trans; eauto.
Qed.

Theorem Nlt_not_eq : forall n m, n < m -> ~ n = m.
Proof.
 intros n m LT EQ. subst m. elim (Nlt_irrefl n); auto.
Qed.

Theorem Ncompare_n_Sm :
  forall n m : N, (n ?= Nsucc m) = Lt <-> (n ?= m) = Lt \/ n = m.
Proof.
intros [|p] [|q]; simpl; split; intros H; auto.
destruct p; discriminate.
destruct H; discriminate.
apply Pcompare_p_Sq in H; destruct H; subst; auto.
apply Pcompare_p_Sq; destruct H; [left|right]; congruence.
Qed.

Lemma Nle_lteq : forall x y, x <= y <-> x < y \/ x=y.
Proof.
unfold Nle, Nlt; intros.
generalize (Ncompare_eq_correct x y).
destruct (x ?= y); intuition; discriminate.
Qed.

Lemma Nlt_succ_r : forall n m,  n < Nsucc m <-> n<=m.
Proof.
intros n m.
eapply iff_trans. apply Ncompare_n_Sm. apply iff_sym, Nle_lteq.
Qed.

Lemma Nle_trans : forall n m p, n<=m -> m<=p -> n<=p.
Proof.
 intros n m p H H'.
 apply Nle_lteq. apply Nle_lteq in H. apply Nle_lteq in H'.
 destruct H, H'; subst; auto.
 left; now apply Nlt_trans with m.
Qed.

Lemma Nle_succ_l : forall n m, Nsucc n <= m <-> n < m.
Proof.
 intros.
 unfold Nle, Nlt.
 rewrite <- 2 (Ncompare_antisym m).
 generalize (Nlt_succ_r m n). unfold Nle,Nlt.
 destruct Ncompare, Ncompare; simpl; intros (U,V);
  intuition; now try discriminate V.
Qed.

Lemma Ncompare_spec : forall x y, CompareSpec (x=y) (x<y) (y<x) (x ?= y).
Proof.
intros.
destruct (Ncompare x y) as [ ]_eqn; constructor; auto.
apply Ncompare_Eq_eq; auto.
apply Ngt_Nlt; auto.
Qed.

(** Order and operations *)

(** NB : Many more results will come from NBinary, the Number instantiation.
    The next lemmas are useful for proving the correctness of
    advanced functions.
*)

Lemma Nplus_lt_cancel_l : forall n m p, p+n < p+m -> n<m.
Proof.
 intros. destruct p. simpl; auto.
 destruct n; destruct m.
 elim (Nlt_irrefl _ H).
 red; auto.
 rewrite Nplus_0_r in H. simpl in H.
 red in H. simpl in H.
 elim (Plt_not_plus_l _ _ H).
 now apply (Pplus_lt_mono_l p).
Qed.

(** 0 is the least natural number *)

Theorem Ncompare_0 : forall n : N, Ncompare n 0 <> Lt.
Proof.
destruct n; discriminate.
Qed.

(** Dividing by 2 *)

Definition Ndiv2 (n:N) :=
  match n with
  | 0 => 0
  | Npos 1 => 0
  | Npos (p~0) => Npos p
  | Npos (p~1) => Npos p
  end.

Lemma Ndouble_div2 : forall n:N, Ndiv2 (Ndouble n) = n.
Proof.
  destruct n; trivial.
Qed.

Lemma Ndouble_plus_one_div2 :
 forall n:N, Ndiv2 (Ndouble_plus_one n) = n.
Proof.
  destruct n; trivial.
Qed.

Lemma Ndouble_inj : forall n m, Ndouble n = Ndouble m -> n = m.
Proof.
  intros. rewrite <- (Ndouble_div2 n). rewrite H. apply Ndouble_div2.
Qed.

Lemma Ndouble_plus_one_inj :
 forall n m, Ndouble_plus_one n = Ndouble_plus_one m -> n = m.
Proof.
  intros. rewrite <- (Ndouble_plus_one_div2 n). rewrite H. apply Ndouble_plus_one_div2.
Qed.

(** Power *)

Definition Npow n p :=
  match p, n with
    | 0, _ => Npos 1
    | _, 0 => 0
    | Npos p, Npos q => Npos (Ppow q p)
  end.

Infix "^" := Npow : N_scope.

Lemma Npow_0_r : forall n, n ^ 0 = Npos 1.
Proof. reflexivity. Qed.

Lemma Npow_succ_r : forall n p, n^(Nsucc p) = n * n^p.
Proof.
 intros [|q] [|p]; simpl; trivial; f_equal.
 apply Ppow_succ_r.
Qed.

(** Base-2 logarithm *)

Definition Nlog2 n :=
 match n with
   | 0 => 0
   | Npos 1 => 0
   | Npos (p~0) => Npos (Psize_pos p)
   | Npos (p~1) => Npos (Psize_pos p)
 end.

Lemma Nlog2_spec : forall n, 0 < n ->
 (Npos 2)^(Nlog2 n) <= n < (Npos 2)^(Nsucc (Nlog2 n)).
Proof.
 intros [|[p|p|]] H; discriminate H || clear H; simpl; split.
 eapply Nle_trans with (Npos (p~0)).
 apply Psize_pos_le.
 apply Nle_lteq; left. exact (Pcompare_p_Sp (p~0)).
 apply Psize_pos_gt.
 apply Psize_pos_le.
 apply Psize_pos_gt.
 discriminate.
 reflexivity.
Qed.

Lemma Nlog2_nonpos : forall n, n<=0 -> Nlog2 n = 0.
Proof.
 intros [|n] Hn. reflexivity. now destruct Hn.
Qed.

(** Parity *)

Definition Neven n :=
  match n with
    | 0 => true
    | Npos (xO _) => true
    | _ => false
  end.
Definition Nodd n := negb (Neven n).

Lemma Neven_spec : forall n, Neven n = true <-> exists m, n=2*m.
Proof.
 destruct n.
 split. now exists 0.
 trivial.
 destruct p; simpl; split; trivial; try discriminate.
 intros (m,H). now destruct m.
 now exists (Npos p).
 intros (m,H). now destruct m.
Qed.

Lemma Nodd_spec : forall n, Nodd n = true <-> exists m, n=2*m+1.
Proof.
 destruct n.
 split. discriminate.
 intros (m,H). now destruct m.
 destruct p; simpl; split; trivial; try discriminate.
 exists (Npos p). reflexivity.
 intros (m,H). now destruct m.
 exists 0. reflexivity.
Qed.
