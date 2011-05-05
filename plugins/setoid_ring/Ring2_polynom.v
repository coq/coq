(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*  A <X1,...,Xn>: non commutative polynomials on a commutative ring A *)

Set Implicit Arguments.
Require Import Setoid.
Require Import BinList.
Require Import BinPos.
Require Import BinNat.
Require Import BinInt.
Require Export Ring2.

Section MakeRingPol.

Variable C:Type.
Variable Cr:Ring C.
Variable R:Type.
Variable Rr:Ring R.

Variable phi:@Ring_morphism C R Cr Rr.

Existing Instance Rr.
Existing Instance Cr.
Existing Instance phi.
(* marche pas avec x * [c] == [c] * x
ou avec 
Variable c:C.
Variable x:C.
Check [c]*x.
 *)
 Variable phiCR_comm: forall (c:C)(x:R), x * [c] == ring_mult [c] x.

 Ltac rsimpl := repeat (gen_ring_rewrite || ring_rewrite phiCR_comm).
 Ltac add_push := gen_add_push .

(* Definition of non commutative multivariable polynomials 
   with coefficients in C :
 *)

 Inductive Pol : Type :=
  | Pc : C -> Pol
  | PX : Pol -> positive -> positive -> Pol -> Pol. 
    (* PX P i n Q represents P * X_i^n + Q *)
Definition cO := @ring0 _ Cr.
Definition cI := @ring1 _ Cr.

 Definition P0 := Pc cO.
 Definition P1 := Pc cI.

Variable Ceqb:C->C->bool.
Class Equalityb (A : Type):= {equalityb : A -> A -> bool}.
Notation "x =? y" := (equalityb x y) (at level 70, no associativity).
Variable Ceqb_eq: forall x y:C, Ceqb x y = true -> (x == y).

Instance equalityb_coef : Equalityb C :=
  {equalityb x y := Ceqb x y}.

 Fixpoint Peq (P P' : Pol) {struct P'} : bool :=
  match P, P' with
  | Pc c, Pc c' => c =? c'
  | PX P i n Q, PX P' i' n' Q' =>
    match Pos.compare i i', Pos.compare n n' with
    | Eq, Eq => if Peq P P' then Peq Q Q' else false
    | _,_ => false
    end
  | _, _ => false
  end.

Instance equalityb_pol : Equalityb Pol :=
  {equalityb x y := Peq x y}.

(* Q a ses variables de queue < i *)
 Definition mkPX P i n Q :=
  match P with
  | Pc c => if c =? cO then Q else PX P i n Q 
  | PX P' i' n' Q' => 
       match Pos.compare i i' with
        | Eq => if Q' =? P0 then PX P' i (n + n') Q else PX P i n Q
        | _ => PX P i n Q
       end
  end.

 Definition mkXi i n := PX P1 i n P0.

 Definition mkX i := mkXi i 1.

 (** Opposite of addition *)

 Fixpoint Popp (P:Pol) : Pol :=
  match P with
  | Pc c => Pc (- c)
  | PX P i n Q => PX (Popp P) i n (Popp Q)
  end.

 Notation "-- P" := (Popp P)(at level 30).

 (** Addition et subtraction *)

 Fixpoint PaddCl (c:C)(P:Pol) {struct P} : Pol :=
  match P with
  | Pc c1 => Pc (c + c1)
  | PX P i n Q => PX P i n (PaddCl c Q)
  end.

(* Q quelconque *)

Section PaddX.
Variable Padd:Pol->Pol->Pol.
Variable P:Pol.

(* Xi^n * P + Q
les variables de tete de Q ne sont pas forcement < i 
mais Q est normalisé : variables de tete decroissantes *)

Fixpoint PaddX (i n:positive)(Q:Pol){struct Q}:=
  match Q with
  | Pc c => mkPX P i n Q
  | PX P' i' n' Q' => 
      match Pos.compare i i' with
      | (* i > i' *)
        Gt => mkPX P i n Q
      | (* i < i' *)
        Lt => mkPX P' i' n' (PaddX i n Q')
      | (* i = i' *)
        Eq => match ZPminus n n' with
              | (* n > n' *) 
                Zpos k => mkPX (PaddX i k P') i' n' Q'
              | (* n = n' *)
                Z0 => mkPX (Padd P P') i n Q'
              | (* n < n' *)
                Zneg k => mkPX (Padd P (mkPX P' i k P0)) i n Q'
              end
      end
  end.

End PaddX.

Fixpoint Padd (P1 P2: Pol) {struct P1} : Pol :=
  match P1 with
  | Pc c => PaddCl c P2
  | PX P' i' n' Q' =>
      PaddX Padd P' i' n' (Padd Q' P2)
  end.

 Notation "P ++ P'" := (Padd P P').

Definition Psub(P P':Pol):= P ++ (--P').

 Notation "P -- P'" := (Psub P P')(at level 50).

 (** Multiplication *)

 Fixpoint PmulC_aux (P:Pol) (c:C)  {struct P} : Pol :=
  match P with
  | Pc c' => Pc (c' * c)
  | PX P i n Q => mkPX (PmulC_aux P c) i n (PmulC_aux Q c)
  end.

 Definition PmulC P c :=
  if c =? cO then P0 else
  if c =? cI then P else PmulC_aux P c.

 Fixpoint Pmul (P1 P2 : Pol) {struct P2} : Pol :=
   match P2 with
   | Pc c => PmulC P1 c
   | PX P i n Q =>
     PaddX Padd (Pmul P1 P) i n (Pmul P1 Q)
   end.

 Notation "P ** P'" := (Pmul P P')(at level 40).

 Definition Psquare (P:Pol) : Pol := P ** P.


 (** Evaluation of a polynomial towards R *)

 Fixpoint Pphi(l:list R) (P:Pol) {struct P} : R :=
  match P with
  | Pc c => [c]
  | PX P i n Q =>
     let x := nth 0 i l in
     let xn := pow_pos Rr x n in
   (Pphi l P) * xn + (Pphi l Q)
  end.

 Reserved Notation "P @ l " (at level 10, no associativity).
 Notation "P @ l " := (Pphi l P).
 (** Proofs *)
 Lemma ZPminus_spec : forall x y,
  match ZPminus x y with
  | Z0 => x = y
  | Zpos k => x = (y + k)%positive
  | Zneg k => y = (x + k)%positive
  end.
 Proof.
  induction x;destruct y.
  replace (ZPminus (xI x) (xI y)) with (Zdouble (ZPminus x y));trivial.
  assert (H := IHx y);destruct (ZPminus x y);unfold Zdouble;rewrite H;trivial.
  replace (ZPminus (xI x) (xO y)) with (Zdouble_plus_one (ZPminus x y));trivial.
  assert (H := IHx y);destruct (ZPminus x y);unfold Zdouble_plus_one;rewrite H;trivial.
  apply Pplus_xI_double_minus_one.
  simpl;trivial.
  replace (ZPminus (xO x) (xI y)) with (Zdouble_minus_one (ZPminus x y));trivial.
  assert (H := IHx y);destruct (ZPminus x y);unfold Zdouble_minus_one;rewrite H;trivial.
  apply Pplus_xI_double_minus_one.
  replace (ZPminus (xO x) (xO y)) with (Zdouble (ZPminus x y));trivial.
  assert (H := IHx y);destruct (ZPminus x y);unfold Zdouble;rewrite H;trivial.
  replace (ZPminus (xO x) xH) with (Zpos (Pdouble_minus_one x));trivial.
  rewrite <- Pplus_one_succ_l.
  rewrite Psucc_o_double_minus_one_eq_xO;trivial.
  replace (ZPminus xH (xI y)) with (Zneg (xO y));trivial.
  replace (ZPminus xH (xO y)) with (Zneg (Pdouble_minus_one y));trivial.
  rewrite <- Pplus_one_succ_l.
  rewrite Psucc_o_double_minus_one_eq_xO;trivial.
  simpl;trivial.
 Qed.

 Lemma Peq_ok : forall P P',
    (P =? P') = true -> forall l, P@l == P'@ l.
 Proof.
  induction P;destruct P';simpl;intros;try discriminate;trivial. apply ring_morphism_eq.
  apply Ceqb_eq ;trivial.
  destruct (Pos.compare_spec p p1); try discriminate H.
  destruct (Pos.compare_spec p0 p2); try discriminate H.
  assert (H1' := IHP1 P'1);assert (H2' := IHP2 P'2).
  simpl in H1'. destruct (Peq P2 P'1); try discriminate H.
  simpl in H2'. destruct (Peq P3 P'2); try discriminate H.
  ring_rewrite (H1');trivial . ring_rewrite (H2');trivial.
  subst. rrefl.
 Qed.

 Lemma Pphi0 : forall l, P0@l == 0.
 Proof.
  intros;simpl. unfold cO. ring_rewrite ring_morphism0. rrefl.
 Qed.

 Lemma Pphi1 : forall l,  P1@l == 1.
 Proof.
  intros;simpl; unfold cI; ring_rewrite ring_morphism1. rrefl.
 Qed.

 Let pow_pos_Pplus :=
    pow_pos_Pplus Rr.

 Lemma mkPX_ok : forall l P i n Q,
  (mkPX P i n Q)@l == P@l * (pow_pos Rr (nth 0 i l) n) + Q@l.
 Proof.
  intros l P i n Q;unfold mkPX.
  destruct P;try (simpl;rrefl).
  assert (H := ring_morphism_eq  c cO). simpl; case_eq (Ceqb c cO);simpl;try rrefl.
intros.
  ring_rewrite H. ring_rewrite ring_morphism0.
  rsimpl. apply Ceqb_eq. trivial.
  case Pos.compare_spec; intros; subst.
  assert (H := @Peq_ok P3 P0). case_eq (P3=? P0). intro. simpl.
  ring_rewrite H; trivial.
  ring_rewrite Pphi0. rsimpl. ring_rewrite Pplus_comm.
  ring_rewrite pow_pos_Pplus;rsimpl; trivial.
  rrefl.
  rrefl.
  rrefl.
 Qed.

Ltac Esimpl :=
  repeat (progress (
   match goal with
   | |- context [?P@?l] =>
       match P with
       | P0 => ring_rewrite (Pphi0 l)
       | P1 => ring_rewrite (Pphi1 l)
       | (mkPX ?P ?i ?n ?Q) => ring_rewrite (mkPX_ok l P i n Q)
       end
   | |- context [[?c]] =>
       match c with
       | cO => ring_rewrite ring_morphism0
       | cI => ring_rewrite ring_morphism1
       | ?x + ?y => ring_rewrite ring_morphism_add
       | ?x * ?y => ring_rewrite ring_morphism_mul
       | ?x - ?y => ring_rewrite ring_morphism_sub
       | - ?x => ring_rewrite ring_morphism_opp
       end
   end));
  ring_simpl; rsimpl.

 Lemma PaddCl_ok : forall c P l, (PaddCl c P)@l == [c] + P@l .
 Proof.
  induction P; ring_simpl; intros; Esimpl; try rrefl. 
  ring_rewrite IHP2. rsimpl. 
ring_rewrite (ring_add_comm  (P2 @ l * pow_pos Rr (nth 0 p l) p0) [c]).
rrefl.
 Qed.

 Lemma PmulC_aux_ok : forall c P l, (PmulC_aux P c)@l ==  P@l * [c].
 Proof.
  induction P;ring_simpl;intros;Esimpl;try rrefl.
  ring_rewrite IHP1;ring_rewrite IHP2;rsimpl. 
 Qed.

 Lemma PmulC_ok : forall c P l, (PmulC P c)@l ==  P@l * [c].
 Proof.
  intros c P l; unfold PmulC.
  assert (H:= ring_morphism_eq c cO);case_eq (c =? cO). intros.
  ring_rewrite H;Esimpl. apply Ceqb_eq;trivial. 
  assert (H1:= ring_morphism_eq c cI);case_eq (c =? cI);intros.
  ring_rewrite H1;Esimpl. apply Ceqb_eq;trivial.
  apply PmulC_aux_ok.
 Qed.

 Lemma Popp_ok : forall P l, (--P)@l == - P@l.
 Proof.
  induction P;ring_simpl;intros.
  Esimpl.
  ring_rewrite IHP1;ring_rewrite IHP2;rsimpl.
 Qed.

 Ltac Esimpl2 :=
  Esimpl;
  repeat (progress (
   match goal with
   | |- context [(PaddCl ?c ?P)@?l] => ring_rewrite (PaddCl_ok c P l)
   | |- context [(PmulC ?P ?c)@?l] => ring_rewrite (PmulC_ok c P l)
   | |- context [(--?P)@?l] => ring_rewrite (Popp_ok P l)
   end)); Esimpl.

Lemma PaddXPX: forall P i n Q,
  PaddX Padd P i n Q =
  match Q with
  | Pc c => mkPX P i n Q
  | PX P' i' n' Q' => 
      match Pos.compare i i' with
      | (* i > i' *)
        Gt => mkPX P i n Q
      | (* i < i' *)
        Lt => mkPX P' i' n' (PaddX Padd P i n Q')
      | (* i = i' *)
        Eq => match ZPminus n n' with
              | (* n > n' *) 
                Zpos k => mkPX (PaddX Padd P i k P') i' n' Q'
              | (* n = n' *)
                Z0 => mkPX (Padd P P') i n Q'
              | (* n < n' *)
                Zneg k => mkPX (Padd P (mkPX P' i k P0)) i n Q'
              end
      end
  end.
induction Q; reflexivity.
Qed.

Lemma PaddX_ok2 : forall P2,
   (forall P l, (P2 ++ P) @ l == P2 @ l + P @ l)
   /\
   (forall P k n l,
           (PaddX Padd P2 k n P) @ l == 
             P2 @ l * pow_pos Rr (nth 0 k l) n  + P @ l).
induction P2;ring_simpl;intros. split. intros. apply PaddCl_ok.
 induction P.  unfold PaddX. intros. ring_rewrite mkPX_ok.
 ring_simpl. rsimpl.
intros. ring_simpl.
 case Pos.compare_spec; intros; subst.
 assert (H1 := ZPminus_spec n p0);destruct (ZPminus n p0). Esimpl2.
 rewrite H1. rrefl.
ring_simpl. ring_rewrite mkPX_ok. ring_rewrite IHP1. Esimpl2.
 rewrite Pplus_comm in H1.
rewrite H1. 
ring_rewrite pow_pos_Pplus.  Esimpl2.
ring_rewrite mkPX_ok. ring_rewrite PaddCl_ok. Esimpl2. rewrite Pplus_comm in H1.
rewrite H1.  Esimpl2. ring_rewrite pow_pos_Pplus. Esimpl2.
ring_rewrite mkPX_ok. ring_rewrite IHP2. Esimpl2.
ring_rewrite (ring_add_comm  (P2 @ l * pow_pos Rr (nth 0 p l) p0) 
                             ([c] * pow_pos Rr (nth 0 k l) n)).
rrefl.  assert (H1 := ring_morphism_eq c cO);case_eq (Ceqb c  cO); 
 intros; ring_simpl.
ring_rewrite H1;trivial. Esimpl2. apply Ceqb_eq; trivial. rrefl.
decompose [and] IHP2_1. decompose [and] IHP2_2. clear IHP2_1 IHP2_2.
split. intros. ring_rewrite H0. ring_rewrite H1.
Esimpl2.
induction P. unfold PaddX. intros. ring_rewrite mkPX_ok. ring_simpl. rrefl.
intros. ring_rewrite PaddXPX. 
case Pos.compare_spec; intros; subst.
assert (H4 := ZPminus_spec n p2);destruct (ZPminus n p2). 
ring_rewrite mkPX_ok. ring_simpl. ring_rewrite H0. ring_rewrite H1. Esimpl2.
rewrite H4. rrefl.
ring_rewrite mkPX_ok. ring_rewrite IHP1. Esimpl2.
rewrite Pplus_comm in H4.
rewrite H4. ring_rewrite pow_pos_Pplus. Esimpl2.
ring_rewrite mkPX_ok. ring_simpl. ring_rewrite H0. ring_rewrite H1. 
ring_rewrite mkPX_ok.
 Esimpl2.
 rewrite Pplus_comm in H4.
rewrite H4. ring_rewrite pow_pos_Pplus. Esimpl2.
ring_rewrite mkPX_ok. ring_simpl. ring_rewrite IHP2. Esimpl2.
gen_add_push (P2 @ l * pow_pos Rr (nth 0 p1 l) p2). try rrefl.
ring_rewrite mkPX_ok. ring_simpl. rrefl.
Qed.

Lemma Padd_ok : forall P Q l, (P ++ Q) @ l == P @ l + Q @ l.
intro P. elim (PaddX_ok2 P); auto.
Qed.

Lemma PaddX_ok : forall P2 P k n l,
   (PaddX Padd P2 k n P) @ l ==  P2 @ l * pow_pos Rr (nth 0 k l) n  + P @ l.
intro P2. elim (PaddX_ok2 P2); auto.
Qed.

 Lemma Psub_ok : forall P' P l, (P -- P')@l == P@l - P'@l.
unfold Psub. intros. ring_rewrite Padd_ok. ring_rewrite Popp_ok. rsimpl.
 Qed.

 Lemma Pmul_ok : forall P P' l, (P**P')@l == P@l * P'@l.
induction P'; ring_simpl; intros. ring_rewrite PmulC_ok. rrefl.
ring_rewrite PaddX_ok. ring_rewrite IHP'1. ring_rewrite IHP'2. Esimpl2.
Qed.

 Lemma Psquare_ok : forall P l, (Psquare P)@l == P@l * P@l.
 Proof.
  intros. unfold Psquare. apply Pmul_ok.
 Qed.

 (** Definition of polynomial expressions *)

 Inductive PExpr : Type :=
  | PEc : C -> PExpr
  | PEX : positive -> PExpr
  | PEadd : PExpr -> PExpr -> PExpr
  | PEsub : PExpr -> PExpr -> PExpr
  | PEmul : PExpr -> PExpr -> PExpr
  | PEopp : PExpr -> PExpr
  | PEpow : PExpr -> N -> PExpr.

 (** Specification of the power function *)
 Section POWER.
  Variable Cpow : Set.
  Variable Cp_phi : N -> Cpow.
  Variable rpow : R -> Cpow -> R.

  Record power_theory : Prop := mkpow_th {
    rpow_pow_N : forall r n,  (rpow r (Cp_phi n))== (pow_N Rr r n)
  }.

 End POWER.
 Variable Cpow : Set.
 Variable Cp_phi : N -> Cpow.
 Variable rpow : R -> Cpow -> R.
 Variable pow_th : power_theory Cp_phi rpow.

 (** evaluation of polynomial expressions towards R *)
 Fixpoint PEeval (l:list R) (pe:PExpr) {struct pe} : R :=
   match pe with
   | PEc c => [c]
   | PEX j => nth 0 j l
   | PEadd pe1 pe2 => (PEeval l pe1) + (PEeval l pe2)
   | PEsub pe1 pe2 => (PEeval l pe1) - (PEeval l pe2)
   | PEmul pe1 pe2 => (PEeval l pe1) * (PEeval l pe2)
   | PEopp pe1 => - (PEeval l pe1)
   | PEpow pe1 n => rpow (PEeval l pe1) (Cp_phi n)
   end.

Strategy expand [PEeval].

 Definition mk_X j := mkX j.

 (** Correctness proofs *)

 Lemma mkX_ok : forall p l, nth 0 p l == (mk_X p) @ l.
 Proof.
  destruct p;ring_simpl;intros;Esimpl;trivial.
 Qed.

 Ltac Esimpl3 :=
  repeat match goal with
  | |- context [(?P1 ++ ?P2)@?l] => ring_rewrite (Padd_ok P1 P2 l)
  | |- context [(?P1 -- ?P2)@?l] => ring_rewrite (Psub_ok P1 P2 l)
  end;try Esimpl2;try rrefl;try apply ring_add_comm.

(* Power using the chinise algorithm *)

Section POWER2.
  Variable subst_l : Pol -> Pol.
  Fixpoint Ppow_pos (res P:Pol) (p:positive){struct p} : Pol :=
   match p with
   | xH => subst_l (Pmul P res)
   | xO p => Ppow_pos (Ppow_pos res P p) P p
   | xI p => subst_l (Pmul P (Ppow_pos (Ppow_pos res P p) P p))
   end.

  Definition Ppow_N P n :=
   match n with
   | N0 => P1
   | Npos p => Ppow_pos P1 P p
   end.

  Fixpoint pow_pos_gen (R:Type)(m:R->R->R)(x:R) (i:positive) {struct i}: R :=
  match i with
  | xH => x
  | xO i => let p := pow_pos_gen m x i in m p p
  | xI i => let p := pow_pos_gen m x i in m x (m p p)
  end.

Lemma Ppow_pos_ok : forall l, (forall P, subst_l P@l == P@l) ->
         forall res P p, (Ppow_pos res P p)@l == (pow_pos_gen Pmul P p)@l * res@l.
  Proof.
   intros l subst_l_ok res P p. generalize res;clear res.
   induction p;ring_simpl;intros. try ring_rewrite subst_l_ok.
 repeat ring_rewrite Pmul_ok. repeat ring_rewrite IHp.
   rsimpl. repeat ring_rewrite Pmul_ok. repeat ring_rewrite IHp. rsimpl.
 try ring_rewrite subst_l_ok.
 repeat ring_rewrite Pmul_ok. rrefl.
  Qed.

Definition pow_N_gen (R:Type)(x1:R)(m:R->R->R)(x:R) (p:N) :=
  match p with
  | N0 => x1
  | Npos p => pow_pos_gen m x p
  end.

  Lemma Ppow_N_ok : forall l,  (forall P, subst_l P@l == P@l) ->
         forall P n, (Ppow_N P n)@l == (pow_N_gen P1 Pmul P n)@l.
  Proof.  destruct n;ring_simpl. rrefl. ring_rewrite Ppow_pos_ok; trivial. Esimpl.  Qed.

 End POWER2.

 (** Normalization and rewriting *)

 Section NORM_SUBST_REC.
  Let subst_l (P:Pol) := P.
  Let Pmul_subst P1 P2 := subst_l (Pmul P1 P2).
  Let Ppow_subst := Ppow_N subst_l.

  Fixpoint norm_aux (pe:PExpr) : Pol :=
   match pe with
   | PEc c => Pc c
   | PEX j => mk_X j
   | PEadd pe1 (PEopp pe2) =>
     Psub (norm_aux pe1) (norm_aux pe2)
   | PEadd pe1 pe2 => Padd (norm_aux  pe1) (norm_aux pe2)
   | PEsub pe1 pe2 => Psub (norm_aux pe1) (norm_aux pe2)
   | PEmul pe1 pe2 => Pmul (norm_aux pe1) (norm_aux pe2)
   | PEopp pe1 => Popp (norm_aux pe1)
   | PEpow pe1 n => Ppow_N (fun p => p) (norm_aux pe1) n
   end.

  Definition norm_subst pe := subst_l (norm_aux pe).

 
 Lemma norm_aux_spec :
     forall l pe, 
       PEeval l pe == (norm_aux pe)@l.
  Proof.
   intros.
   induction pe.
Esimpl3. Esimpl3. ring_simpl.
 ring_rewrite IHpe1;ring_rewrite IHpe2.
 destruct pe2; Esimpl3. 
unfold Psub.
destruct pe1. destruct pe2. Esimpl3. Esimpl3. Esimpl3. Esimpl3. Esimpl3. Esimpl3.
 Esimpl3. Esimpl3. Esimpl3. Esimpl3. Esimpl3. Esimpl3. Esimpl3.
ring_simpl. unfold Psub. ring_rewrite IHpe1;ring_rewrite IHpe2.
destruct pe1. destruct pe2. Esimpl3. Esimpl3. Esimpl3. Esimpl3. Esimpl3. Esimpl3.
 Esimpl3. Esimpl3. Esimpl3. Esimpl3. Esimpl3. Esimpl3. Esimpl3.
ring_simpl. ring_rewrite IHpe1;ring_rewrite IHpe2. ring_rewrite Pmul_ok. rrefl.
ring_simpl. ring_rewrite IHpe; Esimpl3. 
ring_simpl.
   ring_rewrite Ppow_N_ok; (intros;try rrefl). 
   ring_rewrite rpow_pow_N.  Esimpl3.
   induction n;ring_simpl. Esimpl3. induction p; ring_simpl.
  try ring_rewrite IHp;try ring_rewrite IHpe;
 repeat ring_rewrite Pms_ok;
      repeat ring_rewrite Pmul_ok;rrefl.
ring_rewrite Pmul_ok. try ring_rewrite IHp;try ring_rewrite IHpe;
 repeat ring_rewrite Pms_ok;
      repeat ring_rewrite Pmul_ok;rrefl. trivial.
exact pow_th.
  Qed.

 Lemma norm_subst_spec :
     forall l pe, 
       PEeval l pe == (norm_subst pe)@l.
 Proof.
  intros;unfold norm_subst.
  unfold subst_l.  apply norm_aux_spec. 
 Qed.

 End NORM_SUBST_REC.

 Fixpoint interp_PElist (l:list R) (lpe:list (PExpr*PExpr)) {struct lpe} : Prop :=
   match lpe with
   | nil => True
   | (me,pe)::lpe =>
     match lpe with
     | nil => PEeval l me == PEeval l pe
     | _ => PEeval l me == PEeval l pe /\ interp_PElist l lpe
     end
  end.


 Lemma norm_subst_ok : forall l pe,
   PEeval l pe == (norm_subst pe)@l.
 Proof.
   intros;apply norm_subst_spec. 
  Qed.


 Lemma ring_correct : forall l pe1 pe2,
   (norm_subst pe1 =? norm_subst pe2) = true ->
   PEeval l pe1 == PEeval l pe2.
 Proof.
  ring_simpl;intros.
  do 2 (ring_rewrite (norm_subst_ok l);trivial).
  apply Peq_ok;trivial.
 Qed.


End MakeRingPol.