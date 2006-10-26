(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Set Implicit Arguments.
Require Import Setoid.
Require Import BinList.
Require Import BinPos.
Require Import BinInt.
Require Export Ring_theory.

Import RingSyntax.

Section MakeRingPol.
 
 (* Ring elements *)     
 Variable R:Type.
 Variable (rO rI : R) (radd rmul rsub: R->R->R) (ropp : R->R).
 Variable req : R -> R -> Prop.
 
 (* Ring properties *)
 Variable Rsth : Setoid_Theory R req.
 Variable Reqe : ring_eq_ext radd rmul ropp req.
 Variable ARth : almost_ring_theory rO rI radd rmul rsub ropp req.

 (* Coefficients *) 
 Variable C: Type.
 Variable (cO cI: C) (cadd cmul csub : C->C->C) (copp : C->C).
 Variable ceqb : C->C->bool. 
 Variable phi : C -> R.
 Variable CRmorph : ring_morph rO rI radd rmul rsub ropp req
                                cO cI cadd cmul csub copp ceqb phi.


 (* R notations *)
 Notation "0" := rO. Notation "1" := rI.
 Notation "x + y" := (radd x y).  Notation "x * y " := (rmul x y).
 Notation "x - y " := (rsub x y). Notation "- x" := (ropp x).
 Notation "x == y" := (req x y).

 (* C notations *)		 
 Notation "x +! y" := (cadd x y). Notation "x *! y " := (cmul x y).
 Notation "x -! y " := (csub x y). Notation "-! x" := (copp x).
 Notation " x ?=! y" := (ceqb x y). Notation "[ x ]" := (phi x).

 (* Usefull tactics *)		  
  Add Setoid R req Rsth as R_set1.
 Ltac rrefl := gen_reflexivity Rsth.
  Add Morphism radd : radd_ext.  exact (Radd_ext Reqe). Qed.
  Add Morphism rmul : rmul_ext.  exact (Rmul_ext Reqe). Qed.
  Add Morphism ropp : ropp_ext.  exact (Ropp_ext Reqe). Qed.
  Add Morphism rsub : rsub_ext. exact (ARsub_ext Rsth Reqe ARth). Qed.
 Ltac rsimpl := gen_srewrite 0 1 radd rmul rsub ropp req Rsth Reqe ARth.
 Ltac add_push := gen_add_push radd Rsth Reqe ARth.
 Ltac mul_push := gen_mul_push rmul Rsth Reqe ARth.

 (* Definition of multivariable polynomials with coefficients in C :
    Type [Pol] represents [X1 ... Xn].
    The representation is Horner's where a [n] variable polynomial
    (C[X1..Xn]) is seen as a polynomial on [X1] which coefficients
    are polynomials with [n-1] variables (C[X2..Xn]).
    There are several optimisations to make the repr compacter:
    - [Pc c] is the constant polynomial of value c
       == c*X1^0*..*Xn^0
    - [Pinj j Q] is a polynomial constant w.r.t the [j] first variables.
        variable indices are shifted of j in Q.
       == X1^0 *..* Xj^0 * Q{X1 <- Xj+1;..; Xn-j <- Xn}
    - [PX P i Q] is an optimised Horner form of P*X^i + Q
        with P not the null polynomial
       == P * X1^i + Q{X1 <- X2; ..; Xn-1 <- Xn}

    In addition:
    - polynomials of the form (PX (PX P i (Pc 0)) j Q) are forbidden
      since they can be represented by the simpler form (PX P (i+j) Q)
    - (Pinj i (Pinj j P)) is (Pinj (i+j) P)
    - (Pinj i (Pc c)) is (Pc c)
 *)

 Inductive Pol : Type :=
  | Pc : C -> Pol 
  | Pinj : positive -> Pol -> Pol                   
  | PX : Pol -> positive -> Pol -> Pol.

 Definition P0 := Pc cO.
 Definition P1 := Pc cI.
 
 Fixpoint Peq (P P' : Pol) {struct P'} : bool := 
  match P, P' with
  | Pc c, Pc c' => c ?=! c'
  | Pinj j Q, Pinj j' Q' => 
    match Pcompare j j' Eq with
    | Eq => Peq Q Q' 
    | _ => false 
    end
  | PX P i Q, PX P' i' Q' =>
    match Pcompare i i' Eq with
    | Eq => if Peq P P' then Peq Q Q' else false
    | _ => false
    end
  | _, _ => false
  end.

 Notation " P ?== P' " := (Peq P P').

 Definition mkPinj j P :=
  match P with 
  | Pc _ => P
  | Pinj j' Q => Pinj ((j + j'):positive) Q
  | _ => Pinj j P
  end.

 Definition mkPX P i Q := 
  match P with
  | Pc c => if c ?=! cO then mkPinj xH Q else PX P i Q
  | Pinj _ _ => PX P i Q
  | PX P' i' Q' => if Q' ?== P0 then PX P' (i' + i) Q else PX P i Q
  end.
 
 (** Opposite of addition *)
 
 Fixpoint Popp (P:Pol) : Pol := 
  match P with
  | Pc c => Pc (-! c)
  | Pinj j Q => Pinj j (Popp Q)
  | PX P i Q => PX (Popp P) i (Popp Q)
  end.
 
 Notation "-- P" := (Popp P).

 (** Addition et subtraction *)
 
 Fixpoint PaddC (P:Pol) (c:C) {struct P} : Pol :=
  match P with
  | Pc c1 => Pc (c1 +! c)
  | Pinj j Q => Pinj j (PaddC Q c)
  | PX P i Q => PX P i (PaddC Q c)
  end.

 Fixpoint PsubC (P:Pol) (c:C) {struct P} : Pol :=
  match P with
  | Pc c1 => Pc (c1 -! c)
  | Pinj j Q => Pinj j (PsubC Q c)
  | PX P i Q => PX P i (PsubC Q c)
  end.

 Section PopI.

  Variable Pop : Pol -> Pol -> Pol.
  Variable Q : Pol.

  Fixpoint PaddI (j:positive) (P:Pol){struct P} : Pol :=
   match P with
   | Pc c => mkPinj j (PaddC Q c)
   | Pinj j' Q' => 
     match ZPminus j' j with
     | Zpos k =>  mkPinj j (Pop (Pinj k Q') Q)
     | Z0 => mkPinj j (Pop Q' Q)
     | Zneg k => mkPinj j' (PaddI k Q')
     end
   | PX P i Q' => 
     match j with
     | xH => PX P i (Pop Q' Q)
     | xO j => PX P i (PaddI (Pdouble_minus_one j) Q')
     | xI j => PX P i (PaddI (xO j) Q')
     end 
   end.

  Fixpoint PsubI (j:positive) (P:Pol){struct P} : Pol :=
   match P with
   | Pc c => mkPinj j (PaddC (--Q) c)
   | Pinj j' Q' => 
     match ZPminus j' j with
     | Zpos k =>  mkPinj j (Pop (Pinj k Q') Q)
     | Z0 => mkPinj j (Pop Q' Q)
     | Zneg k => mkPinj j' (PsubI k Q')
     end
   | PX P i Q' => 
     match j with
     | xH => PX P i (Pop Q' Q)
     | xO j => PX P i (PsubI (Pdouble_minus_one j) Q')
     | xI j => PX P i (PsubI (xO j) Q')
     end 
   end.
 
 Variable P' : Pol.
 
 Fixpoint PaddX (i':positive) (P:Pol) {struct P} : Pol :=
  match P with
  | Pc c => PX P' i' P
  | Pinj j Q' =>
    match j with
    | xH =>  PX P' i' Q'
    | xO j => PX P' i' (Pinj (Pdouble_minus_one j) Q')
    | xI j => PX P' i' (Pinj (xO j) Q')
    end
  | PX P i Q' =>
    match ZPminus i i' with
    | Zpos k => mkPX (Pop (PX P k P0) P') i' Q'
    | Z0 => mkPX (Pop P P') i Q'
    | Zneg k => mkPX (PaddX k P) i Q'
    end
  end.

 Fixpoint PsubX (i':positive) (P:Pol) {struct P} : Pol :=
  match P with
  | Pc c => PX (--P') i' P
  | Pinj j Q' =>
    match j with
    | xH =>  PX (--P') i' Q'
    | xO j => PX (--P') i' (Pinj (Pdouble_minus_one j) Q')
    | xI j => PX (--P') i' (Pinj (xO j) Q')
    end
  | PX P i Q' =>
    match ZPminus i i' with
    | Zpos k => mkPX (Pop (PX P k P0) P') i' Q'
    | Z0 => mkPX (Pop P P') i Q'
    | Zneg k => mkPX (PsubX k P) i Q'
    end
  end.

    
 End PopI.

 Fixpoint Padd (P P': Pol) {struct P'} : Pol :=
  match P' with
  | Pc c' => PaddC P c'
  | Pinj j' Q' => PaddI Padd Q' j' P
  | PX P' i' Q' =>
    match P with
    | Pc c => PX P' i' (PaddC Q' c)
    | Pinj j Q =>  
      match j with
      | xH => PX P' i' (Padd Q Q')
      | xO j => PX P' i' (Padd (Pinj (Pdouble_minus_one j) Q) Q')
      | xI j => PX P' i' (Padd (Pinj (xO j) Q) Q')
      end 
    | PX P i Q =>
      match ZPminus i i' with
      | Zpos k => mkPX (Padd (PX P k P0) P') i' (Padd Q Q')
      | Z0 => mkPX (Padd P P') i (Padd Q Q')
      | Zneg k => mkPX (PaddX Padd P' k P) i (Padd Q Q')
      end
    end
  end.
 Notation "P ++ P'" := (Padd P P').

 Fixpoint Psub (P P': Pol) {struct P'} : Pol :=
  match P' with
  | Pc c' => PsubC P c'
  | Pinj j' Q' => PsubI Psub Q' j' P
  | PX P' i' Q' =>
    match P with
    | Pc c => PX (--P') i' (*(--(PsubC Q' c))*) (PaddC (--Q') c)
    | Pinj j Q =>  
      match j with
      | xH => PX (--P') i' (Psub Q Q')
      | xO j => PX (--P') i' (Psub (Pinj (Pdouble_minus_one j) Q) Q')
      | xI j => PX (--P') i' (Psub (Pinj (xO j) Q) Q')
      end 
    | PX P i Q =>
      match ZPminus i i' with
      | Zpos k => mkPX (Psub (PX P k P0) P') i' (Psub Q Q')
      | Z0 => mkPX (Psub P P') i (Psub Q Q')
      | Zneg k => mkPX (PsubX Psub P' k P) i (Psub Q Q')
      end
    end
  end.
 Notation "P -- P'" := (Psub P P').
 
 (** Multiplication *) 

 Fixpoint PmulC_aux (P:Pol) (c:C) {struct P} : Pol :=
  match P with
  | Pc c' => Pc (c' *! c)
  | Pinj j Q => mkPinj j (PmulC_aux Q c)
  | PX P i Q => mkPX (PmulC_aux P c) i (PmulC_aux Q c)
  end.

 Definition PmulC P c :=
  if c ?=! cO then P0 else
  if c ?=! cI then P else PmulC_aux P c.
 
 Section PmulI. 
  Variable Pmul : Pol -> Pol -> Pol.
  Variable Q : Pol.
  Fixpoint PmulI (j:positive) (P:Pol) {struct P} : Pol :=
   match P with
   | Pc c => mkPinj j (PmulC Q c)
   | Pinj j' Q' => 
     match ZPminus j' j with
     | Zpos k => mkPinj j (Pmul (Pinj k Q') Q)
     | Z0 => mkPinj j (Pmul Q' Q)
     | Zneg k => mkPinj j' (PmulI k Q')
     end
   | PX P' i' Q' =>
     match j with
     | xH => mkPX (PmulI xH P') i' (Pmul Q' Q)
     | xO j' => mkPX (PmulI j P') i' (PmulI (Pdouble_minus_one j') Q')
     | xI j' => mkPX (PmulI j P') i' (PmulI (xO j') Q')
     end
   end.
 
 End PmulI.

 Fixpoint Pmul_aux (P P' : Pol) {struct P'} : Pol :=
  match P' with
  | Pc c' => PmulC P c'
  | Pinj j' Q' => PmulI Pmul_aux Q' j' P
  | PX P' i' Q' => 
     (mkPX (Pmul_aux P P') i' P0) ++ (PmulI Pmul_aux Q' xH P)
  end.

 Definition Pmul P P' :=
  match P with
  | Pc c => PmulC P' c
  | Pinj j Q => PmulI Pmul_aux Q j P'
  | PX P i Q => 
    Padd (mkPX (Pmul_aux P P') i P0) (PmulI Pmul_aux Q xH P')
  end.
 Notation "P ** P'" := (Pmul P P').
 

 (** Monomial **)
     
  Inductive Mon: Set :=
    mon0: Mon 
  | zmon: positive -> Mon -> Mon 
  | vmon: positive -> Mon -> Mon.

 Fixpoint pow (x:R) (i:positive) {struct i}: R :=
  match i with
  | xH => x
  | xO i => let p := pow x i in p * p
  | xI i => let p := pow x i in x * p * p
  end.

 Fixpoint Mphi(l:list R) (M: Mon) {struct M} : R :=
  match M with
     mon0 => rI
  | zmon j M1  => Mphi (jump j l) M1
  | vmon i M1 =>
     let x := hd 0 l in
     let xi := pow x i in
    (Mphi (tail l) M1) * xi 
  end.

 Definition zmon_pred j M :=
   match j with xH => M | _ => zmon (Ppred j) M end.

 Definition mkZmon j M :=
   match M with mon0 => mon0 | _ => zmon j M end.

 Fixpoint MFactor (P: Pol) (M: Mon) {struct P}: Pol * Pol :=
   match P, M with
        _, mon0 => (Pc cO, P)
   | Pc _, _    => (P, Pc cO)
   | Pinj j1 P1, zmon j2 M1 =>
      match (j1 ?= j2) Eq with
        Eq => let (R,S) := MFactor P1 M1 in
                 (mkPinj j1 R, mkPinj j1 S)
      | Lt => let (R,S) := MFactor P1 (zmon (j2 - j1) M1) in
                 (mkPinj j1 R, mkPinj j1 S)
      | Gt => (P, Pc cO)
      end
  | Pinj _ _, vmon _ _ => (P, Pc cO)
  | PX P1 i Q1, zmon j M1 =>
             let M2 := zmon_pred j M1 in
             let (R1, S1) := MFactor P1 M in
             let (R2, S2) := MFactor Q1 M2 in
               (mkPX R1 i R2, mkPX S1 i S2)
  | PX P1 i Q1, vmon j M1 =>
      match (i ?= j) Eq with
        Eq => let (R1,S1) := MFactor P1 (mkZmon xH M1) in
                 (mkPX R1 i Q1, S1)
      | Lt => let (R1,S1) := MFactor P1 (vmon (j - i) M1) in
                 (mkPX R1 i Q1, S1)
      | Gt => let (R1,S1) := MFactor P1 (mkZmon xH M1) in
                 (mkPX R1 i Q1, mkPX S1 (i-j) (Pc cO))
      end
   end.

  Definition POneSubst (P1: Pol) (M1: Mon) (P2: Pol): option Pol :=
    let (Q1,R1) := MFactor P1 M1 in
    match R1 with 
     (Pc c) => if c ?=! cO then None 
               else Some (Padd Q1 (Pmul P2 R1))
    | _ => Some (Padd Q1 (Pmul P2 R1))
    end.

  Fixpoint PNSubst1 (P1: Pol) (M1: Mon) (P2: Pol) (n: nat) {struct n}: Pol :=
    match POneSubst P1 M1 P2 with 
     Some P3 => match n with S n1 => PNSubst1 P3 M1 P2 n1 | _ => P3 end
    | _ => P1
    end.

  Definition PNSubst (P1: Pol) (M1: Mon) (P2: Pol) (n: nat): option Pol :=
    match POneSubst P1 M1 P2 with 
     Some P3 => match n with S n1 => Some (PNSubst1 P3 M1 P2 n1) | _ => None end
    | _ => None
    end.
            
  Fixpoint PSubstL1 (P1: Pol) (LM1: list (Mon * Pol)) (n: nat) {struct LM1}: 
     Pol :=
    match LM1 with 
     cons (M1,P2) LM2 => PSubstL1 (PNSubst1 P1 M1 P2 n) LM2 n
    | _ => P1
    end.

  Fixpoint PSubstL (P1: Pol) (LM1: list (Mon * Pol)) (n: nat) {struct LM1}: option Pol :=
    match LM1 with 
     cons (M1,P2) LM2 =>
      match PNSubst P1 M1 P2 n with 
        Some P3 => Some (PSubstL1 P3 LM2 n)
     |  None => PSubstL P1 LM2 n
     end
    | _ => None
    end.

  Fixpoint PNSubstL (P1: Pol) (LM1: list (Mon * Pol)) (m n: nat) {struct m}: Pol :=
    match PSubstL P1 LM1 n with 
     Some P3 => match m with S m1 => PNSubstL P3 LM1 m1 n | _ => P3 end
    | _ => P1
    end.

 (** Evaluation of a polynomial towards R *)

 Fixpoint Pphi(l:list R) (P:Pol) {struct P} : R :=
  match P with
  | Pc c => [c]
  | Pinj j Q => Pphi (jump j l) Q
  | PX P i Q => 
     let x := hd 0 l in
     let xi := pow x i in
    (Pphi l P) * xi + (Pphi (tail l) Q)      
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

 Lemma pow_Psucc : forall x j, pow x (Psucc j) == x * pow x j.
 Proof.
  induction j;simpl;rsimpl.
  rewrite IHj;rsimpl;mul_push x;rrefl.
 Qed.

 Lemma pow_Pplus : forall x i j, pow x (i + j) == pow x i * pow x j.
 Proof.
  intro x;induction i;intros.
  rewrite xI_succ_xO;rewrite Pplus_one_succ_r.
  rewrite <- Pplus_diag;repeat rewrite <- Pplus_assoc.
  repeat rewrite IHi.
  rewrite Pplus_comm;rewrite <- Pplus_one_succ_r;rewrite pow_Psucc.
  simpl;rsimpl.
  rewrite <- Pplus_diag;repeat rewrite <- Pplus_assoc.
  repeat rewrite IHi;rsimpl.
  rewrite Pplus_comm;rewrite <- Pplus_one_succ_r;rewrite pow_Psucc;
   simpl;rsimpl.
 Qed.
  
 Lemma Peq_ok : forall P P', 
    (P ?== P') = true -> forall l, P@l == P'@ l.
 Proof.
  induction P;destruct P';simpl;intros;try discriminate;trivial.
  apply (morph_eq CRmorph);trivial.
  assert (H1 := Pcompare_Eq_eq p p0); destruct ((p ?= p0)%positive Eq);
   try discriminate H.
  rewrite (IHP P' H); rewrite H1;trivial;rrefl.
  assert (H1 := Pcompare_Eq_eq p p0); destruct ((p ?= p0)%positive Eq);
   try discriminate H.
  rewrite H1;trivial. clear H1.
  assert (H1 := IHP1 P'1);assert (H2 := IHP2 P'2);
   destruct (P2 ?== P'1);[destruct (P3 ?== P'2); [idtac|discriminate H]
                         |discriminate H].
  rewrite (H1 H);rewrite (H2 H);rrefl.
 Qed.

 Lemma Pphi0 : forall l, P0@l == 0.
 Proof.
  intros;simpl;apply (morph0 CRmorph).
 Qed.

 Lemma Pphi1 : forall l,  P1@l == 1.
 Proof.
  intros;simpl;apply (morph1 CRmorph).
 Qed.

 Lemma mkPinj_ok : forall j l P, (mkPinj j P)@l == P@(jump j l).
 Proof.
  intros j l p;destruct p;simpl;rsimpl.
  rewrite <-jump_Pplus;rewrite Pplus_comm;rrefl.
 Qed.

 Lemma mkPX_ok : forall l P i Q, 
  (mkPX P i Q)@l == P@l*(pow (hd 0 l) i) + Q@(tail l).
 Proof.
  intros l P i Q;unfold mkPX.
  destruct P;try (simpl;rrefl).
  assert (H := morph_eq CRmorph c cO);destruct (c ?=! cO);simpl;try rrefl.
  rewrite (H (refl_equal true));rewrite (morph0 CRmorph).
  rewrite mkPinj_ok;rsimpl;simpl;rrefl.
  assert (H := @Peq_ok P3 P0);destruct (P3 ?== P0);simpl;try rrefl.
  rewrite (H (refl_equal true));trivial.
  rewrite Pphi0;rewrite pow_Pplus;rsimpl.
 Qed.

 Ltac Esimpl :=
  repeat (progress (
   match goal with
   | |- context [P0@?l] => rewrite (Pphi0 l)
   | |- context [P1@?l] => rewrite (Pphi1 l)
   | |- context [(mkPinj ?j ?P)@?l] => rewrite (mkPinj_ok j l P)
   | |- context [(mkPX ?P ?i ?Q)@?l] => rewrite (mkPX_ok l P i Q)
   | |- context [[cO]] => rewrite (morph0 CRmorph)
   | |- context [[cI]] => rewrite (morph1 CRmorph)
   | |- context [[?x +! ?y]] => rewrite ((morph_add CRmorph) x y)
   | |- context [[?x *! ?y]] => rewrite ((morph_mul CRmorph) x y)
   | |- context [[?x -! ?y]] => rewrite ((morph_sub CRmorph) x y)
   | |- context [[-! ?x]] => rewrite ((morph_opp CRmorph) x)
   end));
  rsimpl; simpl. 
 
 Lemma PaddC_ok : forall c P l, (PaddC P c)@l == P@l + [c].
 Proof.
  induction P;simpl;intros;Esimpl;trivial.
  rewrite IHP2;rsimpl.
 Qed.

 Lemma PsubC_ok : forall c P l, (PsubC P c)@l == P@l - [c].
 Proof.
  induction P;simpl;intros.
  Esimpl.
  rewrite IHP;rsimpl.
  rewrite IHP2;rsimpl.
 Qed.

 Lemma PmulC_aux_ok : forall c P l, (PmulC_aux P c)@l == P@l * [c].
 Proof.
  induction P;simpl;intros;Esimpl;trivial.
  rewrite IHP1;rewrite IHP2;rsimpl.
  mul_push ([c]);rrefl.
 Qed. 

 Lemma PmulC_ok : forall c P l, (PmulC P c)@l == P@l * [c].
 Proof.
  intros c P l; unfold PmulC.
  assert (H:= morph_eq CRmorph c cO);destruct (c ?=! cO).
  rewrite (H (refl_equal true));Esimpl.
  assert (H1:= morph_eq CRmorph c cI);destruct (c ?=! cI).
  rewrite (H1 (refl_equal true));Esimpl.
  apply PmulC_aux_ok.
 Qed.

 Lemma Popp_ok : forall P l, (--P)@l == - P@l.
 Proof.
  induction P;simpl;intros.
  Esimpl.
  apply IHP.
  rewrite IHP1;rewrite IHP2;rsimpl.
 Qed.

 Ltac Esimpl2 :=
  Esimpl;
  repeat (progress (
   match goal with 
   | |- context [(PaddC ?P ?c)@?l] => rewrite (PaddC_ok c P l)
   | |- context [(PsubC ?P ?c)@?l] => rewrite (PsubC_ok c P l)
   | |- context [(PmulC ?P ?c)@?l] => rewrite (PmulC_ok c P l)
   | |- context [(--?P)@?l] => rewrite (Popp_ok P l)
   end)); Esimpl.

 Lemma Padd_ok : forall P' P l, (P ++ P')@l == P@l + P'@l.
 Proof.
  induction P';simpl;intros;Esimpl2.
  generalize P p l;clear P p l.
  induction P;simpl;intros.
  Esimpl2;apply (ARadd_sym ARth).
  assert (H := ZPminus_spec p p0);destruct (ZPminus p p0).
  rewrite H;Esimpl. rewrite IHP';rrefl.
  rewrite H;Esimpl. rewrite IHP';Esimpl.
  rewrite <- jump_Pplus;rewrite Pplus_comm;rrefl.
  rewrite H;Esimpl. rewrite IHP.
  rewrite <- jump_Pplus;rewrite Pplus_comm;rrefl.
  destruct p0;simpl.
  rewrite IHP2;simpl;rsimpl.
  rewrite IHP2;simpl.
  rewrite jump_Pdouble_minus_one;rsimpl.
  rewrite IHP';rsimpl.
  destruct P;simpl. 
  Esimpl2;add_push [c];rrefl.
  destruct p0;simpl;Esimpl2.
  rewrite IHP'2;simpl.
  rsimpl;add_push (P'1@l * (pow (hd 0 l) p));rrefl.
  rewrite IHP'2;simpl.
  rewrite jump_Pdouble_minus_one;rsimpl;add_push (P'1@l * (pow (hd 0 l) p));rrefl.
  rewrite IHP'2;rsimpl. add_push (P @ (tail l));rrefl.
  assert (H := ZPminus_spec p0 p);destruct (ZPminus p0 p);Esimpl2.
  rewrite IHP'1;rewrite IHP'2;rsimpl.
  add_push (P3 @ (tail l));rewrite H;rrefl.
  rewrite IHP'1;rewrite IHP'2;simpl;Esimpl.
  rewrite H;rewrite Pplus_comm.
  rewrite pow_Pplus;rsimpl.
  add_push (P3 @ (tail l));rrefl.
  assert (forall P k l, 
           (PaddX Padd P'1 k P) @ l == P@l + P'1@l * pow (hd 0 l) k).
   induction P;simpl;intros;try apply (ARadd_sym ARth).
   destruct p2;simpl;try apply (ARadd_sym ARth).
   rewrite jump_Pdouble_minus_one;apply (ARadd_sym ARth).
    assert (H1 := ZPminus_spec p2 k);destruct (ZPminus p2 k);Esimpl2.
    rewrite IHP'1;rsimpl; rewrite H1;add_push (P5 @ (tail l0));rrefl.
    rewrite IHP'1;simpl;Esimpl.
    rewrite H1;rewrite Pplus_comm.
    rewrite pow_Pplus;simpl;Esimpl.
    add_push (P5 @ (tail l0));rrefl.
    rewrite IHP1;rewrite H1;rewrite Pplus_comm.
    rewrite pow_Pplus;simpl;rsimpl.
    add_push (P5 @ (tail l0));rrefl.
  rewrite H0;rsimpl.
  add_push (P3 @ (tail l)).
  rewrite H;rewrite Pplus_comm.
  rewrite IHP'2;rewrite pow_Pplus;rsimpl.
  add_push (P3 @ (tail l));rrefl.
 Qed.

 Lemma Psub_ok : forall P' P l, (P -- P')@l == P@l - P'@l.
 Proof.
  induction P';simpl;intros;Esimpl2;trivial.
  generalize P p l;clear P p l.
  induction P;simpl;intros.
  Esimpl2;apply (ARadd_sym ARth).
  assert (H := ZPminus_spec p p0);destruct (ZPminus p p0).
  rewrite H;Esimpl. rewrite IHP';rsimpl. 
  rewrite H;Esimpl. rewrite IHP';Esimpl.
  rewrite <- jump_Pplus;rewrite Pplus_comm;rrefl.
  rewrite H;Esimpl. rewrite IHP.
  rewrite <- jump_Pplus;rewrite Pplus_comm;rrefl.
  destruct p0;simpl.
  rewrite IHP2;simpl;rsimpl.
  rewrite IHP2;simpl.
  rewrite jump_Pdouble_minus_one;rsimpl.
  rewrite IHP';rsimpl. 
  destruct P;simpl. 
  repeat rewrite Popp_ok;Esimpl2;rsimpl;add_push [c];try rrefl.
  destruct p0;simpl;Esimpl2.
  rewrite IHP'2;simpl;rsimpl;add_push (P'1@l * (pow (hd 0 l) p));trivial.
  add_push (P @ (jump p0 (jump p0 (tail l))));rrefl.
  rewrite IHP'2;simpl;rewrite jump_Pdouble_minus_one;rsimpl.
  add_push (- (P'1 @ l * pow (hd 0 l) p));rrefl.
  rewrite IHP'2;rsimpl;add_push (P @ (tail l));rrefl.
  assert (H := ZPminus_spec p0 p);destruct (ZPminus p0 p);Esimpl2.
  rewrite IHP'1; rewrite IHP'2;rsimpl.
  add_push (P3 @ (tail l));rewrite H;rrefl.
   rewrite IHP'1; rewrite IHP'2;rsimpl;simpl;Esimpl.
  rewrite H;rewrite Pplus_comm.
  rewrite pow_Pplus;rsimpl.
  add_push (P3 @ (tail l));rrefl.
  assert (forall P k l, 
           (PsubX Psub P'1 k P) @ l == P@l + - P'1@l * pow (hd 0 l) k).
   induction P;simpl;intros.
   rewrite Popp_ok;rsimpl;apply (ARadd_sym ARth);trivial.
   destruct p2;simpl;rewrite Popp_ok;rsimpl.
   apply (ARadd_sym ARth);trivial.
   rewrite jump_Pdouble_minus_one;apply (ARadd_sym ARth);trivial.
   apply (ARadd_sym ARth);trivial.
    assert (H1 := ZPminus_spec p2 k);destruct (ZPminus p2 k);Esimpl2;rsimpl.
    rewrite IHP'1;rsimpl;add_push (P5 @ (tail l0));rewrite H1;rrefl.
    rewrite IHP'1;rewrite H1;rewrite Pplus_comm.
    rewrite pow_Pplus;simpl;Esimpl.
    add_push (P5 @ (tail l0));rrefl.
    rewrite IHP1;rewrite H1;rewrite Pplus_comm.
    rewrite pow_Pplus;simpl;rsimpl.
    add_push (P5 @ (tail l0));rrefl.
  rewrite H0;rsimpl.
  rewrite IHP'2;rsimpl;add_push (P3 @ (tail l)).
  rewrite H;rewrite Pplus_comm.
  rewrite pow_Pplus;rsimpl.
 Qed.
 
 Lemma PmulI_ok : 
  forall P', 
   (forall (P : Pol) (l : list R), (Pmul_aux P P') @ l == P @ l * P' @ l) ->
   forall (P : Pol) (p : positive) (l : list R),
    (PmulI Pmul_aux P' p P) @ l == P @ l * P' @ (jump p l).
 Proof.
  induction P;simpl;intros.
  Esimpl2;apply (ARmul_sym ARth).
  assert (H1 := ZPminus_spec p p0);destruct (ZPminus p p0);Esimpl2.
  rewrite H1; rewrite H;rrefl.
  rewrite H1; rewrite H.
  rewrite Pplus_comm.
  rewrite jump_Pplus;simpl;rrefl.
  rewrite H1;rewrite Pplus_comm.
  rewrite jump_Pplus;rewrite IHP;rrefl.
  destruct p0;Esimpl2.
  rewrite IHP1;rewrite IHP2;simpl;rsimpl.
  mul_push (pow (hd 0 l) p);rrefl.
  rewrite IHP1;rewrite IHP2;simpl;rsimpl.
  mul_push (pow (hd 0 l) p); rewrite jump_Pdouble_minus_one;rrefl.
  rewrite IHP1;simpl;rsimpl.
  mul_push (pow (hd 0 l) p).
  rewrite H;rrefl.
 Qed.

 Lemma Pmul_aux_ok : forall P' P l,(Pmul_aux P P')@l == P@l * P'@l.
 Proof.
  induction P';simpl;intros.
  Esimpl2;trivial.
  apply PmulI_ok;trivial.
  rewrite Padd_ok;Esimpl2.
  rewrite (PmulI_ok P'2 IHP'2). rewrite IHP'1. rrefl.
 Qed.

 Lemma Pmul_ok : forall P P' l, (P**P')@l == P@l * P'@l.
 Proof.
  destruct P;simpl;intros.
  Esimpl2;apply (ARmul_sym ARth).
  rewrite (PmulI_ok P (Pmul_aux_ok P)).
  apply (ARmul_sym ARth).
  rewrite Padd_ok; Esimpl2.
  rewrite (PmulI_ok P3 (Pmul_aux_ok P3));trivial.
  rewrite Pmul_aux_ok;mul_push (P' @ l).
  rewrite (ARmul_sym ARth (P' @ l));rrefl.
 Qed.


 Lemma mkZmon_ok: forall M j l,
   Mphi l (mkZmon j M) == Mphi l (zmon j M).
 intros M j l; case M; simpl; intros; rsimpl.
 Qed.

 Lemma Mphi_ok: forall P M l, 
    let (Q,R) := MFactor P M in
      P@l == Q@l + (Mphi l M) * (R@l).
 Proof.
 intros P; elim P; simpl; auto; clear P.
   intros c M l; case M; simpl; auto; try intro p; try intro m;
   try rewrite (morph0 CRmorph); rsimpl.

   intros i P Hrec M l; case M; simpl; clear M.
     rewrite (morph0 CRmorph); rsimpl.
     intros j M.
     case_eq ((i ?= j) Eq); intros He; simpl.
       rewrite (Pcompare_Eq_eq _ _ He).
       generalize (Hrec M (jump j l)); case (MFactor P M);
        simpl; intros P2 Q2 H; repeat rewrite mkPinj_ok; auto.
       generalize (Hrec (zmon (j -i) M) (jump i l)); 
       case (MFactor P (zmon (j -i) M)); simpl.
       intros P2 Q2 H; repeat rewrite mkPinj_ok; auto.
       rewrite  <- (Pplus_minus _ _ (ZC2 _ _ He)).
       rewrite Pplus_comm; rewrite jump_Pplus; auto.
       rewrite (morph0 CRmorph); rsimpl.
       intros P2 m; rewrite (morph0 CRmorph); rsimpl.

   intros P2 Hrec1 i Q2 Hrec2 M l; case M; simpl; auto.
   rewrite (morph0 CRmorph); rsimpl.
   intros j M1.
     generalize (Hrec1 (zmon j M1) l); 
     case (MFactor P2 (zmon j M1)).
     intros R1 S1 H1.
     generalize (Hrec2 (zmon_pred j M1) (List.tail l)); 
     case (MFactor Q2 (zmon_pred j M1)); simpl.
     intros R2 S2 H2; rewrite H1; rewrite H2.
     repeat rewrite mkPX_ok; simpl.
     rsimpl.  
     apply radd_ext; rsimpl.
     rewrite (ARadd_sym ARth); rsimpl.
     apply radd_ext; rsimpl.
     rewrite (ARadd_sym ARth); rsimpl.
     case j; simpl; auto; try intros j1; rsimpl.
     rewrite jump_Pdouble_minus_one; rsimpl.
   intros j M1.
     case_eq ((i ?= j) Eq); intros He; simpl.
       rewrite (Pcompare_Eq_eq _ _ He).
       generalize (Hrec1 (mkZmon xH M1) l); case (MFactor P2 (mkZmon xH M1));
        simpl; intros P3 Q3 H; repeat rewrite mkPinj_ok; auto.
       rewrite H; rewrite mkPX_ok; rsimpl.
       repeat (rewrite <-(ARadd_assoc ARth)).
       apply radd_ext; rsimpl.
       rewrite (ARadd_sym ARth); rsimpl.
       apply radd_ext; rsimpl.
       repeat (rewrite <-(ARmul_assoc ARth)).
       rewrite mkZmon_ok.
       apply rmul_ext; rsimpl.
       rewrite (ARmul_sym ARth); rsimpl.
       generalize (Hrec1 (vmon (j - i) M1) l); 
             case (MFactor P2 (vmon (j - i) M1));
        simpl; intros P3 Q3 H; repeat rewrite mkPinj_ok; auto.
       rewrite H; rsimpl; repeat rewrite mkPinj_ok; auto.
       rewrite mkPX_ok; rsimpl.
       repeat (rewrite <-(ARadd_assoc ARth)).
       apply radd_ext; rsimpl.
       rewrite (ARadd_sym ARth); rsimpl.
       apply radd_ext; rsimpl.
       repeat (rewrite <-(ARmul_assoc ARth)).
       apply rmul_ext; rsimpl.
       rewrite (ARmul_sym ARth); rsimpl.
       apply rmul_ext; rsimpl.
       rewrite <- pow_Pplus.
       rewrite (Pplus_minus _ _ (ZC2 _ _ He)); rsimpl.
       generalize (Hrec1 (mkZmon 1 M1) l); 
             case (MFactor P2 (mkZmon 1 M1));
        simpl; intros P3 Q3 H; repeat rewrite mkPinj_ok; auto.
       rewrite H; rsimpl.
       rewrite mkPX_ok; rsimpl.
       repeat (rewrite <-(ARadd_assoc ARth)).
       apply radd_ext; rsimpl.
       rewrite (ARadd_sym ARth); rsimpl.
       apply radd_ext; rsimpl.
       rewrite mkZmon_ok.
       repeat (rewrite <-(ARmul_assoc ARth)).
       apply rmul_ext; rsimpl.
       rewrite (ARmul_sym ARth); rsimpl.
       rewrite mkPX_ok; simpl; rsimpl.
       rewrite (morph0 CRmorph); rsimpl.
       repeat (rewrite <-(ARmul_assoc ARth)).
       rewrite (ARmul_sym ARth (Q3@l)); rsimpl.
       apply rmul_ext; rsimpl.
       rewrite <- pow_Pplus.
       rewrite (Pplus_minus _ _ He); rsimpl.
 Qed.


 Lemma POneSubst_ok: forall P1 M1 P2 P3 l,
    POneSubst P1 M1 P2 = Some P3 -> Mphi l M1 == P2@l -> P1@l == P3@l.
 intros P2 M1 P3 P4 l; unfold POneSubst.
 generalize (Mphi_ok P2 M1 l); case (MFactor P2 M1); simpl; auto.
 intros Q1 R1; case R1.
   intros c H; rewrite H.
   generalize (morph_eq CRmorph c cO);
        case (c ?=! cO); simpl; auto.
   intros H1 H2; rewrite H1; auto; rsimpl.
   discriminate.
   intros _ H1 H2; injection H1; intros; subst.
   rewrite H2; rsimpl.
   rewrite Padd_ok; rewrite Pmul_ok; rsimpl.
 intros i P5 H; rewrite H.
   intros HH H1; injection HH; intros; subst; rsimpl.
   rewrite Padd_ok; rewrite Pmul_ok; rewrite H1; rsimpl.
 intros i P5 P6 H1 H2 H3; rewrite H1; rewrite H3.
   injection H2; intros; subst; rsimpl.
   rewrite Padd_ok; rewrite Pmul_ok; rsimpl.
 Qed.


 Lemma PNSubst1_ok: forall n P1 M1 P2 l,
    Mphi l M1 == P2@l -> P1@l == (PNSubst1 P1 M1 P2 n)@l.
 Proof.
 intros n; elim n; simpl; auto.
   intros P2 M1 P3 l H.
   generalize (fun P4 => @POneSubst_ok P2 M1 P3 P4 l); 
   case (POneSubst P2 M1 P3); [idtac | intros; rsimpl].
   intros P4 Hrec; rewrite (Hrec P4); auto; rsimpl.
 intros n1 Hrec P2 M1 P3 l H.
   generalize (fun P4 => @POneSubst_ok P2 M1 P3 P4 l); 
   case (POneSubst P2 M1 P3); [idtac | intros; rsimpl].
   intros P4 Hrec1; rewrite (Hrec1 P4); auto; rsimpl.
 Qed.

 Lemma PNSubst_ok: forall n P1 M1 P2 l P3,
    PNSubst P1 M1 P2 n = Some P3 -> Mphi l M1 == P2@l -> P1@l == P3@l.
 Proof.
 intros n P2 M1 P3 l P4; unfold PNSubst.
 generalize (fun P4 => @POneSubst_ok P2 M1 P3 P4 l); 
 case (POneSubst P2 M1 P3); [idtac | intros; discriminate].
 intros P5 H1; case n; try (intros; discriminate). 
 intros n1 H2; injection H2; intros; subst.
 rewrite <- PNSubst1_ok; auto.
 Qed.

 Fixpoint MPcond (LM1: list (Mon * Pol)) (l: list R) {struct LM1} : Prop :=            
    match LM1 with 
     cons (M1,P2) LM2 =>  (Mphi l M1 == P2@l) /\ (MPcond LM2 l)
    | _ => True
    end.

 Lemma PSubstL1_ok: forall n LM1 P1 l,
    MPcond LM1 l ->  P1@l == (PSubstL1 P1 LM1 n)@l.
 Proof.
 intros n LM1; elim LM1; simpl; auto.
   intros; rsimpl.
 intros (M2,P2) LM2 Hrec P3 l [H H1].
 rewrite <- Hrec; auto.
 apply PNSubst1_ok; auto.
 Qed.

 Lemma PSubstL_ok: forall n LM1 P1 P2 l,
   PSubstL P1 LM1 n = Some P2 -> MPcond LM1 l ->  P1@l == P2@l.
 Proof.
 intros n LM1; elim LM1; simpl; auto.
   intros; discriminate.
 intros (M2,P2) LM2 Hrec P3 P4 l.
 generalize (PNSubst_ok n P3 M2 P2); case (PNSubst P3 M2 P2 n).
   intros P5 H0 H1 [H2 H3]; injection H1; intros; subst.
   rewrite <- PSubstL1_ok; auto.
 intros l1 H [H1 H2]; auto.
 Qed.

 Lemma PNSubstL_ok: forall m n LM1 P1 l,
    MPcond LM1 l ->  P1@l == (PNSubstL P1 LM1 m n)@l.
 Proof.
 intros m; elim m; simpl; auto.
   intros n LM1 P2 l H; generalize (fun P3 => @PSubstL_ok n LM1 P2 P3 l);
     case (PSubstL P2 LM1 n); intros; rsimpl; auto.
 intros m1 Hrec n LM1 P2 l H.
 generalize (fun P3 => @PSubstL_ok n LM1 P2 P3 l);
     case (PSubstL P2 LM1 n); intros; rsimpl; auto.
 rewrite <- Hrec; auto.
 Qed.

 (** Definition of polynomial expressions *)

 Inductive PExpr : Type :=
  | PEc : C -> PExpr
  | PEX : positive -> PExpr
  | PEadd : PExpr -> PExpr -> PExpr
  | PEsub : PExpr -> PExpr -> PExpr
  | PEmul : PExpr -> PExpr -> PExpr
  | PEopp : PExpr -> PExpr.

 (** normalisation towards polynomials *)
 
 Definition X := (PX P1 xH P0).

 Definition mkX j :=
  match j with
  | xH => X
  | xO j => Pinj (Pdouble_minus_one j) X
  | xI j => Pinj (xO j) X
  end.

 Fixpoint norm (pe:PExpr) : Pol :=
  match pe with
  | PEc c => Pc c
  | PEX j => mkX j
  | PEadd pe1 (PEopp pe2) => Psub (norm pe1) (norm pe2)
  | PEadd (PEopp pe1) pe2 => Psub (norm pe2) (norm pe1)
  | PEadd pe1 pe2 => Padd (norm pe1) (norm pe2)
  | PEsub pe1 pe2 => Psub (norm pe1) (norm pe2)
  | PEmul pe1 pe2 => Pmul (norm pe1) (norm pe2)
  | PEopp pe1 => Popp (norm pe1)
  end.

 (** evaluation of polynomial expressions towards R *)
 
 Fixpoint PEeval (l:list R) (pe:PExpr) {struct pe} : R :=
  match pe with
  | PEc c => phi c
  | PEX j => nth 0 j l
  | PEadd pe1 pe2 => (PEeval l pe1) + (PEeval l pe2)
  | PEsub pe1 pe2 => (PEeval l pe1) - (PEeval l pe2)
  | PEmul pe1 pe2 => (PEeval l pe1) * (PEeval l pe2)
  | PEopp pe1 => - (PEeval l pe1)
  end.

 (** Correctness proofs *)
 

 Lemma mkX_ok : forall p l, nth 0 p l == (mkX p) @ l.
 Proof.
  destruct p;simpl;intros;Esimpl;trivial.
  rewrite <-jump_tl;rewrite nth_jump;rrefl.
  rewrite <- nth_jump.
  rewrite nth_Pdouble_minus_one;rrefl.
 Qed.

 Lemma norm_PEopp : forall l pe,  (norm (PEopp pe))@l == -(norm pe)@l.
 Proof.
  intros;simpl;apply Popp_ok.
 Qed.

 Ltac Esimpl3 := 
  repeat match goal with
  | |- context [(?P1 ++ ?P2)@?l] => rewrite (Padd_ok P2 P1 l)
  | |- context [(?P1 -- ?P2)@?l] => rewrite (Psub_ok P2 P1 l)
  | |- context [(norm (PEopp ?pe))@?l] => rewrite (norm_PEopp l pe)
  end;Esimpl2;try rrefl;try apply (ARadd_sym ARth).

 Lemma norm_ok : forall l pe,  PEeval l pe == (norm pe)@l.
 Proof.
  induction pe;simpl;Esimpl3.
  apply mkX_ok.
  rewrite IHpe1;rewrite IHpe2; destruct pe1;destruct pe2;Esimpl3.
  rewrite IHpe1;rewrite IHpe2;rrefl.
  rewrite Pmul_ok;rewrite IHpe1;rewrite IHpe2;rrefl.
  rewrite IHpe;rrefl.
 Qed.

 Lemma ring_correct : forall l pe1 pe2, 
  ((norm pe1) ?== (norm pe2)) = true -> (PEeval l pe1) == (PEeval l pe2).
 Proof.
  intros l pe1 pe2 H.
  repeat rewrite norm_ok.
  apply  (Peq_ok (norm pe1) (norm pe2) H l).
 Qed.

(** Evaluation function avoiding parentheses *)
 Fixpoint mkmult (r:R) (lm:list R) {struct lm}: R :=
  match lm with
  | nil => r
  | cons h t => mkmult (r*h) t
  end.
 		       
 Definition mkadd_mult rP lm :=
  match lm with
  | nil => rP + 1
  | cons h t => rP + mkmult h t
  end.

 Fixpoint powl (i:positive) (x:R) (l:list R) {struct i}: list R :=
  match i with
  | xH => cons x l
  | xO i => powl i x (powl i x l)
  | xI i => powl i x (powl i x (cons x l))
  end.
			       
 Fixpoint add_mult_dev (rP:R) (P:Pol) (fv lm:list R) {struct P} : R :=
  (* rP + P@l * lm *)
  match P with
  | Pc c => if c ?=! cI then mkadd_mult rP (rev' lm) 
    else mkadd_mult rP (cons [c] (rev' lm))
  | Pinj j Q => add_mult_dev rP Q (jump j fv) lm
  | PX P i Q => 
     let rP := add_mult_dev rP P fv (powl i (hd 0 fv) lm) in
     if Q ?== P0 then rP else add_mult_dev rP Q (tail fv) lm
  end.
 
 Definition mkmult1 lm :=
  match lm with
  | nil => rI
  | cons h t => mkmult h t
  end.
    
 Fixpoint mult_dev (P:Pol) (fv lm : list R) {struct P} : R :=
  (* P@l * lm *)							      
  match P with
  | Pc c => if c ?=! cI then mkmult1 (rev' lm) else mkmult [c] (rev' lm)
  | Pinj j Q => mult_dev Q (jump j fv) lm
  | PX P i Q => 
     let rP := mult_dev P fv (powl i (hd 0 fv) lm) in
     if Q ?== P0 then rP else add_mult_dev rP Q (tail fv) lm
  end. 

 Definition Pphi_dev fv P := mult_dev P fv nil.

 Add Morphism mkmult : mkmult_ext.
  intros r r0 eqr l;generalize l r r0 eqr;clear l r r0 eqr;
   induction l;simpl;intros.
  trivial. apply IHl; rewrite eqr;rrefl.
 Qed.

 Lemma mul_mkmult : forall lm r1 r2, r1 * mkmult r2 lm == mkmult (r1*r2) lm.
 Proof.
  induction lm;simpl;intros;try rrefl.
  rewrite IHlm.
  setoid_replace (r1 * (r2 * a)) with (r1 * r2 * a);Esimpl.
 Qed.

 Lemma mkmult1_mkmult : forall lm r, r * mkmult1 lm == mkmult r lm.
 Proof.
  destruct lm;simpl;intros. Esimpl.
  apply mul_mkmult.
 Qed.
 
 Lemma mkmult1_mkmult_1 : forall lm, mkmult1 lm == mkmult 1 lm.
 Proof.
  intros;rewrite <- mkmult1_mkmult;Esimpl.
 Qed.

 Lemma mkmult_rev_append : forall lm l r,
  mkmult r (rev_append lm l) == mkmult (mkmult r l) lm.
 Proof.
 induction lm; simpl in |- *; intros.
 rrefl.
 rewrite IHlm; simpl in |- *.
   repeat rewrite <- (ARmul_sym ARth a); rewrite <- mul_mkmult.
   rrefl.
 Qed.

 Lemma powl_mkmult_rev : forall p r x lm,
  mkmult r (rev' (powl p x lm)) == mkmult (pow x p * r) (rev' lm).
 Proof.
  induction p;simpl;intros.
  repeat rewrite IHp.
  unfold rev';simpl.
  repeat rewrite mkmult_rev_append.
  simpl.
  setoid_replace (pow x p * (pow x p * r) * x) 
    with (x * pow x p * pow x p * r);Esimpl.
  mul_push x;rrefl.
  repeat rewrite IHp.
  setoid_replace (pow x p * (pow x p * r) ) 
    with (pow x p * pow x p * r);Esimpl.
  unfold rev';simpl. repeat rewrite mkmult_rev_append;simpl.
  rewrite (ARmul_sym ARth);rrefl.
 Qed.

 Lemma Pphi_add_mult_dev : forall P rP fv lm, 
    rP + P@fv * mkmult1 (rev' lm) == add_mult_dev rP P fv lm.
 Proof.
  induction P;simpl;intros.
  assert (H := (morph_eq CRmorph) c cI).
   destruct (c ?=! cI).
    rewrite (H (refl_equal true));rewrite (morph1 CRmorph);Esimpl.
    destruct (rev' lm);Esimpl;rrefl.
    rewrite mkmult1_mkmult;rrefl.
   apply IHP.
   replace (match P3 with
       | Pc c => c ?=! cO
       | Pinj _ _ => false
       | PX _ _ _ => false
       end) with (Peq P3 P0);trivial.
   assert (H := Peq_ok P3 P0).
    destruct (P3 ?== P0).
    rewrite (H (refl_equal true));simpl;Esimpl.
   rewrite <- IHP1.
     repeat rewrite mkmult1_mkmult_1.
     rewrite powl_mkmult_rev.
     rewrite <- mul_mkmult;Esimpl.
   rewrite <- IHP2.
   rewrite <- IHP1.
     repeat rewrite mkmult1_mkmult_1.
     rewrite powl_mkmult_rev.
     rewrite <- mul_mkmult;Esimpl.
 Qed.
                                     
 Lemma Pphi_mult_dev : forall P fv lm,
	 P@fv * mkmult1 (rev' lm) == mult_dev P fv lm.
 Proof.
  induction P;simpl;intros.
   assert (H := (morph_eq CRmorph) c cI).
   destruct (c ?=! cI).
    rewrite (H (refl_equal true));rewrite (morph1 CRmorph);Esimpl.
    apply  mkmult1_mkmult.
   apply IHP.
   replace (match P3 with
       | Pc c => c ?=! cO
       | Pinj _ _ => false
       | PX _ _ _ => false
       end) with (Peq P3 P0);trivial.
   assert (H := Peq_ok P3 P0).
   destruct (P3 ?== P0).
   rewrite (H (refl_equal true));simpl;Esimpl.
   rewrite <- IHP1.
     repeat rewrite mkmult1_mkmult_1.
     rewrite powl_mkmult_rev.
     rewrite <- mul_mkmult;Esimpl.
   rewrite <- Pphi_add_mult_dev.
   rewrite <- IHP1.
     repeat rewrite mkmult1_mkmult_1.
     rewrite powl_mkmult_rev.
     rewrite <- mul_mkmult;Esimpl.
 Qed.

 Lemma Pphi_Pphi_dev :  forall P l,  P@l == Pphi_dev l P.
 Proof. 		
  unfold Pphi_dev;intros.
  rewrite <- Pphi_mult_dev;simpl;Esimpl.
 Qed.

 Lemma Pphi_dev_gen_ok :  forall l pe,  PEeval l pe == Pphi_dev l (norm pe).
 Proof.
  intros l pe;rewrite <- Pphi_Pphi_dev;apply norm_ok.
 Qed.

 Lemma Pphi_dev_ok :
   forall l pe npe, norm pe = npe -> PEeval l pe == Pphi_dev l npe.
 Proof.
  intros l pe npe npe_eq; subst npe; apply Pphi_dev_gen_ok.
 Qed. 

 Fixpoint MPcond_dev (LM1: list (Mon * Pol)) (l: list R) {struct LM1} : Prop :=            
    match LM1 with 
     cons (M1,P2) LM2 =>  (Mphi l M1 == Pphi_dev l P2) /\ (MPcond_dev LM2 l)
    | _ => True
    end.

 Fixpoint MPcond_map (LM1: list (Mon * PExpr)): list (Mon * Pol) :=            
    match LM1 with 
     cons (M1,P2) LM2 =>  cons (M1, norm P2) (MPcond_map LM2)
    | _ => nil
    end.

 Lemma MP_cond_dev_imp_MP_cond: forall LM1 l,
     MPcond_dev LM1 l -> MPcond LM1 l.
 Proof.
 intros LM1; elim LM1; simpl; auto.
 intros (M2,P2) LM2 Hrec l [H1 H2]; split; auto.
 rewrite H1; rewrite Pphi_Pphi_dev; rsimpl. 
 Qed.

 Lemma PNSubstL_dev_ok: forall m n lm pe l,
    let LM :=  MPcond_map lm in
    MPcond_dev LM l -> PEeval l pe == Pphi_dev l (PNSubstL (norm pe) LM m n).
 intros m n lm p3 l LM H.
 rewrite <- Pphi_Pphi_dev; rewrite <- PNSubstL_ok; auto.
   apply MP_cond_dev_imp_MP_cond; auto.
 rewrite Pphi_Pphi_dev; apply Pphi_dev_ok; auto.
 Qed.

End MakeRingPol. 
