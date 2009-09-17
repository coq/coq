(************************************************************************)
(*  V      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Set Implicit Arguments.
Require Import Setoid.
Require Import BinList.
Require Import BinPos.
Require Import BinNat.
Require Import BinInt.
Require Export Ring_theory.

Open Local Scope positive_scope.
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

  (* Power coefficients *)
 Variable Cpow : Set.
 Variable Cp_phi : N -> Cpow.
 Variable rpow : R -> Cpow -> R.
 Variable pow_th : power_theory rI rmul req Cp_phi rpow.

 (* division is ok *)
 Variable cdiv: C -> C -> C * C.
 Variable div_th: div_theory req cadd cmul phi cdiv.


 (* R notations *)
 Notation "0" := rO. Notation "1" := rI.
 Notation "x + y" := (radd x y).  Notation "x * y " := (rmul x y).
 Notation "x - y " := (rsub x y). Notation "- x" := (ropp x).
 Notation "x == y" := (req x y).

 (* C notations *)
 Notation "x +! y" := (cadd x y). Notation "x *! y " := (cmul x y).
 Notation "x -! y " := (csub x y). Notation "-! x" := (copp x).
 Notation " x ?=! y" := (ceqb x y). Notation "[ x ]" := (phi x).

 (* Useful tactics *)
  Add Setoid R req Rsth as R_set1.
 Ltac rrefl := gen_reflexivity Rsth.
  Add Morphism radd : radd_ext.  exact (Radd_ext Reqe). Qed.
  Add Morphism rmul : rmul_ext.  exact (Rmul_ext Reqe). Qed.
  Add Morphism ropp : ropp_ext.  exact (Ropp_ext Reqe). Qed.
  Add Morphism rsub : rsub_ext. exact (ARsub_ext Rsth Reqe ARth). Qed.
 Ltac rsimpl := gen_srewrite Rsth Reqe ARth.
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

 Definition mkPinj_pred j P:=
  match j with
  | xH => P
  | xO j => Pinj (Pdouble_minus_one j) P
  | xI j => Pinj (xO j) P
  end.

 Definition mkPX P i Q :=
  match P with
  | Pc c => if c ?=! cO then mkPinj xH Q else PX P i Q
  | Pinj _ _ => PX P i Q
  | PX P' i' Q' => if Q' ?== P0 then PX P' (i' + i) Q else PX P i Q
  end.

 Definition mkXi i := PX P1 i P0.

 Definition mkX := mkXi 1.

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
(* A symmetric version of the multiplication *)

 Fixpoint Pmul (P P'' : Pol) {struct P''} : Pol :=
   match P'' with
   | Pc c => PmulC P c
   | Pinj j' Q' => PmulI Pmul Q' j' P
   | PX P' i' Q' =>
     match P with
     | Pc c => PmulC P'' c
     | Pinj j Q =>
       let QQ' :=
         match j with
         | xH => Pmul Q Q'
         | xO j => Pmul (Pinj (Pdouble_minus_one j) Q) Q'
         | xI j => Pmul (Pinj (xO j) Q) Q'
         end in
       mkPX (Pmul P P') i' QQ'
     | PX P i Q=>
       let QQ' := Pmul Q Q' in
       let PQ' := PmulI Pmul Q' xH P in
       let QP' := Pmul (mkPinj xH Q) P' in
       let PP' := Pmul P P' in
       (mkPX (mkPX PP' i P0 ++ QP') i' P0) ++ mkPX PQ' i QQ'
     end
  end.

(* Non symmetric *)
(*
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
    (mkPX (Pmul_aux P P') i P0) ++ (PmulI Pmul_aux Q xH P')
  end.
*)
 Notation "P ** P'" := (Pmul P P').

 Fixpoint Psquare (P:Pol) : Pol :=
   match P with
   | Pc c => Pc (c *! c)
   | Pinj j Q => Pinj j (Psquare Q)
   | PX P i Q =>
     let twoPQ := Pmul P (mkPinj xH (PmulC Q (cI +! cI))) in
     let Q2 := Psquare Q in
     let P2 := Psquare P in
     mkPX (mkPX P2 i P0 ++ twoPQ) i Q2
   end.

 (** Monomial **)

  Inductive Mon: Set :=
    mon0: Mon
  | zmon: positive -> Mon -> Mon
  | vmon: positive -> Mon -> Mon.

 Fixpoint Mphi(l:list R) (M: Mon) {struct M} : R :=
  match M with
     mon0 => rI
  | zmon j M1  => Mphi (jump j l) M1
  | vmon i M1 =>
     let x := hd 0 l in
     let xi := pow_pos rmul x i in
    (Mphi (tail l) M1) * xi
  end.

 Definition mkZmon j M :=
   match M with mon0 => mon0 | _ => zmon j M end.

 Definition zmon_pred j M :=
   match j with xH => M | _ => mkZmon (Ppred j) M end.

 Definition mkVmon i M :=
   match M with
   | mon0 => vmon i mon0
   | zmon j m => vmon i (zmon_pred j m)
   | vmon i' m => vmon (i+i') m
   end.

 Fixpoint CFactor (P: Pol) (c: C) {struct P}: Pol * Pol :=
   match P with
   | Pc c1   => let (q,r) := cdiv c1 c in (Pc r, Pc q)
   | Pinj j1 P1  =>
     let (R,S) := CFactor P1 c in
            (mkPinj j1 R, mkPinj j1 S)
  | PX P1 i Q1 =>
     let (R1, S1) := CFactor P1 c in
     let (R2, S2) := CFactor Q1 c in
        (mkPX R1 i R2, mkPX S1 i S2)
   end.

 Fixpoint MFactor (P: Pol) (c: C) (M: Mon) {struct P}: Pol * Pol :=
   match P, M with
        _, mon0 =>
            if (ceqb c cI) then (Pc cO, P) else
(*            if (ceqb c (copp cI)) then (Pc cO, Popp P) else  Not in almost ring *)
            CFactor P c
   | Pc _, _    => (P, Pc cO)
   | Pinj j1 P1, zmon j2 M1 =>
      match (j1 ?= j2) Eq with
        Eq => let (R,S) := MFactor P1 c M1 in
                 (mkPinj j1 R, mkPinj j1 S)
      | Lt => let (R,S) := MFactor P1 c (zmon (j2 - j1) M1) in
                 (mkPinj j1 R, mkPinj j1 S)
      | Gt => (P, Pc cO)
      end
  | Pinj _ _, vmon _ _ => (P, Pc cO)
  | PX P1 i Q1, zmon j M1 =>
             let M2 := zmon_pred j M1 in
             let (R1, S1) := MFactor P1 c M in
             let (R2, S2) := MFactor Q1 c M2 in
               (mkPX R1 i R2, mkPX S1 i S2)
  | PX P1 i Q1, vmon j M1 =>
      match (i ?= j) Eq with
        Eq => let (R1,S1) := MFactor P1 c (mkZmon xH M1) in
                 (mkPX R1 i Q1, S1)
      | Lt => let (R1,S1) := MFactor P1 c (vmon (j - i) M1) in
                 (mkPX R1 i Q1, S1)
      | Gt => let (R1,S1) := MFactor P1 c (mkZmon xH M1) in
                 (mkPX R1 i Q1, mkPX S1 (i-j) (Pc cO))
      end
   end.

  Definition POneSubst (P1: Pol) (cM1: C * Mon) (P2: Pol): option Pol :=
    let (c,M1) := cM1 in
    let (Q1,R1) := MFactor P1 c M1 in
    match R1 with
     (Pc c) => if c ?=! cO then None
               else Some (Padd Q1 (Pmul P2 R1))
    | _ => Some (Padd Q1 (Pmul P2 R1))
    end.

  Fixpoint PNSubst1 (P1: Pol) (cM1: C * Mon) (P2: Pol) (n: nat) {struct n}: Pol :=
    match POneSubst P1 cM1 P2 with
     Some P3 => match n with S n1 => PNSubst1 P3 cM1 P2 n1 | _ => P3 end
    | _ => P1
    end.

  Definition PNSubst (P1: Pol) (cM1: C * Mon) (P2: Pol) (n: nat): option Pol :=
    match POneSubst P1 cM1 P2 with
     Some P3 => match n with S n1 => Some (PNSubst1 P3 cM1 P2 n1) | _ => None end
    | _ => None
    end.

  Fixpoint PSubstL1 (P1: Pol) (LM1: list ((C * Mon) * Pol)) (n: nat) {struct LM1}:
     Pol :=
    match LM1 with
     cons (M1,P2) LM2 => PSubstL1 (PNSubst1 P1 M1 P2 n) LM2 n
    | _ => P1
    end.

  Fixpoint PSubstL (P1: Pol) (LM1: list ((C * Mon) * Pol)) (n: nat) {struct LM1}: option Pol :=
    match LM1 with
     cons (M1,P2) LM2 =>
      match PNSubst P1 M1 P2 n with
        Some P3 => Some (PSubstL1 P3 LM2 n)
     |  None => PSubstL P1 LM2 n
     end
    | _ => None
    end.

  Fixpoint PNSubstL (P1: Pol) (LM1: list ((C * Mon) * Pol)) (m n: nat) {struct m}: Pol :=
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
     let xi := pow_pos rmul x i in
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

 Let pow_pos_Pplus :=
    pow_pos_Pplus rmul Rsth Reqe.(Rmul_ext) ARth.(ARmul_comm) ARth.(ARmul_assoc).

 Lemma mkPX_ok : forall l P i Q,
  (mkPX P i Q)@l == P@l*(pow_pos rmul (hd 0 l) i) + Q@(tail l).
 Proof.
  intros l P i Q;unfold mkPX.
  destruct P;try (simpl;rrefl).
  assert (H := morph_eq CRmorph c cO);destruct (c ?=! cO);simpl;try rrefl.
  rewrite (H (refl_equal true));rewrite (morph0 CRmorph).
  rewrite mkPinj_ok;rsimpl;simpl;rrefl.
  assert (H := @Peq_ok P3 P0);destruct (P3 ?== P0);simpl;try rrefl.
  rewrite (H (refl_equal true));trivial.
  rewrite Pphi0.  rewrite pow_pos_Pplus;rsimpl.
 Qed.

 Ltac Esimpl :=
  repeat (progress (
   match goal with
   | |- context [?P@?l] =>
       match P with
       | P0 => rewrite (Pphi0 l)
       | P1 => rewrite (Pphi1 l)
       | (mkPinj ?j ?P) => rewrite (mkPinj_ok j l P)
       | (mkPX ?P ?i ?Q) => rewrite (mkPX_ok l P i Q)
       end
   | |- context [[?c]] =>
       match c with
       | cO => rewrite (morph0 CRmorph)
       | cI => rewrite (morph1 CRmorph)
       | ?x +! ?y => rewrite ((morph_add CRmorph) x y)
       | ?x *! ?y => rewrite ((morph_mul CRmorph) x y)
       | ?x -! ?y => rewrite ((morph_sub CRmorph) x y)
       | -! ?x => rewrite ((morph_opp CRmorph) x)
       end
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
  Esimpl2;apply (ARadd_comm ARth).
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
  rsimpl;add_push (P'1@l * (pow_pos rmul (hd 0 l) p));rrefl.
  rewrite IHP'2;simpl.
  rewrite jump_Pdouble_minus_one;rsimpl;add_push (P'1@l * (pow_pos rmul (hd 0 l) p));rrefl.
  rewrite IHP'2;rsimpl. add_push (P @ (tail l));rrefl.
  assert (H := ZPminus_spec p0 p);destruct (ZPminus p0 p);Esimpl2.
  rewrite IHP'1;rewrite IHP'2;rsimpl.
  add_push (P3 @ (tail l));rewrite H;rrefl.
  rewrite IHP'1;rewrite IHP'2;simpl;Esimpl.
  rewrite H;rewrite Pplus_comm.
  rewrite pow_pos_Pplus;rsimpl.
  add_push (P3 @ (tail l));rrefl.
  assert (forall P k l,
           (PaddX Padd P'1 k P) @ l == P@l + P'1@l * pow_pos rmul (hd 0 l) k).
   induction P;simpl;intros;try apply (ARadd_comm ARth).
   destruct p2;simpl;try apply (ARadd_comm ARth).
   rewrite jump_Pdouble_minus_one;apply (ARadd_comm ARth).
    assert (H1 := ZPminus_spec p2 k);destruct (ZPminus p2 k);Esimpl2.
    rewrite IHP'1;rsimpl; rewrite H1;add_push (P5 @ (tail l0));rrefl.
    rewrite IHP'1;simpl;Esimpl.
    rewrite H1;rewrite Pplus_comm.
    rewrite pow_pos_Pplus;simpl;Esimpl.
    add_push (P5 @ (tail l0));rrefl.
    rewrite IHP1;rewrite H1;rewrite Pplus_comm.
    rewrite pow_pos_Pplus;simpl;rsimpl.
    add_push (P5 @ (tail l0));rrefl.
  rewrite H0;rsimpl.
  add_push (P3 @ (tail l)).
  rewrite H;rewrite Pplus_comm.
  rewrite IHP'2;rewrite pow_pos_Pplus;rsimpl.
  add_push (P3 @ (tail l));rrefl.
 Qed.

 Lemma Psub_ok : forall P' P l, (P -- P')@l == P@l - P'@l.
 Proof.
  induction P';simpl;intros;Esimpl2;trivial.
  generalize P p l;clear P p l.
  induction P;simpl;intros.
  Esimpl2;apply (ARadd_comm ARth).
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
  rewrite IHP'2;simpl;rsimpl;add_push (P'1@l * (pow_pos rmul (hd 0 l) p));trivial.
  add_push (P @ (jump p0 (jump p0 (tail l))));rrefl.
  rewrite IHP'2;simpl;rewrite jump_Pdouble_minus_one;rsimpl.
  add_push (- (P'1 @ l * pow_pos  rmul (hd 0 l) p));rrefl.
  rewrite IHP'2;rsimpl;add_push (P @ (tail l));rrefl.
  assert (H := ZPminus_spec p0 p);destruct (ZPminus p0 p);Esimpl2.
  rewrite IHP'1; rewrite IHP'2;rsimpl.
  add_push (P3 @ (tail l));rewrite H;rrefl.
   rewrite IHP'1; rewrite IHP'2;rsimpl;simpl;Esimpl.
  rewrite H;rewrite Pplus_comm.
  rewrite pow_pos_Pplus;rsimpl.
  add_push (P3 @ (tail l));rrefl.
  assert (forall P k l,
           (PsubX Psub P'1 k P) @ l == P@l + - P'1@l * pow_pos rmul (hd 0 l) k).
   induction P;simpl;intros.
   rewrite Popp_ok;rsimpl;apply (ARadd_comm ARth);trivial.
   destruct p2;simpl;rewrite Popp_ok;rsimpl.
   apply (ARadd_comm ARth);trivial.
   rewrite jump_Pdouble_minus_one;apply (ARadd_comm ARth);trivial.
   apply (ARadd_comm ARth);trivial.
    assert (H1 := ZPminus_spec p2 k);destruct (ZPminus p2 k);Esimpl2;rsimpl.
    rewrite IHP'1;rsimpl;add_push (P5 @ (tail l0));rewrite H1;rrefl.
    rewrite IHP'1;rewrite H1;rewrite Pplus_comm.
    rewrite pow_pos_Pplus;simpl;Esimpl.
    add_push (P5 @ (tail l0));rrefl.
    rewrite IHP1;rewrite H1;rewrite Pplus_comm.
    rewrite pow_pos_Pplus;simpl;rsimpl.
    add_push (P5 @ (tail l0));rrefl.
  rewrite H0;rsimpl.
  rewrite IHP'2;rsimpl;add_push (P3 @ (tail l)).
  rewrite H;rewrite Pplus_comm.
  rewrite pow_pos_Pplus;rsimpl.
 Qed.
(* Proof for the symmetriv version *)

 Lemma PmulI_ok :
  forall P',
   (forall (P : Pol) (l : list R), (Pmul P P') @ l == P @ l * P' @ l) ->
   forall (P : Pol) (p : positive) (l : list R),
    (PmulI Pmul P' p P) @ l == P @ l * P' @ (jump p l).
 Proof.
  induction P;simpl;intros.
  Esimpl2;apply (ARmul_comm ARth).
  assert (H1 := ZPminus_spec p p0);destruct (ZPminus p p0);Esimpl2.
  rewrite H1; rewrite H;rrefl.
  rewrite H1; rewrite H.
  rewrite Pplus_comm.
  rewrite jump_Pplus;simpl;rrefl.
  rewrite H1;rewrite Pplus_comm.
  rewrite jump_Pplus;rewrite IHP;rrefl.
  destruct p0;Esimpl2.
  rewrite IHP1;rewrite IHP2;simpl;rsimpl.
  mul_push (pow_pos rmul (hd 0 l) p);rrefl.
  rewrite IHP1;rewrite IHP2;simpl;rsimpl.
  mul_push (pow_pos rmul (hd 0 l) p); rewrite jump_Pdouble_minus_one;rrefl.
  rewrite IHP1;simpl;rsimpl.
  mul_push (pow_pos rmul (hd 0 l) p).
  rewrite H;rrefl.
 Qed.

(*
 Lemma PmulI_ok :
  forall P',
   (forall (P : Pol) (l : list R), (Pmul_aux P P') @ l == P @ l * P' @ l) ->
   forall (P : Pol) (p : positive) (l : list R),
    (PmulI Pmul_aux P' p P) @ l == P @ l * P' @ (jump p l).
 Proof.
  induction P;simpl;intros.
  Esimpl2;apply (ARmul_comm ARth).
  assert (H1 := ZPminus_spec p p0);destruct (ZPminus p p0);Esimpl2.
  rewrite H1; rewrite H;rrefl.
  rewrite H1; rewrite H.
  rewrite Pplus_comm.
  rewrite jump_Pplus;simpl;rrefl.
  rewrite H1;rewrite Pplus_comm.
  rewrite jump_Pplus;rewrite IHP;rrefl.
  destruct p0;Esimpl2.
  rewrite IHP1;rewrite IHP2;simpl;rsimpl.
  mul_push (pow_pos rmul (hd 0 l) p);rrefl.
  rewrite IHP1;rewrite IHP2;simpl;rsimpl.
  mul_push (pow_pos rmul (hd 0 l) p); rewrite jump_Pdouble_minus_one;rrefl.
  rewrite IHP1;simpl;rsimpl.
  mul_push (pow_pos rmul (hd 0 l) p).
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
*)

(* Proof for the symmetric version *)
 Lemma Pmul_ok : forall P P' l, (P**P')@l == P@l * P'@l.
 Proof.
  intros P P';generalize P;clear P;induction P';simpl;intros.
  apply PmulC_ok. apply PmulI_ok;trivial.
  destruct P.
  rewrite (ARmul_comm ARth);Esimpl2;Esimpl2.
  Esimpl2. rewrite IHP'1;Esimpl2.
   assert (match p0 with
           | xI j => Pinj (xO j) P ** P'2
           | xO j => Pinj (Pdouble_minus_one j) P ** P'2
           | 1 => P ** P'2
           end @ (tail l) == P @ (jump p0 l) * P'2 @ (tail l)).
   destruct p0;simpl;rewrite IHP'2;Esimpl.
   rewrite jump_Pdouble_minus_one;Esimpl.
   rewrite H;Esimpl.
   rewrite Padd_ok; Esimpl2. rewrite Padd_ok; Esimpl2.
   repeat (rewrite IHP'1 || rewrite IHP'2);simpl.
   rewrite PmulI_ok;trivial.
   mul_push (P'1@l). simpl. mul_push (P'2 @ (tail l)). Esimpl.
 Qed.

(*
Lemma Pmul_ok : forall P P' l, (P**P')@l == P@l * P'@l.
 Proof.
  destruct P;simpl;intros.
  Esimpl2;apply (ARmul_comm ARth).
  rewrite (PmulI_ok P (Pmul_aux_ok P)).
  apply (ARmul_comm ARth).
  rewrite Padd_ok; Esimpl2.
  rewrite (PmulI_ok P3 (Pmul_aux_ok P3));trivial.
  rewrite Pmul_aux_ok;mul_push (P' @ l).
  rewrite (ARmul_comm ARth (P' @ l));rrefl.
 Qed.
*)

 Lemma Psquare_ok : forall P l, (Psquare P)@l == P@l * P@l.
 Proof.
  induction P;simpl;intros;Esimpl2.
  apply IHP. rewrite Padd_ok. rewrite Pmul_ok;Esimpl2.
  rewrite IHP1;rewrite IHP2.
  mul_push (pow_pos rmul (hd 0 l) p). mul_push (P2@l).
  rrefl.
 Qed.


 Lemma mkZmon_ok: forall M j l,
   Mphi l (mkZmon j M) == Mphi l (zmon j M).
 intros M j l; case M; simpl; intros; rsimpl.
 Qed.

 Lemma zmon_pred_ok : forall M j l,
    Mphi (tail l) (zmon_pred j M) == Mphi l (zmon j M).
 Proof.
   destruct j; simpl;intros auto; rsimpl.
   rewrite mkZmon_ok;rsimpl.
   rewrite mkZmon_ok;simpl. rewrite jump_Pdouble_minus_one; rsimpl.
 Qed.

 Lemma mkVmon_ok : forall M i l, Mphi l (mkVmon i M) == Mphi l M*pow_pos rmul (hd 0 l) i.
 Proof.
  destruct M;simpl;intros;rsimpl.
   rewrite zmon_pred_ok;simpl;rsimpl.
  rewrite Pplus_comm;rewrite pow_pos_Pplus;rsimpl.
 Qed.

 Lemma Mcphi_ok: forall P c l,
    let (Q,R) := CFactor P c in
      P@l == Q@l + (phi c) * (R@l).
 Proof.
 intros P; elim P; simpl; auto; clear P.
   intros c c1 l; generalize (div_th.(div_eucl_th) c c1); case cdiv.
   intros q r H; rewrite H.
   Esimpl.
   rewrite (ARadd_comm ARth); rsimpl.
 intros i P Hrec c l.
  generalize (Hrec c (jump i l)); case CFactor.
  intros R1 S1; Esimpl; auto.
 intros Q1 Qrec i R1 Rrec c l.
   generalize (Qrec c l); case CFactor; intros S1 S2 HS.
   generalize (Rrec c (tail l)); case CFactor; intros S3 S4 HS1.
   rewrite HS; rewrite HS1; Esimpl.
   apply (Radd_ext Reqe); rsimpl.
   repeat rewrite <- (ARadd_assoc ARth).
   apply (Radd_ext Reqe); rsimpl.
   rewrite (ARadd_comm ARth); rsimpl.
 Qed.

 Lemma Mphi_ok: forall P (cM: C * Mon) l,
    let (c,M) := cM in
    let (Q,R) := MFactor P c M in
      P@l == Q@l + (phi c) * (Mphi l M) * (R@l).
 Proof.
 intros P; elim P; simpl; auto; clear P.
   intros c (c1, M) l; case M; simpl; auto.
   assert (H1:= morph_eq CRmorph c1 cI);destruct (c1 ?=! cI).
   rewrite (H1 (refl_equal true));Esimpl.
    try rewrite (morph0 CRmorph); rsimpl.
   generalize (div_th.(div_eucl_th) c c1); case (cdiv c c1).
   intros q r H; rewrite H; clear H H1.
   Esimpl.
   rewrite (ARadd_comm ARth); rsimpl.
   intros p m; Esimpl.
   intros p m; Esimpl.
   intros i P Hrec (c,M) l; case M; simpl; clear M.
     assert (H1:= morph_eq CRmorph c cI);destruct (c ?=! cI).
     rewrite (H1 (refl_equal true));Esimpl.
     Esimpl.
   generalize (Mcphi_ok P c (jump i l)); case CFactor.
   intros R1 Q1 HH; rewrite HH; Esimpl.
     intros j M.
     case_eq ((i ?= j) Eq); intros He; simpl.
       rewrite (Pcompare_Eq_eq _ _ He).
       generalize (Hrec (c, M) (jump j l)); case (MFactor P c M);
        simpl; intros P2 Q2 H; repeat rewrite mkPinj_ok; auto.
       generalize (Hrec (c, (zmon (j -i) M)) (jump i l));
       case (MFactor P c (zmon (j -i) M)); simpl.
       intros P2 Q2 H; repeat rewrite mkPinj_ok; auto.
       rewrite  <- (Pplus_minus _ _ (ZC2 _ _ He)).
       rewrite Pplus_comm; rewrite jump_Pplus; auto.
       rewrite (morph0 CRmorph); rsimpl.
       intros P2 m; rewrite (morph0 CRmorph); rsimpl.

   intros P2 Hrec1 i Q2 Hrec2 (c, M) l; case M; simpl; auto.
     assert (H1:= morph_eq CRmorph c cI);destruct (c ?=! cI).
     rewrite (H1 (refl_equal true));Esimpl.
     Esimpl.
    generalize (Mcphi_ok P2 c l); case CFactor.
    intros S1 S2 HS.
    generalize (Mcphi_ok Q2 c (tail l)); case CFactor.
    intros S3 S4 HS1; Esimpl; rewrite HS; rewrite HS1.
    rsimpl.
    apply (Radd_ext Reqe); rsimpl.
    repeat rewrite <- (ARadd_assoc ARth).
    apply (Radd_ext Reqe); rsimpl.
    rewrite (ARadd_comm ARth); rsimpl.
   intros j M1.
     generalize (Hrec1 (c,zmon j M1) l);
     case (MFactor P2 c (zmon j M1)).
     intros R1 S1 H1.
     generalize (Hrec2 (c, zmon_pred j M1) (List.tail l));
     case (MFactor Q2 c (zmon_pred j M1)); simpl.
     intros R2 S2 H2; rewrite H1; rewrite H2.
     repeat rewrite mkPX_ok; simpl.
     rsimpl.
     apply radd_ext; rsimpl.
     rewrite (ARadd_comm ARth); rsimpl.
     apply radd_ext; rsimpl.
     rewrite (ARadd_comm ARth); rsimpl.
     rewrite zmon_pred_ok;rsimpl.
   intros j M1.
     case_eq ((i ?= j) Eq); intros He; simpl.
       rewrite (Pcompare_Eq_eq _ _ He).
       generalize (Hrec1 (c, mkZmon xH M1) l); case (MFactor P2 c (mkZmon xH M1));
        simpl; intros P3 Q3 H; repeat rewrite mkPinj_ok; auto.
       rewrite H; rewrite mkPX_ok; rsimpl.
       repeat (rewrite <-(ARadd_assoc ARth)).
       apply radd_ext; rsimpl.
       rewrite (ARadd_comm ARth); rsimpl.
       apply radd_ext; rsimpl.
       repeat (rewrite <-(ARmul_assoc ARth)).
       rewrite mkZmon_ok.
       apply rmul_ext; rsimpl.
       repeat (rewrite <-(ARmul_assoc ARth)).
       apply rmul_ext; rsimpl.
       rewrite (ARmul_comm ARth); rsimpl.
       generalize (Hrec1 (c, vmon (j - i) M1) l);
             case (MFactor P2 c (vmon (j - i) M1));
        simpl; intros P3 Q3 H; repeat rewrite mkPinj_ok; auto.
       rewrite H; rsimpl; repeat rewrite mkPinj_ok; auto.
       rewrite mkPX_ok; rsimpl.
       repeat (rewrite <-(ARadd_assoc ARth)).
       apply radd_ext; rsimpl.
       rewrite (ARadd_comm ARth); rsimpl.
       apply radd_ext; rsimpl.
       repeat (rewrite <-(ARmul_assoc ARth)).
       apply rmul_ext; rsimpl.
       rewrite (ARmul_comm ARth); rsimpl.
       apply rmul_ext; rsimpl.
       rewrite <- (ARmul_comm ARth (Mphi (tail l) M1)); rsimpl.
       repeat (rewrite <-(ARmul_assoc ARth)).
       apply rmul_ext; rsimpl.
       rewrite <- pow_pos_Pplus.
       rewrite (Pplus_minus _ _ (ZC2 _ _ He)); rsimpl.
       generalize (Hrec1 (c, mkZmon 1 M1) l);
             case (MFactor P2 c (mkZmon 1 M1));
        simpl; intros P3 Q3 H; repeat rewrite mkPinj_ok; auto.
       rewrite H; rsimpl.
       rewrite mkPX_ok; rsimpl.
       repeat (rewrite <-(ARadd_assoc ARth)).
       apply radd_ext; rsimpl.
       rewrite (ARadd_comm ARth); rsimpl.
       apply radd_ext; rsimpl.
       rewrite mkZmon_ok.
       repeat (rewrite <-(ARmul_assoc ARth)).
       apply rmul_ext; rsimpl.
       rewrite (ARmul_comm ARth); rsimpl.
       rewrite mkPX_ok; simpl; rsimpl.
       rewrite (morph0 CRmorph); rsimpl.
       repeat (rewrite <-(ARmul_assoc ARth)).
       rewrite (ARmul_comm ARth (Q3@l)); rsimpl.
       apply rmul_ext; rsimpl.
       rewrite (ARmul_comm ARth); rsimpl.
       repeat (rewrite <- (ARmul_assoc ARth)).
       apply rmul_ext; rsimpl.
       rewrite <- pow_pos_Pplus.
       rewrite (Pplus_minus _ _ He); rsimpl.
 Qed.

(* Proof for the symmetric version *)

 Lemma POneSubst_ok: forall P1 M1 P2 P3 l,
    POneSubst P1 M1 P2 = Some P3 -> phi (fst M1) * Mphi l (snd M1) == P2@l -> P1@l == P3@l.
 Proof.
 intros P2 (cc,M1) P3 P4 l; unfold POneSubst.
 generalize (Mphi_ok P2 (cc, M1) l); case (MFactor P2 cc M1); simpl; auto.
 intros Q1 R1; case R1.
   intros c H; rewrite H.
   generalize (morph_eq CRmorph c cO);
        case (c ?=! cO); simpl; auto.
   intros H1 H2; rewrite H1; auto; rsimpl.
   discriminate.
   intros _ H1 H2; injection H1; intros; subst.
   rewrite H2; rsimpl.
 (* new version *)
   rewrite Padd_ok; rewrite PmulC_ok; rsimpl.
 intros i P5 H; rewrite H.
   intros HH H1; injection HH; intros; subst; rsimpl.
   rewrite Padd_ok; rewrite PmulI_ok by (intros;apply Pmul_ok). rewrite H1; rsimpl.
 intros i P5 P6 H1 H2 H3; rewrite H1; rewrite H3.
   assert (P4 = Q1 ++ P3 ** PX i P5 P6).
   injection H2; intros; subst;trivial.
  rewrite H;rewrite Padd_ok;rewrite Pmul_ok;rsimpl.
 Qed.
(*
  Lemma POneSubst_ok: forall P1 M1 P2 P3 l,
    POneSubst P1 M1 P2 = Some P3 -> Mphi l M1 == P2@l -> P1@l == P3@l.
Proof.
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
   rewrite Padd_ok; rewrite Pmul_ok. rewrite H1; rsimpl.
   intros i P5 P6 H1 H2 H3; rewrite H1; rewrite H3.
   injection H2; intros; subst; rsimpl.
   rewrite Padd_ok.
   rewrite Pmul_ok; rsimpl.
 Qed.
*)
 Lemma PNSubst1_ok: forall n P1 M1 P2 l,
    [fst M1] * Mphi l (snd M1) == P2@l -> P1@l == (PNSubst1 P1 M1 P2 n)@l.
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
    PNSubst P1 M1 P2 n = Some P3 -> [fst M1] * Mphi l (snd M1) == P2@l -> P1@l == P3@l.
 Proof.
 intros n P2 (cc, M1) P3 l P4; unfold PNSubst.
 generalize (fun P4 => @POneSubst_ok P2 (cc,M1) P3 P4 l);
 case (POneSubst P2 (cc,M1) P3); [idtac | intros; discriminate].
 intros P5 H1; case n; try (intros; discriminate).
 intros n1 H2; injection H2; intros; subst.
 rewrite <- PNSubst1_ok; auto.
 Qed.

 Fixpoint MPcond (LM1: list (C * Mon * Pol)) (l: list R) {struct LM1} : Prop :=
    match LM1 with
     cons (M1,P2) LM2 =>  ([fst M1] * Mphi l (snd M1) == P2@l) /\ (MPcond LM2 l)
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
  | PEopp : PExpr -> PExpr
  | PEpow : PExpr -> N -> PExpr.

 (** evaluation of polynomial expressions towards R *)
 Definition mk_X j := mkPinj_pred j mkX.

 (** evaluation of polynomial expressions towards R *)

 Fixpoint PEeval (l:list R) (pe:PExpr) {struct pe} : R :=
   match pe with
   | PEc c => phi c
   | PEX j => nth 0 j l
   | PEadd pe1 pe2 => (PEeval l pe1) + (PEeval l pe2)
   | PEsub pe1 pe2 => (PEeval l pe1) - (PEeval l pe2)
   | PEmul pe1 pe2 => (PEeval l pe1) * (PEeval l pe2)
   | PEopp pe1 => - (PEeval l pe1)
   | PEpow pe1 n => rpow (PEeval l pe1) (Cp_phi n)
   end.

Strategy expand [PEeval].

 (** Correctness proofs *)

 Lemma mkX_ok : forall p l, nth 0 p l == (mk_X p) @ l.
 Proof.
  destruct p;simpl;intros;Esimpl;trivial.
  rewrite <-jump_tl;rewrite nth_jump;rrefl.
  rewrite <- nth_jump.
  rewrite nth_Pdouble_minus_one;rrefl.
 Qed.

 Ltac Esimpl3 :=
  repeat match goal with
  | |- context [(?P1 ++ ?P2)@?l] => rewrite (Padd_ok P2 P1 l)
  | |- context [(?P1 -- ?P2)@?l] => rewrite (Psub_ok P2 P1 l)
  end;Esimpl2;try rrefl;try apply (ARadd_comm ARth).

(* Power using the chinise algorithm *)
(*Section POWER.
  Variable subst_l : Pol -> Pol.
  Fixpoint Ppow_pos (P:Pol) (p:positive){struct p} : Pol :=
   match p with
   | xH => P
   | xO p => subst_l (Psquare (Ppow_pos P p))
   | xI p => subst_l (Pmul P (Psquare (Ppow_pos P p)))
   end.

  Definition Ppow_N P n :=
   match n with
   | N0 => P1
   | Npos p => Ppow_pos P p
   end.

  Lemma Ppow_pos_ok : forall l, (forall P, subst_l P@l == P@l) ->
         forall P p, (Ppow_pos P p)@l == (pow_pos Pmul P p)@l.
  Proof.
   intros l subst_l_ok P.
   induction p;simpl;intros;try rrefl;try rewrite subst_l_ok.
   repeat rewrite Pmul_ok;rewrite Psquare_ok;rewrite IHp;rrefl.
   repeat rewrite Pmul_ok;rewrite Psquare_ok;rewrite IHp;rrefl.
  Qed.

  Lemma Ppow_N_ok : forall l,  (forall P, subst_l P@l == P@l) ->
         forall P n, (Ppow_N P n)@l == (pow_N P1 Pmul P n)@l.
  Proof.  destruct n;simpl. rrefl. apply Ppow_pos_ok. trivial.  Qed.

 End POWER. *)

Section POWER.
  Variable subst_l : Pol -> Pol.
  Fixpoint Ppow_pos (res P:Pol) (p:positive){struct p} : Pol :=
   match p with
   | xH => subst_l (Pmul res P)
   | xO p => Ppow_pos (Ppow_pos res P p) P p
   | xI p => subst_l (Pmul  (Ppow_pos (Ppow_pos res P p) P p) P)
   end.

  Definition Ppow_N P n :=
   match n with
   | N0 => P1
   | Npos p => Ppow_pos P1 P p
   end.

  Lemma Ppow_pos_ok : forall l, (forall P, subst_l P@l == P@l) ->
         forall res P p, (Ppow_pos res P p)@l == res@l * (pow_pos Pmul P p)@l.
  Proof.
   intros l subst_l_ok res P p. generalize res;clear res.
   induction p;simpl;intros;try rewrite subst_l_ok; repeat rewrite Pmul_ok;repeat rewrite IHp.
   rsimpl. mul_push (P@l);rsimpl. rsimpl. rrefl.
  Qed.

  Lemma Ppow_N_ok : forall l,  (forall P, subst_l P@l == P@l) ->
         forall P n, (Ppow_N P n)@l == (pow_N P1 Pmul P n)@l.
  Proof.  destruct n;simpl. rrefl. rewrite Ppow_pos_ok by trivial. Esimpl.  Qed.

 End POWER.

 (** Normalization and rewriting *)

 Section NORM_SUBST_REC.
  Variable n : nat.
  Variable lmp:list (C*Mon*Pol).
  Let subst_l P := PNSubstL P lmp n n.
  Let Pmul_subst P1 P2 := subst_l (Pmul P1 P2).
  Let Ppow_subst := Ppow_N subst_l.

  Fixpoint norm_aux (pe:PExpr) : Pol :=
   match pe with
   | PEc c => Pc c
   | PEX j => mk_X j
   | PEadd (PEopp pe1) pe2 => Psub (norm_aux pe2) (norm_aux pe1)
   | PEadd pe1 (PEopp pe2) =>
     Psub (norm_aux pe1) (norm_aux pe2)
   | PEadd pe1 pe2 => Padd (norm_aux  pe1) (norm_aux pe2)
   | PEsub pe1 pe2 => Psub (norm_aux pe1) (norm_aux pe2)
   | PEmul pe1 pe2 => Pmul (norm_aux pe1) (norm_aux pe2)
   | PEopp pe1 => Popp (norm_aux pe1)
   | PEpow pe1 n => Ppow_N (fun p => p) (norm_aux pe1) n
   end.

  Definition norm_subst pe := subst_l (norm_aux pe).

 (*
  Fixpoint norm_subst (pe:PExpr) : Pol :=
   match pe with
   | PEc c => Pc c
   | PEX j => subst_l (mk_X j)
   | PEadd (PEopp pe1) pe2 => Psub (norm_subst pe2) (norm_subst pe1)
   | PEadd pe1 (PEopp pe2) =>
     Psub (norm_subst pe1) (norm_subst pe2)
   | PEadd pe1 pe2 => Padd (norm_subst  pe1) (norm_subst pe2)
   | PEsub pe1 pe2 => Psub (norm_subst pe1) (norm_subst pe2)
   | PEmul pe1 pe2 => Pmul_subst (norm_subst pe1) (norm_subst pe2)
   | PEopp pe1 => Popp (norm_subst pe1)
   | PEpow pe1 n => Ppow_subst (norm_subst pe1) n
   end.

  Lemma norm_subst_spec :
     forall l pe, MPcond lmp l ->
       PEeval l pe == (norm_subst pe)@l.
  Proof.
   intros;assert (subst_l_ok:forall P, (subst_l P)@l == P@l).
      unfold subst_l;intros.
      rewrite <- PNSubstL_ok;trivial. rrefl.
   assert (Pms_ok:forall P1 P2, (Pmul_subst P1 P2)@l == P1@l*P2@l).
    intros;unfold Pmul_subst;rewrite subst_l_ok;rewrite Pmul_ok;rrefl.
   induction pe;simpl;Esimpl3.
   rewrite subst_l_ok;apply mkX_ok.
   rewrite IHpe1;rewrite IHpe2;destruct pe1;destruct pe2;Esimpl3.
   rewrite IHpe1;rewrite IHpe2;rrefl.
   rewrite Pms_ok;rewrite IHpe1;rewrite IHpe2;rrefl.
   rewrite IHpe;rrefl.
   unfold Ppow_subst. rewrite Ppow_N_ok. trivial.
   rewrite pow_th.(rpow_pow_N). destruct n0;Esimpl3.
   induction p;simpl;try rewrite IHp;try rewrite IHpe;repeat rewrite Pms_ok;
      repeat rewrite Pmul_ok;rrefl.
  Qed.
*)
 Lemma norm_aux_spec :
     forall l pe, MPcond lmp l ->
       PEeval l pe == (norm_aux pe)@l.
  Proof.
   intros.
   induction pe;simpl;Esimpl3.
   apply mkX_ok.
   rewrite IHpe1;rewrite IHpe2;destruct pe1;destruct pe2;Esimpl3.
   rewrite IHpe1;rewrite IHpe2;rrefl.
   rewrite IHpe1;rewrite IHpe2. rewrite Pmul_ok. rrefl.
   rewrite IHpe;rrefl.
   rewrite Ppow_N_ok by (intros;rrefl).
   rewrite pow_th.(rpow_pow_N). destruct n0;Esimpl3.
   induction p;simpl;try rewrite IHp;try rewrite IHpe;repeat rewrite Pms_ok;
      repeat rewrite Pmul_ok;rrefl.
  Qed.

 Lemma norm_subst_spec :
     forall l pe, MPcond lmp l ->
       PEeval l pe == (norm_subst pe)@l.
 Proof.
  intros;unfold norm_subst.
  unfold subst_l;rewrite <- PNSubstL_ok;trivial. apply norm_aux_spec. trivial.
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

  Fixpoint mon_of_pol (P:Pol) : option (C * Mon) :=
  match P with
  | Pc c => if (c ?=! cO) then None else Some (c, mon0)
  | Pinj j P =>
    match mon_of_pol P with
    | None => None
    | Some (c,m) =>  Some (c, mkZmon j m)
    end
  | PX P i Q =>
    if Peq Q P0 then
      match mon_of_pol P with
      | None => None
      | Some (c,m) => Some (c, mkVmon i m)
      end
    else None
  end.

 Fixpoint mk_monpol_list (lpe:list (PExpr * PExpr)) : list (C*Mon*Pol) :=
  match lpe with
  | nil => nil
  | (me,pe)::lpe =>
    match mon_of_pol (norm_subst 0 nil me) with
    | None => mk_monpol_list lpe
    | Some m => (m,norm_subst 0 nil pe):: mk_monpol_list lpe
    end
  end.

  Lemma mon_of_pol_ok : forall P m, mon_of_pol P = Some m ->
              forall l, [fst m] * Mphi l (snd m) == P@l.
  Proof.
    induction P;simpl;intros;Esimpl.
    assert (H1 := (morph_eq CRmorph) c cO).
    destruct (c ?=! cO).
    discriminate.
    inversion H;trivial;Esimpl.
    generalize H;clear H;case_eq (mon_of_pol P).
    intros (c1,P2) H0 H1; inversion H1; Esimpl.
      generalize (IHP (c1, P2) H0 (jump p l)).
      rewrite mkZmon_ok;simpl;auto.
    intros; discriminate.
    generalize H;clear H;change match P3 with
        | Pc c => c ?=! cO
        | Pinj _ _ => false
        | PX _ _ _ => false
        end with (P3 ?== P0).
    assert (H := Peq_ok P3 P0).
    destruct (P3 ?== P0).
    case_eq (mon_of_pol P2);try intros (cc, pp); intros.
    inversion H1.
    simpl.
    rewrite mkVmon_ok;simpl.
    rewrite H;trivial;Esimpl.
     generalize (IHP1 _ H0); simpl; intros HH; rewrite HH; rsimpl.
    discriminate.
    intros;discriminate.
   Qed.

 Lemma interp_PElist_ok : forall l lpe,
         interp_PElist l lpe -> MPcond (mk_monpol_list lpe) l.
 Proof.
   induction lpe;simpl. trivial.
   destruct a;simpl;intros.
   assert (HH:=mon_of_pol_ok (norm_subst 0 nil  p));
     destruct  (mon_of_pol (norm_subst 0 nil p)).
   split.
   rewrite <- norm_subst_spec by exact I.
   destruct lpe;try destruct H;rewrite <- H;
   rewrite (norm_subst_spec 0 nil); try exact I;apply HH;trivial.
   apply IHlpe. destruct lpe;simpl;trivial. destruct H. exact H0.
   apply IHlpe. destruct lpe;simpl;trivial. destruct H. exact H0.
 Qed.

 Lemma norm_subst_ok : forall n l lpe pe,
   interp_PElist l lpe ->
   PEeval l pe == (norm_subst n (mk_monpol_list lpe) pe)@l.
 Proof.
   intros;apply norm_subst_spec. apply interp_PElist_ok;trivial.
  Qed.

 Lemma ring_correct : forall n l lpe pe1 pe2,
   interp_PElist l lpe ->
   (let lmp := mk_monpol_list lpe in
   norm_subst n lmp pe1 ?== norm_subst n lmp pe2) = true ->
   PEeval l pe1 == PEeval l pe2.
 Proof.
  simpl;intros.
  do 2 (rewrite (norm_subst_ok n l lpe);trivial).
  apply Peq_ok;trivial.
 Qed.



  (** Generic evaluation of polynomial towards R avoiding parenthesis *)
 Variable get_sign : C -> option C.
 Variable get_sign_spec : sign_theory copp ceqb get_sign.


 Section EVALUATION.

  (* [mkpow x p] = x^p *)
  Variable mkpow : R -> positive -> R.
  (* [mkpow x p] = -(x^p) *)
  Variable mkopp_pow : R -> positive -> R.
  (* [mkmult_pow r x p] = r * x^p *)
  Variable mkmult_pow : R -> R -> positive -> R.

  Fixpoint mkmult_rec (r:R) (lm:list (R*positive)) {struct lm}: R :=
   match lm with
   | nil => r
   | cons (x,p) t => mkmult_rec (mkmult_pow r x p) t
   end.

  Definition mkmult1 lm :=
   match lm with
   | nil => 1
   | cons (x,p) t => mkmult_rec (mkpow x p) t
   end.

  Definition mkmultm1 lm :=
   match lm with
   | nil => ropp rI
   | cons (x,p) t => mkmult_rec (mkopp_pow x p) t
   end.

  Definition mkmult_c_pos c lm :=
   if c ?=! cI then mkmult1 (rev' lm)
   else mkmult_rec [c] (rev' lm).

  Definition mkmult_c c lm :=
   match get_sign c with
   | None => mkmult_c_pos c lm
   | Some c' =>
     if c' ?=! cI then mkmultm1 (rev' lm)
     else mkmult_rec [c] (rev' lm)
   end.

  Definition mkadd_mult rP c lm :=
   match get_sign c with
   | None => rP + mkmult_c_pos c lm
   | Some c' => rP - mkmult_c_pos c' lm
   end.

  Definition add_pow_list (r:R) n l :=
   match n with
   | N0 => l
   | Npos p => (r,p)::l
   end.

  Fixpoint add_mult_dev
      (rP:R) (P:Pol) (fv:list R) (n:N) (lm:list (R*positive)) {struct P} : R :=
   match P with
   | Pc c =>
     let lm := add_pow_list (hd 0 fv) n lm in
     mkadd_mult rP c lm
   | Pinj j Q =>
     add_mult_dev rP Q (jump j fv) N0 (add_pow_list (hd 0 fv) n lm)
   | PX P i Q =>
     let rP := add_mult_dev rP P fv (Nplus (Npos i) n) lm in
     if Q ?== P0 then rP
     else add_mult_dev rP Q (tail fv) N0 (add_pow_list (hd 0 fv) n lm)
   end.

  Fixpoint mult_dev (P:Pol) (fv : list R) (n:N)
                     (lm:list (R*positive)) {struct P} : R :=
  (* P@l * (hd 0 l)^n * lm *)
  match P with
  | Pc c => mkmult_c c (add_pow_list (hd 0 fv) n lm)
  | Pinj j Q => mult_dev Q (jump j fv) N0 (add_pow_list (hd 0 fv) n lm)
  | PX P i Q =>
     let rP := mult_dev P fv (Nplus (Npos i) n) lm in
     if Q ?== P0 then rP
     else
       let lmq := add_pow_list (hd 0 fv) n lm in
       add_mult_dev rP Q (tail fv) N0 lmq
  end.

 Definition Pphi_avoid fv P := mult_dev P fv N0 nil.

 Fixpoint r_list_pow (l:list (R*positive)) : R :=
  match l with
  | nil => rI
  | cons (r,p) l => pow_pos rmul r p * r_list_pow l
  end.

  Hypothesis mkpow_spec : forall r p, mkpow r p == pow_pos rmul r p.
  Hypothesis mkopp_pow_spec : forall r p, mkopp_pow r p == - (pow_pos rmul r p).
  Hypothesis mkmult_pow_spec : forall r x p, mkmult_pow r x p == r * pow_pos rmul x p.

 Lemma mkmult_rec_ok : forall lm r, mkmult_rec r lm == r * r_list_pow lm.
 Proof.
   induction lm;intros;simpl;Esimpl.
   destruct a as (x,p);Esimpl.
   rewrite IHlm. rewrite mkmult_pow_spec. Esimpl.
  Qed.

 Lemma mkmult1_ok : forall lm, mkmult1 lm == r_list_pow lm.
 Proof.
   destruct lm;simpl;Esimpl.
   destruct p. rewrite mkmult_rec_ok;rewrite mkpow_spec;Esimpl.
 Qed.

 Lemma mkmultm1_ok : forall lm, mkmultm1 lm == - r_list_pow lm.
 Proof.
  destruct lm;simpl;Esimpl.
  destruct p;rewrite mkmult_rec_ok. rewrite mkopp_pow_spec;Esimpl.
 Qed.

 Lemma r_list_pow_rev :  forall l, r_list_pow (rev' l) == r_list_pow l.
 Proof.
   assert
    (forall l lr : list (R * positive), r_list_pow (rev_append l lr) == r_list_pow lr * r_list_pow l).
   induction l;intros;simpl;Esimpl.
   destruct a;rewrite IHl;Esimpl.
   rewrite (ARmul_comm ARth (pow_pos rmul r p)). rrefl.
  intros;unfold rev'. rewrite H;simpl;Esimpl.
  Qed.

 Lemma mkmult_c_pos_ok : forall c lm, mkmult_c_pos c lm == [c]* r_list_pow lm.
 Proof.
  intros;unfold mkmult_c_pos;simpl.
   assert (H := (morph_eq CRmorph) c cI).
   rewrite <- r_list_pow_rev; destruct (c ?=! cI).
  rewrite H;trivial;Esimpl.
  apply mkmult1_ok.  apply mkmult_rec_ok.
 Qed.

 Lemma mkmult_c_ok : forall c lm, mkmult_c c lm == [c] * r_list_pow lm.
 Proof.
  intros;unfold mkmult_c;simpl.
  case_eq (get_sign c);intros.
  assert (H1 := (morph_eq CRmorph) c0  cI).
  destruct (c0 ?=! cI).
   rewrite (CRmorph.(morph_eq) _ _ (get_sign_spec.(sign_spec) _ H)). Esimpl. rewrite H1;trivial.
   rewrite <- r_list_pow_rev;trivial;Esimpl.
  apply mkmultm1_ok.
 rewrite <- r_list_pow_rev; apply mkmult_rec_ok.
 apply mkmult_c_pos_ok.
Qed.

 Lemma mkadd_mult_ok : forall rP c lm, mkadd_mult rP c lm == rP + [c]*r_list_pow lm.
 Proof.
  intros;unfold mkadd_mult.
  case_eq (get_sign c);intros.
  rewrite (CRmorph.(morph_eq) _ _ (get_sign_spec.(sign_spec) _ H));Esimpl.
  rewrite mkmult_c_pos_ok;Esimpl.
  rewrite mkmult_c_pos_ok;Esimpl.
 Qed.

 Lemma add_pow_list_ok :
      forall r n l, r_list_pow (add_pow_list r n l) == pow_N rI rmul r n * r_list_pow l.
 Proof.
   destruct n;simpl;intros;Esimpl.
 Qed.

 Lemma add_mult_dev_ok : forall P rP fv n lm,
    add_mult_dev rP P fv n lm == rP + P@fv*pow_N rI rmul (hd 0 fv) n * r_list_pow lm.
  Proof.
    induction P;simpl;intros.
    rewrite mkadd_mult_ok. rewrite  add_pow_list_ok; Esimpl.
    rewrite IHP. simpl. rewrite  add_pow_list_ok; Esimpl.
    change (match P3 with
       | Pc c => c ?=! cO
       | Pinj _ _ => false
       | PX _ _ _ => false
       end) with (Peq P3 P0).
   change match n with
    | N0 => Npos p
    | Npos q => Npos (p + q)
    end with (Nplus (Npos p) n);trivial.
   assert (H := Peq_ok P3 P0).
    destruct (P3 ?== P0).
    rewrite (H (refl_equal true)).
   rewrite  IHP1. destruct n;simpl;Esimpl;rewrite pow_pos_Pplus;Esimpl.
   rewrite  IHP2.
   rewrite IHP1. destruct n;simpl;Esimpl;rewrite pow_pos_Pplus;Esimpl.
 Qed.

 Lemma mult_dev_ok : forall P fv n lm,
    mult_dev P fv n lm == P@fv * pow_N rI rmul (hd 0 fv) n * r_list_pow lm.
 Proof.
   induction P;simpl;intros;Esimpl.
   rewrite mkmult_c_ok;rewrite add_pow_list_ok;Esimpl.
   rewrite IHP. simpl;rewrite add_pow_list_ok;Esimpl.
  change (match P3 with
       | Pc c => c ?=! cO
       | Pinj _ _ => false
       | PX _ _ _ => false
       end) with (Peq P3 P0).
   change match n with
    | N0 => Npos p
    | Npos q => Npos (p + q)
    end with (Nplus (Npos p) n);trivial.
   assert (H := Peq_ok P3 P0).
    destruct (P3 ?== P0).
    rewrite (H (refl_equal true)).
   rewrite  IHP1. destruct n;simpl;Esimpl;rewrite pow_pos_Pplus;Esimpl.
   rewrite add_mult_dev_ok. rewrite IHP1; rewrite add_pow_list_ok.
   destruct n;simpl;Esimpl;rewrite pow_pos_Pplus;Esimpl.
  Qed.

 Lemma Pphi_avoid_ok : forall P fv, Pphi_avoid fv P  == P@fv.
 Proof.
   unfold Pphi_avoid;intros;rewrite mult_dev_ok;simpl;Esimpl.
 Qed.

 End EVALUATION.

  Definition Pphi_pow :=
   let mkpow x p :=
      match p with xH => x | _ => rpow x (Cp_phi (Npos p)) end in
   let mkopp_pow x p := ropp (mkpow x p)  in
   let mkmult_pow r x p := rmul r (mkpow x p) in
    Pphi_avoid mkpow mkopp_pow mkmult_pow.

 Lemma local_mkpow_ok :
   forall (r : R) (p : positive),
    match p with
    | xI _ => rpow r (Cp_phi (Npos p))
    | xO _ => rpow r (Cp_phi (Npos p))
    | 1 => r
    end == pow_pos rmul r p.
 Proof. intros r p;destruct p;try rewrite pow_th.(rpow_pow_N);reflexivity. Qed.

 Lemma Pphi_pow_ok : forall P fv, Pphi_pow fv P  == P@fv.
 Proof.
  unfold Pphi_pow;intros;apply Pphi_avoid_ok;intros;try rewrite local_mkpow_ok;rrefl.
 Qed.

 Lemma ring_rw_pow_correct : forall n lH l,
      interp_PElist l lH ->
      forall lmp, mk_monpol_list lH = lmp ->
      forall pe npe, norm_subst n lmp pe = npe ->
      PEeval l pe == Pphi_pow l npe.
 Proof.
  intros n lH l H1 lmp Heq1 pe npe Heq2.
  rewrite Pphi_pow_ok. rewrite <- Heq2;rewrite <- Heq1.
  apply norm_subst_ok. trivial.
 Qed.

 Fixpoint mkmult_pow (r x:R) (p: positive) {struct p} : R :=
   match p with
   | xH => r*x
   | xO p => mkmult_pow (mkmult_pow r x p) x p
   | xI p => mkmult_pow (mkmult_pow (r*x) x p) x p
   end.

  Definition mkpow x p :=
    match p with
    | xH => x
    | xO p => mkmult_pow x x (Pdouble_minus_one p)
    | xI p => mkmult_pow x x (xO p)
    end.

  Definition mkopp_pow x p :=
    match p with
    | xH => -x
    | xO p => mkmult_pow (-x) x (Pdouble_minus_one p)
    | xI p => mkmult_pow (-x) x (xO p)
    end.

  Definition Pphi_dev := Pphi_avoid mkpow mkopp_pow mkmult_pow.

  Lemma mkmult_pow_ok : forall p r x, mkmult_pow r x p == r*pow_pos rmul x p.
  Proof.
    induction p;intros;simpl;Esimpl.
    repeat rewrite IHp;Esimpl.
    repeat rewrite IHp;Esimpl.
  Qed.

 Lemma mkpow_ok : forall p x, mkpow x p == pow_pos rmul x p.
  Proof.
    destruct p;simpl;intros;Esimpl.
    repeat rewrite mkmult_pow_ok;Esimpl.
    rewrite mkmult_pow_ok;Esimpl.
    pattern x at 1;replace x with (pow_pos rmul x 1).
    rewrite <- pow_pos_Pplus.
    rewrite <- Pplus_one_succ_l.
    rewrite Psucc_o_double_minus_one_eq_xO.
    simpl;Esimpl.
    trivial.
  Qed.

  Lemma mkopp_pow_ok : forall p x, mkopp_pow x p == - pow_pos rmul x p.
  Proof.
    destruct p;simpl;intros;Esimpl.
    repeat rewrite mkmult_pow_ok;Esimpl.
    rewrite mkmult_pow_ok;Esimpl.
    pattern x at 1;replace x with (pow_pos rmul x 1).
    rewrite <- pow_pos_Pplus.
    rewrite <- Pplus_one_succ_l.
    rewrite Psucc_o_double_minus_one_eq_xO.
    simpl;Esimpl.
    trivial.
  Qed.

 Lemma Pphi_dev_ok : forall P fv, Pphi_dev fv P == P@fv.
  Proof.
   unfold Pphi_dev;intros;apply Pphi_avoid_ok.
   intros;apply mkpow_ok.
   intros;apply mkopp_pow_ok.
   intros;apply mkmult_pow_ok.
  Qed.

 Lemma ring_rw_correct : forall n lH l,
      interp_PElist l lH ->
      forall lmp, mk_monpol_list lH = lmp ->
      forall pe npe, norm_subst n lmp pe = npe ->
      PEeval l pe == Pphi_dev l npe.
 Proof.
  intros n lH l H1 lmp Heq1 pe npe Heq2.
  rewrite  Pphi_dev_ok. rewrite <- Heq2;rewrite <- Heq1.
  apply norm_subst_ok. trivial.
 Qed.


End MakeRingPol.

