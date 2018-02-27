(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(* F. Besson: to evaluate polynomials, the original code is using a list.
   For big polynomials, this is inefficient -- linear access.
   I have modified the code to use binary trees -- logarithmic access.  *)


Set Implicit Arguments.
Require Import Setoid Morphisms Env BinPos BinNat BinInt.
Require Export Ring_theory.

Local Open Scope positive_scope.
Import RingSyntax.

Section MakeRingPol.

 (* Ring elements *)
 Variable R:Type.
 Variable (rO rI : R) (radd rmul rsub: R->R->R) (ropp : R->R).
 Variable req : R -> R -> Prop.

 (* Ring properties *)
 Variable Rsth : Equivalence req.
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
 Variable Cpow : Type.
 Variable Cp_phi : N -> Cpow.
 Variable rpow : R -> Cpow -> R.
 Variable pow_th : power_theory rI rmul req Cp_phi rpow.

 (* R notations *)
 Notation "0" := rO. Notation "1" := rI.
 Infix "+" := radd. Infix "*" := rmul.
 Infix "-" := rsub. Notation "- x" := (ropp x).
 Infix "==" := req.
 Infix "^" := (pow_pos rmul).

 (* C notations *)
 Infix "+!" := cadd. Infix "*!" := cmul.
 Infix "-! " := csub. Notation "-! x" := (copp x).
 Infix "?=!" := ceqb. Notation "[ x ]" := (phi x).

 (* Useful tactics *)
 Add Morphism radd with signature (req ==> req ==> req) as radd_ext.
 Proof. exact (Radd_ext Reqe). Qed.

 Add Morphism rmul with signature (req ==> req ==> req) as rmul_ext.
 Proof. exact (Rmul_ext Reqe). Qed.

 Add Morphism ropp with signature (req ==> req) as ropp_ext.
 Proof. exact (Ropp_ext Reqe). Qed.

 Add Morphism rsub with signature (req ==> req ==> req) as rsub_ext.
 Proof. exact (ARsub_ext Rsth Reqe ARth). Qed.

 Ltac rsimpl := gen_srewrite Rsth Reqe ARth.

 Ltac add_push := gen_add_push radd Rsth Reqe ARth.
 Ltac mul_push := gen_mul_push rmul Rsth Reqe ARth.

 Ltac add_permut_rec t :=
   match t with
   | ?x + ?y => add_permut_rec y || add_permut_rec x
   | _ => add_push t; apply (Radd_ext Reqe); [|reflexivity]
   end.

 Ltac add_permut :=
  repeat (reflexivity ||
    match goal with |- ?t == _ => add_permut_rec t end).

 Ltac mul_permut_rec t :=
   match t with
   | ?x * ?y => mul_permut_rec y || mul_permut_rec x
   | _ => mul_push t; apply (Rmul_ext Reqe); [|reflexivity]
   end.

 Ltac mul_permut :=
  repeat (reflexivity ||
    match goal with |- ?t == _ => mul_permut_rec t end).


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
    match j ?= j' with
    | Eq => Peq Q Q'
    | _ => false
    end
  | PX P i Q, PX P' i' Q' =>
    match i ?= i' with
    | Eq => if Peq P P' then Peq Q Q' else false
    | _ => false
    end
  | _, _ => false
  end.

 Infix "?==" := Peq.

 Definition mkPinj j P :=
  match P with
  | Pc _ => P
  | Pinj j' Q => Pinj (j + j') Q
  | _ => Pinj j P
  end.

 Definition mkPinj_pred j P:=
  match j with
  | xH => P
  | xO j => Pinj (Pos.pred_double j) P
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

 Fixpoint PaddC (P:Pol) (c:C) : Pol :=
  match P with
  | Pc c1 => Pc (c1 +! c)
  | Pinj j Q => Pinj j (PaddC Q c)
  | PX P i Q => PX P i (PaddC Q c)
  end.

 Fixpoint PsubC (P:Pol) (c:C) : Pol :=
  match P with
  | Pc c1 => Pc (c1 -! c)
  | Pinj j Q => Pinj j (PsubC Q c)
  | PX P i Q => PX P i (PsubC Q c)
  end.

 Section PopI.

  Variable Pop : Pol -> Pol -> Pol.
  Variable Q : Pol.

  Fixpoint PaddI (j:positive) (P:Pol) : Pol :=
   match P with
   | Pc c => mkPinj j (PaddC Q c)
   | Pinj j' Q' =>
     match Z.pos_sub j' j with
     | Zpos k =>  mkPinj j (Pop (Pinj k Q') Q)
     | Z0 => mkPinj j (Pop Q' Q)
     | Zneg k => mkPinj j' (PaddI k Q')
     end
   | PX P i Q' =>
     match j with
     | xH => PX P i (Pop Q' Q)
     | xO j => PX P i (PaddI (Pos.pred_double j) Q')
     | xI j => PX P i (PaddI (xO j) Q')
     end
   end.

  Fixpoint PsubI (j:positive) (P:Pol) : Pol :=
   match P with
   | Pc c => mkPinj j (PaddC (--Q) c)
   | Pinj j' Q' =>
     match Z.pos_sub j' j with
     | Zpos k =>  mkPinj j (Pop (Pinj k Q') Q)
     | Z0 => mkPinj j (Pop Q' Q)
     | Zneg k => mkPinj j' (PsubI k Q')
     end
   | PX P i Q' =>
     match j with
     | xH => PX P i (Pop Q' Q)
     | xO j => PX P i (PsubI (Pos.pred_double j) Q')
     | xI j => PX P i (PsubI (xO j) Q')
     end
   end.

 Variable P' : Pol.

 Fixpoint PaddX (i':positive) (P:Pol) : Pol :=
  match P with
  | Pc c => PX P' i' P
  | Pinj j Q' =>
    match j with
    | xH =>  PX P' i' Q'
    | xO j => PX P' i' (Pinj (Pos.pred_double j) Q')
    | xI j => PX P' i' (Pinj (xO j) Q')
    end
  | PX P i Q' =>
    match Z.pos_sub i i' with
    | Zpos k => mkPX (Pop (PX P k P0) P') i' Q'
    | Z0 => mkPX (Pop P P') i Q'
    | Zneg k => mkPX (PaddX k P) i Q'
    end
  end.

 Fixpoint PsubX (i':positive) (P:Pol) : Pol :=
  match P with
  | Pc c => PX (--P') i' P
  | Pinj j Q' =>
    match j with
    | xH =>  PX (--P') i' Q'
    | xO j => PX (--P') i' (Pinj (Pos.pred_double j) Q')
    | xI j => PX (--P') i' (Pinj (xO j) Q')
    end
  | PX P i Q' =>
    match Z.pos_sub i i' with
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
      | xO j => PX P' i' (Padd (Pinj (Pos.pred_double j) Q) Q')
      | xI j => PX P' i' (Padd (Pinj (xO j) Q) Q')
      end
    | PX P i Q =>
      match Z.pos_sub i i' with
      | Zpos k => mkPX (Padd (PX P k P0) P') i' (Padd Q Q')
      | Z0 => mkPX (Padd P P') i (Padd Q Q')
      | Zneg k => mkPX (PaddX Padd P' k P) i (Padd Q Q')
      end
    end
  end.
 Infix "++" := Padd.

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
      | xO j => PX (--P') i' (Psub (Pinj (Pos.pred_double j) Q) Q')
      | xI j => PX (--P') i' (Psub (Pinj (xO j) Q) Q')
      end
    | PX P i Q =>
      match Z.pos_sub i i' with
      | Zpos k => mkPX (Psub (PX P k P0) P') i' (Psub Q Q')
      | Z0 => mkPX (Psub P P') i (Psub Q Q')
      | Zneg k => mkPX (PsubX Psub P' k P) i (Psub Q Q')
      end
    end
  end.
 Infix "--" := Psub.

 (** Multiplication *)

 Fixpoint PmulC_aux (P:Pol) (c:C) : Pol :=
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
  Fixpoint PmulI (j:positive) (P:Pol) : Pol :=
   match P with
   | Pc c => mkPinj j (PmulC Q c)
   | Pinj j' Q' =>
     match Z.pos_sub j' j with
     | Zpos k => mkPinj j (Pmul (Pinj k Q') Q)
     | Z0 => mkPinj j (Pmul Q' Q)
     | Zneg k => mkPinj j' (PmulI k Q')
     end
   | PX P' i' Q' =>
     match j with
     | xH => mkPX (PmulI xH P') i' (Pmul Q' Q)
     | xO j' => mkPX (PmulI j P') i' (PmulI (Pos.pred_double j') Q')
     | xI j' => mkPX (PmulI j P') i' (PmulI (xO j') Q')
     end
   end.

 End PmulI.

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
         | xO j => Pmul (Pinj (Pos.pred_double j) Q) Q'
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

 Infix "**" := Pmul.

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

 (** A monomial is X1^k1...Xi^ki. Its representation
     is a simplified version of the polynomial representation:

     - [mon0] correspond to the polynom [P1].
     - [(zmon j M)] corresponds to [(Pinj j ...)],
       i.e. skip j variable indices.
     - [(vmon i M)] is X^i*M with X the current variable,
       its corresponds to (PX P1 i ...)]
 *)

  Inductive Mon: Set :=
  | mon0: Mon
  | zmon: positive -> Mon -> Mon
  | vmon: positive -> Mon -> Mon.

 Definition mkZmon j M :=
   match M with mon0 => mon0 | _ => zmon j M end.

 Definition zmon_pred j M :=
   match j with xH => M | _ => mkZmon (Pos.pred j) M end.

 Definition mkVmon i M :=
   match M with
   | mon0 => vmon i mon0
   | zmon j m => vmon i (zmon_pred j m)
   | vmon i' m => vmon (i+i') m
   end.

 Fixpoint MFactor (P: Pol) (M: Mon) : Pol * Pol :=
   match P, M with
        _, mon0 => (Pc cO, P)
   | Pc _, _    => (P, Pc cO)
   | Pinj j1 P1, zmon j2 M1 =>
      match (j1 ?= j2) with
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
      match (i ?= j) with
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

  Fixpoint PNSubst1 (P1: Pol) (M1: Mon) (P2: Pol) (n: nat) : Pol :=
    match POneSubst P1 M1 P2 with
     Some P3 => match n with S n1 => PNSubst1 P3 M1 P2 n1 | _ => P3 end
    | _ => P1
    end.

  Definition PNSubst (P1: Pol) (M1: Mon) (P2: Pol) (n: nat): option Pol :=
    match POneSubst P1 M1 P2 with
     Some P3 => match n with S n1 => Some (PNSubst1 P3 M1 P2 n1) | _ => None end
    | _ => None
    end.

  Fixpoint PSubstL1 (P1: Pol) (LM1: list (Mon * Pol)) (n: nat) : Pol :=
    match LM1 with
     cons (M1,P2) LM2 => PSubstL1 (PNSubst1 P1 M1 P2 n) LM2 n
    | _ => P1
    end.

  Fixpoint PSubstL (P1: Pol) (LM1: list (Mon * Pol)) (n: nat) : option Pol :=
    match LM1 with
     cons (M1,P2) LM2 =>
      match PNSubst P1 M1 P2 n with
        Some P3 => Some (PSubstL1 P3 LM2 n)
     |  None => PSubstL P1 LM2 n
     end
    | _ => None
    end.

  Fixpoint PNSubstL (P1: Pol) (LM1: list (Mon * Pol)) (m n: nat) : Pol :=
    match PSubstL P1 LM1 n with
     Some P3 => match m with S m1 => PNSubstL P3 LM1 m1 n | _ => P3 end
    | _ => P1
    end.

 (** Evaluation of a polynomial towards R *)

 Fixpoint Pphi(l:Env R) (P:Pol) : R :=
  match P with
  | Pc c => [c]
  | Pinj j Q => Pphi (jump j l) Q
  | PX P i Q => Pphi l P * (hd l) ^ i + Pphi (tail l) Q
  end.

 Reserved Notation "P @ l " (at level 10, no associativity).
 Notation "P @ l " := (Pphi l P).

 (** Evaluation of a monomial towards R *)

 Fixpoint Mphi(l:Env R) (M: Mon) : R :=
  match M with
  | mon0 => rI
  | zmon j M1 => Mphi (jump j l) M1
  | vmon i M1 => Mphi (tail l) M1 * (hd l) ^ i
  end.

 Notation "M @@ l" := (Mphi l M) (at level 10, no associativity).

 (** Proofs *)

 Ltac destr_pos_sub :=
  match goal with |- context [Z.pos_sub ?x ?y] =>
   generalize (Z.pos_sub_discr x y); destruct (Z.pos_sub x y)
  end.

 Lemma Peq_ok P P' : (P ?== P') = true -> forall l, P@l == P'@ l.
 Proof.
  revert P';induction P;destruct P';simpl; intros H l; try easy.
  - now apply (morph_eq CRmorph).
  - destruct (Pos.compare_spec p p0); [ subst | easy | easy ].
    now rewrite IHP.
  - specialize (IHP1 P'1); specialize (IHP2 P'2).
    destruct (Pos.compare_spec p p0); [ subst | easy | easy ].
    destruct (P2 ?== P'1); [|easy].
    rewrite H in *.
    now rewrite IHP1, IHP2.
 Qed.

 Lemma Peq_spec P P' :
   BoolSpec (forall l, P@l == P'@l) True (P ?== P').
 Proof.
  generalize (Peq_ok P P'). destruct (P ?== P'); auto.
 Qed.

 Lemma Pphi0 l : P0@l == 0.
 Proof.
  simpl;apply (morph0 CRmorph).
 Qed.

 Lemma Pphi1 l : P1@l == 1.
 Proof.
  simpl;apply (morph1 CRmorph).
 Qed.

Lemma env_morph p e1 e2 :
  (forall x, e1 x = e2 x) -> p @ e1 = p @ e2.
Proof.
  revert e1 e2. induction p ; simpl.
  - reflexivity.
  - intros e1 e2 EQ. apply IHp. intros. apply EQ.
  - intros e1 e2 EQ. f_equal; [f_equal|].
    + now apply IHp1.
    + f_equal. apply EQ.
    + apply IHp2. intros; apply EQ.
Qed.

Lemma Pjump_add P i j l :
  P @ (jump (i + j) l) = P @ (jump j (jump i l)).
Proof.
  apply env_morph. intros. rewrite <- jump_add. f_equal.
  apply Pos.add_comm.
Qed.

Lemma Pjump_xO_tail P p l :
  P @ (jump (xO p) (tail l)) = P @ (jump (xI p) l).
Proof.
  apply env_morph. intros. now jump_simpl.
Qed.

Lemma Pjump_pred_double P p l :
  P @ (jump (Pos.pred_double p) (tail l)) = P @ (jump (xO p) l).
Proof.
  apply env_morph. intros.
  rewrite jump_pred_double. now jump_simpl.
Qed.

 Lemma mkPinj_ok j l P : (mkPinj j P)@l == P@(jump j l).
 Proof.
  destruct P;simpl;rsimpl.
  now rewrite Pjump_add.
 Qed.

 Lemma pow_pos_add x i j : x^(j + i) == x^i * x^j.
 Proof.
  rewrite Pos.add_comm.
  apply (pow_pos_add Rsth Reqe.(Rmul_ext) ARth.(ARmul_assoc)).
 Qed.

 Lemma ceqb_spec c c' : BoolSpec ([c] == [c']) True (c ?=! c').
 Proof.
  generalize (morph_eq CRmorph c c').
  destruct (c ?=! c'); auto.
 Qed.

 Lemma mkPX_ok l P i Q :
  (mkPX P i Q)@l == P@l * (hd l)^i + Q@(tail l).
 Proof.
  unfold mkPX. destruct P.
  - case ceqb_spec; intros H; simpl; try reflexivity.
    rewrite H, (morph0 CRmorph), mkPinj_ok; rsimpl.
  - reflexivity.
  - case Peq_spec; intros H; simpl; try reflexivity.
    rewrite H, Pphi0, Pos.add_comm, pow_pos_add; rsimpl.
 Qed.

 Hint Rewrite
  Pphi0
  Pphi1
  mkPinj_ok
  mkPX_ok
  (morph0 CRmorph)
  (morph1 CRmorph)
  (morph0 CRmorph)
  (morph_add CRmorph)
  (morph_mul CRmorph)
  (morph_sub CRmorph)
  (morph_opp CRmorph)
  : Esimpl.

 (* Quicker than autorewrite with Esimpl :-) *)
 Ltac Esimpl := try rewrite_db Esimpl; rsimpl; simpl.

 Lemma PaddC_ok c P l : (PaddC P c)@l == P@l + [c].
 Proof.
  revert l;induction P;simpl;intros;Esimpl;trivial.
  rewrite IHP2;rsimpl.
 Qed.

 Lemma PsubC_ok c P l : (PsubC P c)@l == P@l - [c].
 Proof.
  revert l;induction P;simpl;intros.
  - Esimpl.
  - rewrite IHP;rsimpl.
  - rewrite IHP2;rsimpl.
 Qed.

 Lemma PmulC_aux_ok c P l : (PmulC_aux P c)@l == P@l * [c].
 Proof.
  revert l;induction P;simpl;intros;Esimpl;trivial.
  rewrite IHP1, IHP2;rsimpl. add_permut. mul_permut.
 Qed.

 Lemma PmulC_ok c P l : (PmulC P c)@l == P@l * [c].
 Proof.
  unfold PmulC.
  case ceqb_spec; intros H.
  - rewrite H; Esimpl.
  - case ceqb_spec; intros H'.
    + rewrite H'; Esimpl.
    + apply PmulC_aux_ok.
 Qed.

 Lemma Popp_ok P l : (--P)@l == - P@l.
 Proof.
  revert l;induction P;simpl;intros.
  - Esimpl.
  - apply IHP.
  - rewrite IHP1, IHP2;rsimpl.
 Qed.

 Hint Rewrite PaddC_ok PsubC_ok PmulC_ok Popp_ok : Esimpl.

 Lemma PaddX_ok P' P k l :
  (forall P l, (P++P')@l == P@l + P'@l) ->
  (PaddX Padd P' k P) @ l == P@l + P'@l * (hd l)^k.
 Proof.
  intros IHP'.
  revert k l. induction P;simpl;intros.
  - add_permut.
  - destruct p; simpl;
    rewrite ?Pjump_xO_tail, ?Pjump_pred_double; add_permut.
  - destr_pos_sub; intros ->;Esimpl.
    + rewrite IHP';rsimpl. add_permut.
    + rewrite IHP', pow_pos_add;simpl;Esimpl. add_permut.
    + rewrite IHP1, pow_pos_add;rsimpl. add_permut.
 Qed.

 Lemma Padd_ok P' P l : (P ++ P')@l == P@l + P'@l.
 Proof.
  revert P l; induction P';simpl;intros;Esimpl.
  - revert p l; induction P;simpl;intros.
    + Esimpl; add_permut.
    + destr_pos_sub; intros ->;Esimpl.
      * now rewrite IHP'.
      * rewrite IHP';Esimpl. now rewrite Pjump_add.
      * rewrite IHP. now rewrite Pjump_add.
    + destruct p0;simpl.
      * rewrite IHP2;simpl. rsimpl. rewrite Pjump_xO_tail. Esimpl.
      * rewrite IHP2;simpl. rewrite Pjump_pred_double. rsimpl.
      * rewrite IHP'. rsimpl.
  - destruct P;simpl.
    + Esimpl. add_permut.
    + destruct p0;simpl;Esimpl; rewrite IHP'2; simpl.
      * rewrite Pjump_xO_tail. rsimpl. add_permut.
      * rewrite Pjump_pred_double. rsimpl. add_permut.
      * rsimpl. unfold tail. add_permut.
    + destr_pos_sub; intros ->; Esimpl.
      * rewrite IHP'1, IHP'2;rsimpl. add_permut.
      * rewrite IHP'1, IHP'2;simpl;Esimpl.
        rewrite pow_pos_add;rsimpl. add_permut.
      * rewrite PaddX_ok by trivial; rsimpl.
        rewrite IHP'2, pow_pos_add; rsimpl. add_permut.
 Qed.

 Lemma PsubX_ok P' P k l :
  (forall P l, (P--P')@l == P@l - P'@l) ->
  (PsubX Psub P' k P) @ l == P@l - P'@l * (hd l)^k.
 Proof.
  intros IHP'.
  revert k l. induction P;simpl;intros.
  - rewrite Popp_ok;rsimpl; add_permut.
  - destruct p; simpl;
    rewrite Popp_ok;rsimpl;
    rewrite ?Pjump_xO_tail, ?Pjump_pred_double; add_permut.
  - destr_pos_sub; intros ->; Esimpl.
    + rewrite IHP';rsimpl. add_permut.
    + rewrite IHP', pow_pos_add;simpl;Esimpl. add_permut.
    + rewrite IHP1, pow_pos_add;rsimpl. add_permut.
 Qed.

 Lemma Psub_ok P' P l : (P -- P')@l == P@l - P'@l.
 Proof.
  revert P l; induction P';simpl;intros;Esimpl.
  - revert p l; induction P;simpl;intros.
    + Esimpl; add_permut.
    + destr_pos_sub; intros ->;Esimpl.
      * rewrite IHP';rsimpl.
      * rewrite IHP';Esimpl. now rewrite Pjump_add.
      * rewrite IHP. now rewrite Pjump_add.
    + destruct p0;simpl.
      * rewrite IHP2;simpl. rsimpl. rewrite Pjump_xO_tail. Esimpl.
      * rewrite IHP2;simpl. rewrite Pjump_pred_double. rsimpl.
      * rewrite IHP'. rsimpl.
  - destruct P;simpl.
    + Esimpl; add_permut.
    + destruct p0;simpl;Esimpl; rewrite IHP'2; simpl.
      * rewrite Pjump_xO_tail. rsimpl. add_permut.
      * rewrite Pjump_pred_double. rsimpl. add_permut.
      * rsimpl. unfold tail. add_permut.
    + destr_pos_sub; intros ->; Esimpl.
      * rewrite IHP'1, IHP'2;rsimpl. add_permut.
      * rewrite IHP'1, IHP'2;simpl;Esimpl.
        rewrite pow_pos_add;rsimpl. add_permut.
      * rewrite PsubX_ok by trivial;rsimpl.
        rewrite IHP'2, pow_pos_add;rsimpl. add_permut.
 Qed.

 Lemma PmulI_ok P' :
   (forall P l, (Pmul P P') @ l == P @ l * P' @ l) ->
   forall P p l, (PmulI Pmul P' p P) @ l == P @ l * P' @ (jump p l).
 Proof.
  intros IHP'.
  induction P;simpl;intros.
  - Esimpl; mul_permut.
  - destr_pos_sub; intros ->;Esimpl.
    + now rewrite IHP'.
    + now rewrite IHP', Pjump_add.
    + now rewrite IHP, Pjump_add.
  - destruct p0;Esimpl; rewrite ?IHP1, ?IHP2; rsimpl.
    + rewrite Pjump_xO_tail. f_equiv. mul_permut.
    + rewrite Pjump_pred_double. f_equiv. mul_permut.
    + rewrite IHP'. f_equiv. mul_permut.
 Qed.

 Lemma Pmul_ok P P' l : (P**P')@l == P@l * P'@l.
 Proof.
  revert P l;induction P';simpl;intros.
  - apply PmulC_ok.
  - apply PmulI_ok;trivial.
  - destruct P.
    + rewrite (ARmul_comm ARth). Esimpl.
    + Esimpl. rewrite IHP'1;Esimpl. f_equiv.
      destruct p0;rewrite IHP'2;Esimpl.
      * now rewrite Pjump_xO_tail.
      * rewrite Pjump_pred_double; Esimpl.
    + rewrite Padd_ok, !mkPX_ok, Padd_ok, !mkPX_ok,
       !IHP'1, !IHP'2, PmulI_ok; trivial. simpl. Esimpl.
      unfold tail.
      add_permut; f_equiv; mul_permut.
 Qed.

 Lemma Psquare_ok P l : (Psquare P)@l == P@l * P@l.
 Proof.
  revert l;induction P;simpl;intros;Esimpl.
  - apply IHP.
  - rewrite Padd_ok, Pmul_ok;Esimpl.
    rewrite IHP1, IHP2.
    mul_push ((hd l)^p). now mul_push (P2@l).
 Qed.

 Lemma Mphi_morph M e1 e2 :
  (forall x, e1 x = e2 x) -> M @@ e1 = M @@ e2.
 Proof.
   revert e1 e2; induction M; simpl; intros e1 e2 EQ; trivial.
   - apply IHM. intros; apply EQ.
   - f_equal.
     * apply IHM. intros; apply EQ.
     * f_equal. apply EQ.
 Qed.

Lemma Mjump_xO_tail M p l :
  M @@ (jump (xO p) (tail l)) = M @@ (jump (xI p) l).
Proof.
  apply Mphi_morph. intros. now jump_simpl.
Qed.

Lemma Mjump_pred_double M p l :
  M @@ (jump (Pos.pred_double p) (tail l)) = M @@ (jump (xO p) l).
Proof.
  apply Mphi_morph. intros.
  rewrite jump_pred_double. now jump_simpl.
Qed.

Lemma Mjump_add M i j l :
  M @@ (jump (i + j) l) = M @@ (jump j (jump i l)).
Proof.
  apply Mphi_morph. intros. now rewrite <- jump_add, Pos.add_comm.
Qed.

 Lemma mkZmon_ok M j l :
   (mkZmon j M) @@ l == (zmon j M) @@ l.
 Proof.
 destruct M; simpl; rsimpl.
 Qed.

 Lemma zmon_pred_ok M j l :
   (zmon_pred j M) @@ (tail l) == (zmon j M) @@ l.
 Proof.
   destruct j; simpl; rewrite ?mkZmon_ok; simpl; rsimpl.
   - now rewrite Mjump_xO_tail.
   - rewrite Mjump_pred_double; rsimpl.
 Qed.

 Lemma mkVmon_ok M i l :
   (mkVmon i M)@@l == M@@l * (hd l)^i.
 Proof.
  destruct M;simpl;intros;rsimpl.
  - rewrite zmon_pred_ok;simpl;rsimpl.
  - rewrite pow_pos_add;rsimpl.
 Qed.

 Ltac destr_mfactor R S := match goal with
  | H : context [MFactor ?P _] |- context [MFactor ?P ?M] =>
    specialize (H M); destruct MFactor as (R,S)
 end.

 Lemma Mphi_ok P M l :
   let (Q,R) := MFactor P M in
     P@l == Q@l + M@@l * R@l.
 Proof.
 revert M l; induction P; destruct M; intros l; simpl; auto; Esimpl.
 - case Pos.compare_spec; intros He; simpl.
   * destr_mfactor R1 S1. now rewrite IHP, He, !mkPinj_ok.
   * destr_mfactor R1 S1. rewrite IHP; simpl.
     now rewrite !mkPinj_ok, <- Mjump_add, Pos.add_comm, Pos.sub_add.
   * Esimpl.
 - destr_mfactor R1 S1. destr_mfactor R2 S2.
   rewrite IHP1, IHP2, !mkPX_ok, zmon_pred_ok; simpl; rsimpl.
   add_permut.
 - case Pos.compare_spec; intros He; simpl; destr_mfactor R1 S1;
   rewrite ?He, IHP1, mkPX_ok, ?mkZmon_ok; simpl; rsimpl;
   unfold tail; add_permut; mul_permut.
   * rewrite <- pow_pos_add, Pos.add_comm, Pos.sub_add by trivial; rsimpl.
   * rewrite mkPX_ok. simpl. Esimpl. mul_permut.
     rewrite <- pow_pos_add, Pos.sub_add by trivial; rsimpl.
 Qed.

 Lemma POneSubst_ok P1 M1 P2 P3 l :
   POneSubst P1 M1 P2 = Some P3 -> M1@@l == P2@l ->
   P1@l == P3@l.
 Proof.
 unfold POneSubst.
 assert (H := Mphi_ok P1). destr_mfactor R1 S1. rewrite H; clear H.
 intros EQ EQ'. replace P3 with (R1 ++ P2 ** S1).
 - rewrite EQ', Padd_ok, Pmul_ok; rsimpl.
 - revert EQ. destruct S1; try now injection 1.
   case ceqb_spec; now inversion 2.
 Qed.

 Lemma PNSubst1_ok n P1 M1 P2 l :
    M1@@l == P2@l -> P1@l == (PNSubst1 P1 M1 P2 n)@l.
 Proof.
 revert P1. induction n; simpl; intros P1;
 generalize (POneSubst_ok P1 M1 P2); destruct POneSubst;
   intros; rewrite <- ?IHn; auto; reflexivity.
 Qed.

 Lemma PNSubst_ok n P1 M1 P2 l P3 :
    PNSubst P1 M1 P2 n = Some P3 -> M1@@l == P2@l -> P1@l == P3@l.
 Proof.
 unfold PNSubst.
 assert (H := POneSubst_ok P1 M1 P2); destruct POneSubst; try discriminate.
 destruct n; inversion_clear 1.
 intros. rewrite <- PNSubst1_ok; auto.
 Qed.

 Fixpoint MPcond (LM1: list (Mon * Pol)) (l: Env R) : Prop :=
   match LM1 with
   | cons (M1,P2) LM2 => (M1@@l == P2@l) /\ MPcond LM2 l
   | _ => True
   end.

 Lemma PSubstL1_ok n LM1 P1 l :
   MPcond LM1 l -> P1@l == (PSubstL1 P1 LM1 n)@l.
 Proof.
 revert P1; induction LM1 as [|(M2,P2) LM2 IH]; simpl; intros.
 - reflexivity.
 - rewrite <- IH by intuition. now apply PNSubst1_ok.
 Qed.

 Lemma PSubstL_ok n LM1 P1 P2 l :
   PSubstL P1 LM1 n = Some P2 -> MPcond LM1 l -> P1@l == P2@l.
 Proof.
 revert P1. induction LM1 as [|(M2,P2') LM2 IH]; simpl; intros.
 - discriminate.
 - assert (H':=PNSubst_ok n P3 M2 P2'). destruct PNSubst.
   * injection H as <-. rewrite <- PSubstL1_ok; intuition.
   * now apply IH.
 Qed.

 Lemma PNSubstL_ok m n LM1 P1 l :
    MPcond LM1 l -> P1@l == (PNSubstL P1 LM1 m n)@l.
 Proof.
 revert LM1 P1. induction m; simpl; intros;
 assert (H' := PSubstL_ok n LM1 P2); destruct PSubstL;
 auto; try reflexivity.
 rewrite <- IHm; auto.
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

 Fixpoint PEeval (l:Env R) (pe:PExpr) : R :=
   match pe with
   | PEc c => phi c
   | PEX j => nth j l
   | PEadd pe1 pe2 => (PEeval l pe1) + (PEeval l pe2)
   | PEsub pe1 pe2 => (PEeval l pe1) - (PEeval l pe2)
   | PEmul pe1 pe2 => (PEeval l pe1) * (PEeval l pe2)
   | PEopp pe1 => - (PEeval l pe1)
   | PEpow pe1 n => rpow (PEeval l pe1) (Cp_phi n)
   end.

 (** Correctness proofs *)

 Lemma mkX_ok p l : nth p l == (mk_X p) @ l.
 Proof.
  destruct p;simpl;intros;Esimpl;trivial.
  rewrite nth_spec ; auto.
  unfold hd.
  now rewrite <- nth_pred_double, nth_jump.
 Qed.

 Hint Rewrite Padd_ok Psub_ok : Esimpl.

Section POWER.
  Variable subst_l : Pol -> Pol.
  Fixpoint Ppow_pos (res P:Pol) (p:positive) : Pol :=
   match p with
   | xH => subst_l (res ** P)
   | xO p => Ppow_pos (Ppow_pos res P p) P p
   | xI p => subst_l ((Ppow_pos (Ppow_pos res P p) P p) ** P)
   end.

  Definition Ppow_N P n :=
   match n with
   | N0 => P1
   | Npos p => Ppow_pos P1 P p
   end.

  Lemma Ppow_pos_ok l :
    (forall P, subst_l P@l == P@l) ->
    forall res P p, (Ppow_pos res P p)@l == res@l * (pow_pos Pmul P p)@l.
  Proof.
   intros subst_l_ok res P p. revert res.
   induction p;simpl;intros; rewrite ?subst_l_ok, ?Pmul_ok, ?IHp;
    mul_permut.
  Qed.

  Lemma Ppow_N_ok l :
    (forall P, subst_l P@l == P@l) ->
    forall P n, (Ppow_N P n)@l == (pow_N P1 Pmul P n)@l.
  Proof.
  destruct n;simpl.
  - reflexivity.
  - rewrite Ppow_pos_ok by trivial. Esimpl.
  Qed.

 End POWER.

 (** Normalization and rewriting *)

 Section NORM_SUBST_REC.
  Variable n : nat.
  Variable lmp:list (Mon*Pol).
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

  (** Internally, [norm_aux] is expanded in a large number of cases.
      To speed-up proofs, we use an alternative definition. *)

  Definition get_PEopp pe :=
   match pe with
   | PEopp pe' => Some pe'
   | _ => None
   end.

  Lemma norm_aux_PEadd pe1 pe2 :
    norm_aux (PEadd pe1 pe2) =
    match get_PEopp pe1, get_PEopp pe2 with
    | Some pe1', _ => (norm_aux pe2) -- (norm_aux pe1')
    | None, Some pe2' => (norm_aux pe1) -- (norm_aux pe2')
    | None, None => (norm_aux pe1) ++ (norm_aux pe2)
    end.
  Proof.
  simpl (norm_aux (PEadd _ _)).
  destruct pe1; [ | | | | | reflexivity | ];
   destruct pe2; simpl get_PEopp; reflexivity.
  Qed.

  Lemma norm_aux_PEopp pe :
    match get_PEopp pe with
    | Some pe' => norm_aux pe = -- (norm_aux pe')
    | None => True
    end.
  Proof.
  now destruct pe.
  Qed.

  Lemma norm_aux_spec l pe :
    PEeval l pe == (norm_aux pe)@l.
  Proof.
   intros.
   induction pe.
   - reflexivity.
   - apply mkX_ok.
   - simpl PEeval. rewrite IHpe1, IHpe2.
     assert (H1 := norm_aux_PEopp pe1).
     assert (H2 := norm_aux_PEopp pe2).
     rewrite norm_aux_PEadd.
     do 2 destruct get_PEopp; rewrite ?H1, ?H2; Esimpl; add_permut.
   - simpl. rewrite IHpe1, IHpe2. Esimpl.
   - simpl. rewrite IHpe1, IHpe2. now rewrite Pmul_ok.
   - simpl. rewrite IHpe. Esimpl.
   - simpl. rewrite Ppow_N_ok by reflexivity.
     rewrite pow_th.(rpow_pow_N). destruct n0; simpl; Esimpl.
     induction p;simpl; now rewrite ?IHp, ?IHpe, ?Pms_ok, ?Pmul_ok.
  Qed.

 End NORM_SUBST_REC.

End MakeRingPol.
