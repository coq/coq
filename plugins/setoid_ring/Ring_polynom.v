(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


Set Implicit Arguments.
Require Import Setoid Morphisms. 
Require Import BinList BinPos BinNat BinInt.
Require Export Ring_theory.
Local Open Scope positive_scope.
Import RingSyntax.
(* Set Universe Polymorphism. *)

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

 (* division is ok *)
 Variable cdiv: C -> C -> C * C.
 Variable div_th: div_theory req cadd cmul phi cdiv.


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
        _, mon0 => if (ceqb c cI) then (Pc cO, P) else CFactor P c
   | Pc _, _    => (P, Pc cO)
   | Pinj j1 P1, zmon j2 M1 =>
      match j1 ?= j2 with
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
      match i ?= j with
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

  Fixpoint PNSubst1 (P1: Pol) (cM1: C * Mon) (P2: Pol) (n: nat) : Pol :=
    match POneSubst P1 cM1 P2 with
     Some P3 => match n with S n1 => PNSubst1 P3 cM1 P2 n1 | _ => P3 end
    | _ => P1
    end.

  Definition PNSubst (P1: Pol) (cM1: C * Mon) (P2: Pol) (n: nat): option Pol :=
    match POneSubst P1 cM1 P2 with
     Some P3 => match n with S n1 => Some (PNSubst1 P3 cM1 P2 n1) | _ => None end
    | _ => None
    end.

  Fixpoint PSubstL1 (P1: Pol) (LM1: list ((C * Mon) * Pol)) (n: nat) : Pol :=
    match LM1 with
     cons (M1,P2) LM2 => PSubstL1 (PNSubst1 P1 M1 P2 n) LM2 n
    | _ => P1
    end.

  Fixpoint PSubstL (P1: Pol) (LM1: list ((C * Mon) * Pol)) (n: nat) : option Pol :=
    match LM1 with
     cons (M1,P2) LM2 =>
      match PNSubst P1 M1 P2 n with
        Some P3 => Some (PSubstL1 P3 LM2 n)
     |  None => PSubstL P1 LM2 n
     end
    | _ => None
    end.

  Fixpoint PNSubstL (P1: Pol) (LM1: list ((C * Mon) * Pol)) (m n: nat) : Pol :=
    match PSubstL P1 LM1 n with
     Some P3 => match m with S m1 => PNSubstL P3 LM1 m1 n | _ => P3 end
    | _ => P1
    end.

 (** Evaluation of a polynomial towards R *)

 Local Notation hd := (List.hd 0).

 Fixpoint Pphi(l:list R) (P:Pol) : R :=
  match P with
  | Pc c => [c]
  | Pinj j Q => Pphi (jump j l) Q
  | PX P i Q => Pphi l P * (hd l) ^ i + Pphi (tail l) Q
  end.

 Reserved Notation "P @ l " (at level 10, no associativity).
 Notation "P @ l " := (Pphi l P).

 Definition Pequiv (P Q : Pol) := forall l, P@l == Q@l.
 Infix "===" := Pequiv (at level 70, no associativity).

 Instance Pequiv_eq : Equivalence Pequiv.
 Proof.
  unfold Pequiv; split; red; intros; [reflexivity|now symmetry|now etransitivity].
 Qed.

 Instance Pphi_ext : Proper (eq ==> Pequiv ==> req) Pphi.
 Proof.
  now intros l l' <- P Q H.
 Qed.

 Instance Pinj_ext : Proper (eq ==> Pequiv ==> Pequiv) Pinj.
 Proof.
  intros i j <- P P' HP l. simpl. now rewrite HP.
 Qed.

 Instance PX_ext : Proper (Pequiv ==> eq ==> Pequiv ==> Pequiv) PX.
 Proof.
  intros P P' HP p p' <- Q Q' HQ l. simpl. now rewrite HP, HQ.
 Qed.

 (** Evaluation of a monomial towards R *)

 Fixpoint Mphi(l:list R) (M: Mon) : R :=
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

 Lemma jump_add' i j (l:list R) : jump (i + j) l = jump j (jump i l).
 Proof. rewrite Pos.add_comm. apply jump_add. Qed.

 Lemma Peq_ok P P' : (P ?== P') = true -> P === P'.
 Proof.
  unfold Pequiv.
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

 Lemma Peq_spec P P' : BoolSpec (P === P') True (P ?== P').
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

 Lemma mkPinj_ok j l P : (mkPinj j P)@l == P@(jump j l).
 Proof.
  destruct P;simpl;rsimpl.
  now rewrite jump_add'.
 Qed.

 Instance mkPinj_ext : Proper (eq ==> Pequiv ==> Pequiv) mkPinj.
 Proof.
  intros i j <- P Q H l. now rewrite !mkPinj_ok.
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

 Instance mkPX_ext : Proper (Pequiv ==> eq ==> Pequiv ==> Pequiv) mkPX.
 Proof.
  intros P P' HP i i' <- Q Q' HQ l. now rewrite !mkPX_ok, HP, HQ.
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
    rewrite ?jump_pred_double; add_permut.
  - destr_pos_sub; intros ->; Esimpl.
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
      * rewrite IHP';Esimpl. now rewrite jump_add'.
      * rewrite IHP. now rewrite jump_add'.
    + destruct p0;simpl.
      * rewrite IHP2;simpl. rsimpl.
      * rewrite IHP2;simpl. rewrite jump_pred_double. rsimpl.
      * rewrite IHP'. rsimpl.
  - destruct P;simpl.
    + Esimpl. add_permut.
    + destruct p0;simpl;Esimpl; rewrite IHP'2; simpl.
      * rsimpl. add_permut.
      * rewrite jump_pred_double. rsimpl. add_permut.
      * rsimpl. add_permut.
    + destr_pos_sub; intros ->; Esimpl.
      * rewrite IHP'1, IHP'2;rsimpl. add_permut.
      * rewrite IHP'1, IHP'2;simpl;Esimpl.
        rewrite pow_pos_add;rsimpl. add_permut.
      * rewrite PaddX_ok by trivial; rsimpl.
        rewrite IHP'2, pow_pos_add; rsimpl. add_permut.
 Qed.

 Lemma Psub_opp P' P : P -- P' === P ++ (--P').
 Proof.
  revert P; induction P'; simpl; intros.
  - intro l; Esimpl.
  - revert p; induction P; simpl; intros; try reflexivity.
    + destr_pos_sub; intros ->; now apply mkPinj_ext.
    + destruct p0; now apply PX_ext.
  - destruct P; simpl; try reflexivity.
    + destruct p0; now apply PX_ext.
    + destr_pos_sub; intros ->; apply mkPX_ext; auto.
      revert p1. induction P2; simpl; intros; try reflexivity.
      destr_pos_sub; intros ->; now apply mkPX_ext.
 Qed.

 Lemma Psub_ok P' P l : (P -- P')@l == P@l - P'@l.
 Proof.
  rewrite Psub_opp, Padd_ok, Popp_ok. rsimpl.
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
    + now rewrite IHP', jump_add'.
    + now rewrite IHP, jump_add'.
  - destruct p0;Esimpl; rewrite ?IHP1, ?IHP2; rsimpl.
    + f_equiv. mul_permut.
    + rewrite jump_pred_double. f_equiv. mul_permut.
    + rewrite IHP'. f_equiv. mul_permut.
 Qed.

 Lemma Pmul_ok P P' l : (P**P')@l == P@l * P'@l.
 Proof.
  revert P l;induction P';simpl;intros.
  - apply PmulC_ok.
  - apply PmulI_ok;trivial.
  - destruct P.
    + rewrite (ARmul_comm ARth). Esimpl.
    + Esimpl. f_equiv. rewrite IHP'1; Esimpl.
      destruct p0;rewrite IHP'2;Esimpl.
      rewrite jump_pred_double; Esimpl.
    + rewrite Padd_ok, !mkPX_ok, Padd_ok, !mkPX_ok,
       !IHP'1, !IHP'2, PmulI_ok; trivial. simpl. Esimpl.
      add_permut; f_equiv; mul_permut.
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
   rewrite jump_pred_double; rsimpl.
 Qed.

 Lemma mkVmon_ok M i l :
   (mkVmon i M)@@l == M@@l * (hd l)^i.
 Proof.
  destruct M;simpl;intros;rsimpl.
  - rewrite zmon_pred_ok;simpl;rsimpl.
  - rewrite pow_pos_add;rsimpl.
 Qed.

 Ltac destr_factor := match goal with
  | H : context [CFactor ?P _] |- context [CFactor ?P ?c] =>
    destruct (CFactor P c); destr_factor; rewrite H; clear H
  | H : context [MFactor ?P _ _] |- context [MFactor ?P ?c ?M] =>
    specialize (H M); destruct (MFactor P c M); destr_factor; rewrite H; clear H
  | _ => idtac
 end.

 Lemma Mcphi_ok P c l :
   let (Q,R) := CFactor P c in
     P@l == Q@l + [c] * R@l.
 Proof.
 revert l.
 induction P as [c0 | j P IH | P1 IH1 i P2 IH2]; intros l; Esimpl. 
 - assert (H := div_th.(div_eucl_th) c0 c). 
   destruct cdiv as (q,r). rewrite H; Esimpl. add_permut. 
 - destr_factor. Esimpl.
 - destr_factor. Esimpl. add_permut.
 Qed.

 Lemma Mphi_ok P (cM: C * Mon) l :
   let (c,M) := cM in
   let (Q,R) := MFactor P c M in
     P@l == Q@l + [c] * M@@l * R@l.
 Proof. 
 destruct cM as (c,M). revert M l.
 induction P; destruct M; intros l; simpl; auto; 
 try (case ceqb_spec; intro He);
  try (case Pos.compare_spec; intros He);
  rewrite ?He;
   destr_factor; simpl; Esimpl.
 - assert (H := div_th.(div_eucl_th) c0 c).
   destruct cdiv as (q,r). rewrite H; Esimpl. add_permut.
 - assert (H := Mcphi_ok P c). destr_factor. Esimpl.
 - now rewrite <- jump_add, Pos.sub_add.
 - assert (H2 := Mcphi_ok P2 c). assert (H3 := Mcphi_ok P3 c).
   destr_factor. Esimpl. add_permut.
 - rewrite zmon_pred_ok. simpl. add_permut.
 - rewrite mkZmon_ok. simpl. add_permut. mul_permut.
 - add_permut. mul_permut.
   rewrite <- pow_pos_add, Pos.add_comm, Pos.sub_add by trivial; rsimpl.
 - rewrite mkZmon_ok. simpl. Esimpl. add_permut. mul_permut.
   rewrite <- pow_pos_add, Pos.sub_add by trivial; rsimpl.
 Qed.

 Lemma POneSubst_ok P1 cM1 P2 P3 l :
   POneSubst P1 cM1 P2 = Some P3 ->
   [fst cM1] * (snd cM1)@@l == P2@l -> P1@l == P3@l.
 Proof.
 destruct cM1 as (cc,M1).
 unfold POneSubst.
 assert (H := Mphi_ok P1 (cc, M1) l). simpl in H.
 destruct MFactor as (R1,S1); simpl. rewrite H. clear H.
 intros EQ EQ'. replace P3 with (R1 ++ P2 ** S1).
 - rewrite EQ', Padd_ok, Pmul_ok; rsimpl.
 - revert EQ. destruct S1; try now injection 1.
   case ceqb_spec; now inversion 2.
 Qed.

 Lemma PNSubst1_ok n P1 cM1 P2 l :
   [fst cM1] * (snd cM1)@@l == P2@l ->
   P1@l == (PNSubst1 P1 cM1 P2 n)@l.
 Proof.
 revert P1. induction n; simpl; intros P1;
 generalize (POneSubst_ok P1 cM1 P2); destruct POneSubst;
   intros; rewrite <- ?IHn; auto; reflexivity.
 Qed.

 Lemma PNSubst_ok n P1 cM1 P2 l P3 :
   PNSubst P1 cM1 P2 n = Some P3 ->
   [fst cM1] * (snd cM1)@@l == P2@l -> P1@l == P3@l.
 Proof.
 unfold PNSubst.
 assert (H := POneSubst_ok P1 cM1 P2); destruct POneSubst; try discriminate.
 destruct n; inversion_clear 1.
 intros. rewrite <- PNSubst1_ok; auto.
 Qed.

 Fixpoint MPcond (LM1: list (C * Mon * Pol)) (l: list R) : Prop :=
   match LM1 with
   | (M1,P2) :: LM2 => ([fst M1] * (snd M1)@@l == P2@l) /\ MPcond LM2 l
   | _ => True
   end.

 Lemma PSubstL1_ok n LM1 P1 l :
   MPcond LM1 l -> P1@l == (PSubstL1 P1 LM1 n)@l.
 Proof.
 revert P1; induction LM1 as [|(M2,P2) LM2 IH]; simpl; intros. 
 - reflexivity. 
 - rewrite <- IH by intuition; now apply PNSubst1_ok.
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
  | PEO : PExpr
  | PEI : PExpr            
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
   | PEO => rO
   | PEI => rI
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

 Lemma mkX_ok p l : nth 0 p l == (mk_X p) @ l.
 Proof.
  destruct p;simpl;intros;Esimpl;trivial.
  - now rewrite <-jump_tl, nth_jump.
  - now rewrite <- nth_jump, nth_pred_double.
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
  Variable lmp:list (C*Mon*Pol).
  Let subst_l P := PNSubstL P lmp n n.
  Let Pmul_subst P1 P2 := subst_l (P1 ** P2).
  Let Ppow_subst := Ppow_N subst_l.

  Fixpoint norm_aux (pe:PExpr) : Pol :=
   match pe with
   | PEO => Pc cO
   | PEI => Pc cI
   | PEc c => Pc c
   | PEX j => mk_X j
   | PEadd (PEopp pe1) pe2 => (norm_aux pe2) -- (norm_aux pe1)
   | PEadd pe1 (PEopp pe2) => (norm_aux pe1) -- (norm_aux pe2)
   | PEadd pe1 pe2 => (norm_aux pe1) ++ (norm_aux pe2)
   | PEsub pe1 pe2 => (norm_aux pe1) -- (norm_aux pe2)
   | PEmul pe1 pe2 => (norm_aux pe1) ** (norm_aux pe2)
   | PEopp pe1 => -- (norm_aux pe1)
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
  destruct pe1; [ | | | | | | | reflexivity | ];
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

  Arguments norm_aux !pe : simpl nomatch.

  Lemma norm_aux_spec l pe :
    PEeval l pe == (norm_aux pe)@l.
  Proof.
   intros.
   induction pe; cbn.
   - now rewrite (morph0 CRmorph). 
   - now rewrite (morph1 CRmorph).
   - reflexivity.
   - apply mkX_ok.
   - rewrite IHpe1, IHpe2.
     assert (H1 := norm_aux_PEopp pe1).
     assert (H2 := norm_aux_PEopp pe2).
     rewrite norm_aux_PEadd.
     do 2 destruct get_PEopp; rewrite ?H1, ?H2; Esimpl; add_permut.
   - rewrite IHpe1, IHpe2. Esimpl.
   - rewrite IHpe1, IHpe2. now rewrite Pmul_ok.
   - rewrite IHpe. Esimpl.
   - rewrite Ppow_N_ok by reflexivity.
     rewrite pow_th.(rpow_pow_N). destruct n0; simpl; Esimpl.
     induction p;simpl; now rewrite ?IHp, ?IHpe, ?Pms_ok, ?Pmul_ok.
  Qed.

 Lemma norm_subst_spec :
     forall l pe, MPcond lmp l ->
       PEeval l pe == (norm_subst pe)@l.
 Proof.
  intros;unfold norm_subst.
  unfold subst_l;rewrite <- PNSubstL_ok;trivial. apply norm_aux_spec.
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
     let lm := add_pow_list (hd fv) n lm in
     mkadd_mult rP c lm
   | Pinj j Q =>
     add_mult_dev rP Q (jump j fv) N0 (add_pow_list (hd fv) n lm)
   | PX P i Q =>
     let rP := add_mult_dev rP P fv (N.add (Npos i) n) lm in
     if Q ?== P0 then rP
     else add_mult_dev rP Q (tail fv) N0 (add_pow_list (hd fv) n lm)
   end.

  Fixpoint mult_dev (P:Pol) (fv : list R) (n:N)
                     (lm:list (R*positive)) {struct P} : R :=
  (* P@l * (hd 0 l)^n * lm *)
  match P with
  | Pc c => mkmult_c c (add_pow_list (hd fv) n lm)
  | Pinj j Q => mult_dev Q (jump j fv) N0 (add_pow_list (hd fv) n lm)
  | PX P i Q =>
     let rP := mult_dev P fv (N.add (Npos i) n) lm in
     if Q ?== P0 then rP
     else
       let lmq := add_pow_list (hd fv) n lm in
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
   rewrite (ARmul_comm ARth (pow_pos rmul r p)). reflexivity.
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
    add_mult_dev rP P fv n lm == rP + P@fv*pow_N rI rmul (hd fv) n * r_list_pow lm.
  Proof.
    induction P;simpl;intros.
    rewrite mkadd_mult_ok. rewrite add_pow_list_ok; Esimpl.
    rewrite IHP. simpl. rewrite add_pow_list_ok; Esimpl.
    change (match P3 with
       | Pc c => c ?=! cO
       | Pinj _ _ => false
       | PX _ _ _ => false
       end) with (Peq P3 P0).
   change match n with
    | N0 => Npos p
    | Npos q => Npos (p + q)
    end with (N.add (Npos p) n);trivial.
   assert (H := Peq_ok P3 P0).
    destruct (P3 ?== P0).
    rewrite (H eq_refl).
   rewrite IHP1. destruct n;simpl;Esimpl;rewrite pow_pos_add;Esimpl.
   add_permut. mul_permut.
   rewrite IHP2.
   rewrite IHP1. destruct n;simpl;Esimpl;rewrite pow_pos_add;Esimpl.
   add_permut. mul_permut.
 Qed.

 Lemma mult_dev_ok : forall P fv n lm,
    mult_dev P fv n lm == P@fv * pow_N rI rmul (hd fv) n * r_list_pow lm.
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
    end with (N.add (Npos p) n);trivial.
   assert (H := Peq_ok P3 P0).
    destruct (P3 ?== P0).
    rewrite (H eq_refl).
   rewrite  IHP1. destruct n;simpl;Esimpl;rewrite pow_pos_add;Esimpl.
   mul_permut.
   rewrite add_mult_dev_ok. rewrite IHP1; rewrite add_pow_list_ok.
   destruct n;simpl;Esimpl;rewrite pow_pos_add;Esimpl.
   add_permut; mul_permut.
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

 Lemma local_mkpow_ok r p :
    match p with
    | xI _ => rpow r (Cp_phi (Npos p))
    | xO _ => rpow r (Cp_phi (Npos p))
    | 1 => r
    end == pow_pos rmul r p.
 Proof. destruct p; now rewrite ?pow_th.(rpow_pow_N). Qed.

 Lemma Pphi_pow_ok : forall P fv, Pphi_pow fv P  == P@fv.
 Proof.
  unfold Pphi_pow;intros;apply Pphi_avoid_ok;intros;
   now rewrite ?local_mkpow_ok.
 Qed.

 Lemma ring_rw_pow_correct : forall n lH l,
      interp_PElist l lH ->
      forall lmp, mk_monpol_list lH = lmp ->
      forall pe npe, norm_subst n lmp pe = npe ->
      PEeval l pe == Pphi_pow l npe.
 Proof.
  intros n lH l H1 lmp Heq1 pe npe Heq2.
  rewrite Pphi_pow_ok, <- Heq2, <- Heq1.
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
    | xO p => mkmult_pow x x (Pos.pred_double p)
    | xI p => mkmult_pow x x (xO p)
    end.

  Definition mkopp_pow x p :=
    match p with
    | xH => -x
    | xO p => mkmult_pow (-x) x (Pos.pred_double p)
    | xI p => mkmult_pow (-x) x (xO p)
    end.

  Definition Pphi_dev := Pphi_avoid mkpow mkopp_pow mkmult_pow.

  Lemma mkmult_pow_ok p r x : mkmult_pow r x p == r * x^p.
  Proof.
    revert r; induction p;intros;simpl;Esimpl;rewrite !IHp;Esimpl.
  Qed.

 Lemma mkpow_ok p x : mkpow x p == x^p.
  Proof.
    destruct p;simpl;intros;Esimpl.
    - rewrite !mkmult_pow_ok;Esimpl.
    - rewrite mkmult_pow_ok;Esimpl.
      change x with (x^1) at 1.
      now rewrite <- pow_pos_add, Pos.add_1_r, Pos.succ_pred_double.
  Qed.

  Lemma mkopp_pow_ok p x : mkopp_pow x p == - x^p.
  Proof.
    destruct p;simpl;intros;Esimpl.
    - rewrite !mkmult_pow_ok;Esimpl.
    - rewrite mkmult_pow_ok;Esimpl.
      change x with (x^1) at 1.
      now rewrite <- pow_pos_add, Pos.add_1_r, Pos.succ_pred_double.
  Qed.

 Lemma Pphi_dev_ok : forall P fv, Pphi_dev fv P == P@fv.
  Proof.
   unfold Pphi_dev;intros;apply Pphi_avoid_ok.
   - intros;apply mkpow_ok.
   - intros;apply mkopp_pow_ok.
   - intros;apply mkmult_pow_ok.
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

Arguments PEO [C].
Arguments PEI [C].
