Set Implicit Arguments.
Require Import Setoid.
Require Export BinList.
Require Import BinPos.
Require Import BinInt.
Require Export Ring_th.

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
  Add Morphism radd : radd_ext.  exact Reqe.(Radd_ext). Qed.
  Add Morphism rmul : rmul_ext.  exact Reqe.(Rmul_ext). Qed.
  Add Morphism ropp : ropp_ext.  exact Reqe.(Ropp_ext). Qed.
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
 
 (** Evaluation of a polynomial towards R *)

 Fixpoint pow (x:R) (i:positive) {struct i}: R :=
  match i with
  | xH => x
  | xO i => let p := pow x i in p * p
  | xI i => let p := pow x i in x * p * p
  end.

 Fixpoint Pphi(l:list R) (P:Pol) {struct P} : R :=
  match P with
  | Pc c => [c]
  | Pinj j Q => Pphi (jump j l) Q
  | PX P i Q => 
     let x := hd 0 l in
     let xi := pow x i in
    (Pphi l P) * xi + (Pphi (tl l) Q)      
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
  apply CRmorph.(morph_eq);trivial.
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
  intros;simpl;apply CRmorph.(morph0).
 Qed.

 Lemma Pphi1 : forall l,  P1@l == 1.
 Proof.
  intros;simpl;apply CRmorph.(morph1).
 Qed.

 Lemma mkPinj_ok : forall j l P, (mkPinj j P)@l == P@(jump j l).
 Proof.
  intros j l p;destruct p;simpl;rsimpl.
  rewrite <-jump_Pplus;rewrite Pplus_comm;rrefl.
 Qed.

 Lemma mkPX_ok : forall l P i Q, 
  (mkPX P i Q)@l == P@l*(pow (hd 0 l) i) + Q@(tl l).
 Proof.
  intros l P i Q;unfold mkPX.
  destruct P;try (simpl;rrefl).
  assert (H := @CRmorph.(morph_eq) c cO);destruct (c ?=! cO);simpl;try rrefl.
  rewrite (H (refl_equal true));rewrite CRmorph.(morph0).
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
   | |- context [[cO]] => rewrite CRmorph.(morph0)
   | |- context [[cI]] => rewrite CRmorph.(morph1)
   | |- context [[?x +! ?y]] => rewrite (CRmorph.(morph_add) x y)
   | |- context [[?x *! ?y]] => rewrite (CRmorph.(morph_mul) x y)
   | |- context [[?x -! ?y]] => rewrite (CRmorph.(morph_sub) x y)
   | |- context [[-! ?x]] => rewrite (CRmorph.(morph_opp) x)
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
  assert (H:= @CRmorph.(morph_eq) c cO);destruct (c ?=! cO).
  rewrite (H (refl_equal true));Esimpl.
  assert (H1:= @CRmorph.(morph_eq) c cI);destruct (c ?=! cI).
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
  Esimpl2;apply ARth.(ARadd_sym).
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
  rewrite IHP'2;rsimpl. add_push (P @ (tl l));rrefl.
  assert (H := ZPminus_spec p0 p);destruct (ZPminus p0 p);Esimpl2.
  rewrite IHP'1;rewrite IHP'2;rsimpl.
  add_push (P3 @ (tl l));rewrite H;rrefl.
  rewrite IHP'1;rewrite IHP'2;simpl;Esimpl.
  rewrite H;rewrite Pplus_comm.
  rewrite pow_Pplus;rsimpl.
  add_push (P3 @ (tl l));rrefl.
  assert (forall P k l, 
           (PaddX Padd P'1 k P) @ l == P@l + P'1@l * pow (hd 0 l) k).
   induction P;simpl;intros;try apply ARth.(ARadd_sym).
   destruct p2;simpl;try apply ARth.(ARadd_sym).
   rewrite jump_Pdouble_minus_one;apply ARth.(ARadd_sym).
    assert (H1 := ZPminus_spec p2 k);destruct (ZPminus p2 k);Esimpl2.
    rewrite IHP'1;rsimpl; rewrite H1;add_push (P5 @ (tl l0));rrefl.
    rewrite IHP'1;simpl;Esimpl.
    rewrite H1;rewrite Pplus_comm.
    rewrite pow_Pplus;simpl;Esimpl.
    add_push (P5 @ (tl l0));rrefl.
    rewrite IHP1;rewrite H1;rewrite Pplus_comm.
    rewrite pow_Pplus;simpl;rsimpl.
    add_push (P5 @ (tl l0));rrefl.
  rewrite H0;rsimpl.
  add_push (P3 @ (tl l)).
  rewrite H;rewrite Pplus_comm.
  rewrite IHP'2;rewrite pow_Pplus;rsimpl.
  add_push (P3 @ (tl l));rrefl.
 Qed.

 Lemma Psub_ok : forall P' P l, (P -- P')@l == P@l - P'@l.
 Proof.
  induction P';simpl;intros;Esimpl2;trivial.
  generalize P p l;clear P p l.
  induction P;simpl;intros.
  Esimpl2;apply ARth.(ARadd_sym).
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
  add_push (P @ (jump p0 (jump p0 (tl l))));rrefl.
  rewrite IHP'2;simpl;rewrite jump_Pdouble_minus_one;rsimpl.
  add_push (- (P'1 @ l * pow (hd 0 l) p));rrefl.
  rewrite IHP'2;rsimpl;add_push (P @ (tl l));rrefl.
  assert (H := ZPminus_spec p0 p);destruct (ZPminus p0 p);Esimpl2.
  rewrite IHP'1; rewrite IHP'2;rsimpl.
  add_push (P3 @ (tl l));rewrite H;rrefl.
   rewrite IHP'1; rewrite IHP'2;rsimpl;simpl;Esimpl.
  rewrite H;rewrite Pplus_comm.
  rewrite pow_Pplus;rsimpl.
  add_push (P3 @ (tl l));rrefl.
  assert (forall P k l, 
           (PsubX Psub P'1 k P) @ l == P@l + - P'1@l * pow (hd 0 l) k).
   induction P;simpl;intros.
   rewrite Popp_ok;rsimpl;apply ARth.(ARadd_sym);trivial.
   destruct p2;simpl;rewrite Popp_ok;rsimpl.
   apply ARth.(ARadd_sym);trivial.
   rewrite jump_Pdouble_minus_one;apply ARth.(ARadd_sym);trivial.
   apply ARth.(ARadd_sym);trivial.
    assert (H1 := ZPminus_spec p2 k);destruct (ZPminus p2 k);Esimpl2;rsimpl.
    rewrite IHP'1;rsimpl;add_push (P5 @ (tl l0));rewrite H1;rrefl.
    rewrite IHP'1;rewrite H1;rewrite Pplus_comm.
    rewrite pow_Pplus;simpl;Esimpl.
    add_push (P5 @ (tl l0));rrefl.
    rewrite IHP1;rewrite H1;rewrite Pplus_comm.
    rewrite pow_Pplus;simpl;rsimpl.
    add_push (P5 @ (tl l0));rrefl.
  rewrite H0;rsimpl.
  rewrite IHP'2;rsimpl;add_push (P3 @ (tl l)).
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
  Esimpl2;apply ARth.(ARmul_sym).
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
  Esimpl2;apply ARth.(ARmul_sym).
  rewrite (PmulI_ok P (Pmul_aux_ok P)).
  apply ARth.(ARmul_sym).
  rewrite Padd_ok; Esimpl2.
  rewrite (PmulI_ok P3 (Pmul_aux_ok P3));trivial.
  rewrite Pmul_aux_ok;mul_push (P' @ l).
  rewrite (ARmul_sym ARth (P' @ l));rrefl.
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
  end;Esimpl2;try rrefl;try apply ARth.(ARadd_sym).

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
  | Pc c => if c ?=! cI then mkadd_mult rP (rev lm) 
    else mkadd_mult rP (cons [c] (rev lm))
  | Pinj j Q => add_mult_dev rP Q (jump j fv) lm
  | PX P i Q => 
     let rP := add_mult_dev rP P fv (powl i (hd 0 fv) lm) in
     if Q ?== P0 then rP else add_mult_dev rP Q (tl fv) lm
  end.
 
 Definition mkmult1 lm :=
  match lm with
  | nil => rI
  | cons h t => mkmult h t
  end.
    
 Fixpoint mult_dev (P:Pol) (fv lm : list R) {struct P} : R :=
  (* P@l * lm *)							      
  match P with
  | Pc c => if c ?=! cI then mkmult1 (rev lm) else mkmult [c] (rev lm)
  | Pinj j Q => mult_dev Q (jump j fv) lm
  | PX P i Q => 
     let rP := mult_dev P fv (powl i (hd 0 fv) lm) in
     if Q ?== P0 then rP else add_mult_dev rP Q (tl fv) lm
  end. 

 Definition Pphi_dev fv P := mult_dev P fv (nil R).

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
  mkmult r (rev_append l lm) == mkmult (mkmult r l) lm.
 Proof.
 induction lm; simpl in |- *; intros.
 rrefl.
 rewrite IHlm; simpl in |- *.
   repeat rewrite <- (ARmul_sym ARth a); rewrite <- mul_mkmult.
   rrefl.
 Qed.

 Lemma powl_mkmult_rev : forall p r x lm,
  mkmult r (rev (powl p x lm)) == mkmult (pow x p * r) (rev lm).
 Proof.
  induction p;simpl;intros.
  repeat rewrite IHp.
  unfold rev;simpl.
  repeat rewrite mkmult_rev_append.
  simpl.
  setoid_replace (pow x p * (pow x p * r) * x) 
    with (x * pow x p * pow x p * r);Esimpl.
  mul_push x;rrefl.
  repeat rewrite IHp.
  setoid_replace (pow x p * (pow x p * r) ) 
    with (pow x p * pow x p * r);Esimpl.
  unfold rev;simpl. repeat rewrite mkmult_rev_append;simpl.
  rewrite ARth.(ARmul_sym);rrefl.
 Qed.

 Lemma Pphi_add_mult_dev : forall P rP fv lm, 
    rP + P@fv * mkmult1 (rev lm) == add_mult_dev rP P fv lm.
 Proof.
  induction P;simpl;intros.
  assert (H := CRmorph.(morph_eq) c cI).
   destruct (c ?=! cI).
    rewrite (H (refl_equal true));rewrite CRmorph.(morph1);Esimpl.
    destruct (rev lm);Esimpl;rrefl.
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
	 P@fv * mkmult1 (rev lm) == mult_dev P fv lm.
 Proof.
  induction P;simpl;intros.
   assert (H := CRmorph.(morph_eq) c cI).
   destruct (c ?=! cI).
    rewrite (H (refl_equal true));rewrite CRmorph.(morph1);Esimpl.
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

 Lemma Pphi_dev_ok :  forall l pe,  PEeval l pe == Pphi_dev l (norm pe).
 Proof.
  intros l pe;rewrite <- Pphi_Pphi_dev;apply norm_ok.
 Qed.

 Lemma Pphi_dev_ok' :
   forall l pe npe, norm pe = npe -> PEeval l pe == Pphi_dev l npe.
 Proof.
  intros l pe npe npe_eq; subst npe; apply Pphi_dev_ok.
 Qed.
 
(* The same but building a PExpr *)
(*
 Fixpoint Pmkmult (r:PExpr) (lm:list PExpr) {struct lm}: PExpr :=
  match lm with
  | nil => r
  | cons h t => Pmkmult (PEmul r h) t
  end.
		       
 Definition Pmkadd_mult rP lm :=
  match lm with
  | nil => PEadd rP (PEc cI)
  | cons h t => PEadd rP (Pmkmult h t)
  end.

 Fixpoint Ppowl (i:positive) (x:PExpr) (l:list PExpr) {struct i}: list PExpr :=
  match i with
  | xH => cons x l
  | xO i => Ppowl i x (Ppowl i x l)
  | xI i => Ppowl i x (Ppowl i x (cons x l))
  end.
			       
 Fixpoint Padd_mult_dev
     (rP:PExpr) (P:Pol) (fv lm:list PExpr) {struct P} : PExpr :=
  (* rP + P@l * lm *)
  match P with
  | Pc c => if c ?=! cI then Pmkadd_mult rP (rev lm) 
    else Pmkadd_mult rP (cons [PEc c] (rev lm))
  | Pinj j Q => Padd_mult_dev rP Q (jump j fv) lm
  | PX P i Q => 
     let rP := Padd_mult_dev rP P fv (Ppowl i (hd P0 fv) lm) in
     if Q ?== P0 then rP else Padd_mult_dev rP Q (tl fv) lm
  end.
 
 Definition Pmkmult1 lm :=
  match lm with
  | nil => PEc cI
  | cons h t => Pmkmult h t
  end.
   
 Fixpoint Pmult_dev (P:Pol) (fv lm : list PExpr) {struct P} : PExpr :=
  (* P@l * lm *)							      
  match P with
  | Pc c => if c ?=! cI then Pmkmult1 (rev lm) else Pmkmult [PEc c] (rev lm)
  | Pinj j Q => Pmult_dev Q (jump j fv) lm
  | PX P i Q => 
     let rP := Pmult_dev P fv (Ppowl i (hd (PEc r0) fv) lm) in
     if Q ?== P0 then rP else Padd_mult_dev rP Q (tl fv) lm
  end. 

 Definition Pphi_dev2 fv P := Pmult_dev P fv (nil PExpr).

...
*)
  (************************************************)
 (* avec des parentheses mais un peu plus efficace *)


 (**************************************************

  Fixpoint pow_mult (i:positive) (x r:R){struct i}:R :=
  match i with
  | xH => r * x
  | xO i => pow_mult i x (pow_mult i x r)
  | xI i => pow_mult i x (pow_mult i x (r * x))
  end.
 
 Definition pow_dev i x :=
  match i with
  | xH => x
  | xO i => pow_mult (Pdouble_minus_one i) x x
  | xI i => pow_mult (xO i) x x
  end.

 Lemma pow_mult_pow : forall i x r, pow_mult i x r == pow x i * r.
 Proof.
  induction i;simpl;intros.
  rewrite (IHi x (pow_mult i x (r * x)));rewrite (IHi x (r*x));rsimpl.
  mul_push x;rrefl.
  rewrite (IHi x (pow_mult i x r));rewrite (IHi x r);rsimpl.
  apply ARth.(ARmul_sym).
 Qed.

 Lemma pow_dev_pow : forall p x, pow_dev p x == pow x p.
 Proof.
  destruct p;simpl;intros.
  rewrite (pow_mult_pow p x (pow_mult p x x)).
  rewrite (pow_mult_pow p x x);rsimpl;mul_push x;rrefl.
  rewrite (pow_mult_pow (Pdouble_minus_one p) x x).
  rewrite (ARth.(ARmul_sym) (pow x (Pdouble_minus_one p)) x).
  rewrite <- (pow_Psucc x (Pdouble_minus_one p)).
  rewrite Psucc_o_double_minus_one_eq_xO;simpl; rrefl.
  rrefl.
 Qed.

 Fixpoint Pphi_dev (fv:list R) (P:Pol) {struct P} : R :=
  match P with
  | Pc c => [c]
  | Pinj j Q => Pphi_dev (jump j fv) Q
  | PX P i Q => 
    let rP := mult_dev P fv (pow_dev i (hd 0 fv)) in
    add_dev rP Q (tl fv)
  end

 with add_dev (ra:R) (P:Pol) (fv:list R) {struct P} : R :=
   match P with
  | Pc c => if c ?=! cO then ra else ra + [c] 
  | Pinj j Q => add_dev ra Q (jump j fv)
  | PX P i Q =>
    let ra := add_mult_dev ra P fv (pow_dev i (hd 0 fv)) in
    add_dev ra Q (tl fv)
  end
 
 with mult_dev (P:Pol) (fv:list R) (rm:R) {struct P} : R :=
  match P with
  | Pc c => if c ?=! cI then rm else [c]*rm
  | Pinj j Q => mult_dev Q (jump j fv) rm
  | PX P i Q =>
    let ra := mult_dev P fv (pow_mult i (hd 0 fv) rm) in
    add_mult_dev ra Q (tl fv) rm
  end

 with add_mult_dev (ra:R) (P:Pol) (fv:list R) (rm:R) {struct P} : R :=
  match P with
  | Pc c =>  if c ?=! cO then ra else ra + [c]*rm
  | Pinj j Q => add_mult_dev ra Q (jump j fv) rm
  | PX P i Q =>
    let rmP := pow_mult i (hd 0 fv) rm in
    let raP := add_mult_dev ra P fv rmP in
    add_mult_dev raP Q (tl fv) rm
  end.
 
 Lemma Pphi_add_mult_dev : forall P ra fv rm,
    add_mult_dev ra P fv rm == ra + P@fv * rm.
 Proof.
  induction P;simpl;intros.
  assert (H := CRmorph.(morph_eq) c cO).
   destruct (c ?=! cO).
    rewrite (H (refl_equal true));rewrite CRmorph.(morph0);Esimpl.
    rrefl.
  apply IHP.
  rewrite (IHP2 (add_mult_dev ra P2 fv (pow_mult p (hd 0 fv) rm)) (tl fv) rm).
  rewrite (IHP1 ra fv (pow_mult p (hd 0 fv) rm)).
  rewrite (pow_mult_pow p (hd 0 fv) rm);rsimpl.
 Qed.
  
 Lemma Pphi_add_dev : forall P ra fv, add_dev ra P fv == ra + P@fv.
 Proof.
  induction P;simpl;intros.
  assert (H := CRmorph.(morph_eq) c cO).
   destruct (c ?=! cO).
    rewrite (H (refl_equal true));rewrite CRmorph.(morph0);Esimpl.
    rrefl.
  apply IHP.
  rewrite (IHP2 (add_mult_dev ra P2 fv (pow_dev p (hd 0 fv))) (tl fv)).
  rewrite (Pphi_add_mult_dev P2 ra fv (pow_dev p (hd 0 fv))).
  rewrite  (pow_dev_pow p (hd 0 fv));rsimpl. 
 Qed.

 Lemma Pphi_mult_dev : forall P fv rm, mult_dev P fv rm == P@fv * rm.
 Proof.
  induction P;simpl;intros.
  assert (H := CRmorph.(morph_eq) c cI).
   destruct (c ?=! cI).
    rewrite (H (refl_equal true));rewrite CRmorph.(morph1);Esimpl.
    rrefl.
  apply IHP.
  rewrite (Pphi_add_mult_dev P3 
	    (mult_dev P2 fv (pow_mult p (hd 0 fv) rm)) (tl fv) rm).
  rewrite (IHP1 fv  (pow_mult p (hd 0 fv) rm)).
  rewrite (pow_mult_pow p (hd 0 fv) rm);rsimpl.
 Qed.

 Lemma Pphi_Pphi_dev : forall P fv, P@fv == Pphi_dev fv P.
 Proof.
  induction P;simpl;intros.
  rrefl. trivial.
  rewrite (Pphi_add_dev P3 (mult_dev P2 fv (pow_dev p (hd 0 fv))) (tl fv)).
  rewrite (Pphi_mult_dev P2 fv (pow_dev p (hd 0 fv))).
  rewrite (pow_dev_pow p (hd 0 fv));rsimpl.
 Qed.

 Lemma Pphi_dev_ok :  forall l pe,  PEeval l pe == Pphi_dev l (norm pe).
 Proof.
  intros l pe;rewrite <- (Pphi_Pphi_dev (norm pe) l);apply norm_ok.
 Qed.

 Ltac Trev l :=  
  let rec rev_append rev l :=
   match l with
   | (nil _) => constr:(rev)
   | (cons ?h ?t) => let rev := constr:(cons h rev) in rev_append rev t 
   end in
 rev_append (nil R) l.

 Ltac TPphi_dev add mul :=
  let tl l := match l with (cons ?h ?t) => constr:(t) end in
  let rec jump j l :=
   match j with
   | xH => tl l
   | (xO ?j) => let l := jump j l in jump j l
   | (xI ?j) => let t := tl l in let l := jump j l in jump j l
   end in
  let rec pow_mult i x r :=
   match i with
   | xH => constr:(mul r x)
   | (xO ?i) => let r := pow_mult i x r in pow_mult i x r
   | (xI ?i) => 
     let r := constr:(mul r x) in
     let r := pow_mult i x r in 
     pow_mult i x r
   end in
  let pow_dev i x :=
   match i with
   | xH => x
   | (xO ?i) => 
      let i := eval compute in (Pdouble_minus_one i) in pow_mult i x x
   | (xI ?i) => pow_mult (xO i) x x
   end in
  let rec add_mult_dev ra P fv rm :=
   match P with
   | (Pc ?c) => 
     match eval compute in (c ?=! cO) with
     | true => constr:ra 
     | _ => let rc := eval compute in [c] in constr:(add ra (mul rc rm))
     end
   | (Pinj ?j ?Q) => 
     let fv := jump j fv in add_mult_dev ra Q fv rm
   | (PX ?P ?i ?Q) =>
     match fv with 
     | (cons ?hd ?tl) =>
       let rmP := pow_mult i hd rm in
       let raP := add_mult_dev ra P fv rmP in
       add_mult_dev raP Q tl rm
     end
   end in
  let rec mult_dev P fv rm :=
   match P with
   | (Pc ?c) =>
     match eval compute in (c ?=! cI) with
     | true => constr:rm 
     | false => let rc := eval compute in [c] in constr:(mul rc rm)
     end
   | (Pinj ?j ?Q) => let fv := jump j fv in mult_dev Q fv rm
   | (PX ?P ?i ?Q) =>
     match fv with
     | (cons ?hd ?tl) =>
       let rmP := pow_mult i hd rm in
       let ra := mult_dev P fv rmP in
       add_mult_dev ra Q tl rm
     end
   end in
  let rec add_dev ra P fv :=
   match P with
   | (Pc ?c) =>
     match eval compute in (c ?=! cO) with
     | true => ra
     | false => let rc := eval compute in [c] in constr:(add ra rc)
     end
   | (Pinj ?j ?Q) => let fv := jump j fv in add_dev ra Q fv
   | (PX ?P ?i ?Q) =>
     match fv with
     | (cons ?hd ?tl) =>
       let rmP := pow_dev i hd in
       let ra := add_mult_dev ra P fv rmP in
       add_dev ra Q tl
     end
   end in
  let rec Pphi_dev fv P :=
   match P with
   | (Pc ?c) => eval compute in [c]
   | (Pinj ?j ?Q) => let fv := jump j fv in Pphi_dev fv Q
   | (PX ?P ?i ?Q) =>
     match fv with
     | (cons ?hd ?tl) =>
       let rm := pow_dev i hd in
       let rP := mult_dev P fv rm in
       add_dev rP Q tl
     end
   end in
  Pphi_dev.
 
 **************************************************************)

End MakeRingPol. 
