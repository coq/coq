(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import ZArith_base.
Require Import Zpow_def.
Require Import BinInt.
Require Import BinNat.
Require Import Setoid.
Require Import Ring_theory.
Require Import Ring_polynom.
Require Import ZOdiv_def.
Import List.

Set Implicit Arguments.

Import RingSyntax.

(* An object to return when an expression is not recognized as a constant *)
Definition NotConstant := false.

(** Z is a ring and a setoid*)

Lemma Zsth : Setoid_Theory Z (@eq Z).
Proof (Eqsth Z).
 
Lemma Zeqe : ring_eq_ext Zplus Zmult Zopp (@eq Z).
Proof (Eq_ext Zplus Zmult Zopp).

Lemma Zth : ring_theory Z0 (Zpos xH) Zplus Zmult Zminus Zopp (@eq Z).
Proof.
 constructor. exact Zplus_0_l. exact Zplus_comm. exact Zplus_assoc.
 exact Zmult_1_l. exact Zmult_comm. exact Zmult_assoc.
 exact Zmult_plus_distr_l. trivial. exact Zminus_diag.
Qed.

 Lemma Zeqb_ok : forall x y, Zeq_bool x y = true -> x = y.
 Proof.
  intros x y.
  assert (H := Zcompare_Eq_eq x y);unfold Zeq_bool;
  destruct (Zcompare x y);intros H1;auto;discriminate H1.
 Qed.


(** Two generic morphisms from Z to (abrbitrary) rings, *)
(**second one is more convenient for proofs but they are ext. equal*)
Section ZMORPHISM.
 Variable R : Type.
 Variable (rO rI : R) (radd rmul rsub: R->R->R) (ropp : R -> R).
 Variable req : R -> R -> Prop.
  Notation "0" := rO.  Notation "1" := rI.
  Notation "x + y" := (radd x y).  Notation "x * y " := (rmul x y).
  Notation "x - y " := (rsub x y).  Notation "- x" := (ropp x).
  Notation "x == y" := (req x y).
  Variable Rsth : Setoid_Theory R req.
     Add Setoid R req Rsth as R_setoid3.
     Ltac rrefl := gen_reflexivity Rsth.
 Variable Reqe : ring_eq_ext radd rmul ropp req.
   Add Morphism radd : radd_ext3.  exact (Radd_ext Reqe). Qed.
   Add Morphism rmul : rmul_ext3.  exact (Rmul_ext Reqe). Qed.
   Add Morphism ropp : ropp_ext3.  exact (Ropp_ext Reqe). Qed.

 Fixpoint gen_phiPOS1 (p:positive) : R :=
  match p with
  | xH => 1
  | xO p => (1 + 1) * (gen_phiPOS1 p)
  | xI p => 1 + ((1 + 1) * (gen_phiPOS1 p))
  end.

 Fixpoint gen_phiPOS (p:positive) : R :=
  match p with
  | xH => 1 
  | xO xH => (1 + 1)
  | xO p => (1 + 1) * (gen_phiPOS p)
  | xI xH => 1 + (1 +1)
  | xI p => 1 + ((1 + 1) * (gen_phiPOS p))
  end.

 Definition gen_phiZ1 z :=
  match z with
  | Zpos p => gen_phiPOS1 p
  | Z0 => 0
  | Zneg p => -(gen_phiPOS1 p)
  end.
 
 Definition gen_phiZ z := 
  match z with
  | Zpos p => gen_phiPOS p
  | Z0 => 0
  | Zneg p => -(gen_phiPOS p)
  end.
 Notation "[ x ]" := (gen_phiZ x).   

 Definition get_signZ z :=
  match z with
  | Zneg p => Some (Zpos p) 
  | _ => None
  end.

 Lemma get_signZ_th : sign_theory Zopp Zeq_bool get_signZ.
 Proof.
  constructor.
  destruct c;intros;try discriminate.
  injection H;clear H;intros H1;subst c'.
  simpl. unfold Zeq_bool. rewrite Zcompare_refl. trivial.
 Qed.

 
 Section ALMOST_RING.
 Variable ARth : almost_ring_theory 0 1 radd rmul rsub ropp req.
   Add Morphism rsub : rsub_ext3. exact (ARsub_ext Rsth Reqe ARth). Qed.
   Ltac norm := gen_srewrite 0 1 radd rmul rsub ropp req Rsth Reqe ARth.
   Ltac add_push := gen_add_push radd Rsth Reqe ARth.
 
 Lemma same_gen : forall x, gen_phiPOS1 x == gen_phiPOS x.
 Proof.
  induction x;simpl. 
  rewrite IHx;destruct x;simpl;norm.
  rewrite IHx;destruct x;simpl;norm.
  rrefl.
 Qed.

 Lemma ARgen_phiPOS_Psucc : forall x,
   gen_phiPOS1 (Psucc x) == 1 + (gen_phiPOS1 x).
 Proof.
  induction x;simpl;norm.
  rewrite IHx;norm.
  add_push 1;rrefl.
 Qed.

 Lemma ARgen_phiPOS_add : forall x y,
   gen_phiPOS1 (x + y) == (gen_phiPOS1 x) + (gen_phiPOS1 y).
 Proof.
  induction x;destruct y;simpl;norm.
  rewrite Pplus_carry_spec.
  rewrite ARgen_phiPOS_Psucc.
  rewrite IHx;norm.
  add_push (gen_phiPOS1 y);add_push 1;rrefl.
  rewrite IHx;norm;add_push (gen_phiPOS1 y);rrefl.
  rewrite ARgen_phiPOS_Psucc;norm;add_push 1;rrefl.
  rewrite IHx;norm;add_push(gen_phiPOS1 y); add_push 1;rrefl.
  rewrite IHx;norm;add_push(gen_phiPOS1 y);rrefl.
  add_push 1;rrefl.
  rewrite ARgen_phiPOS_Psucc;norm;add_push 1;rrefl.
 Qed.

 Lemma ARgen_phiPOS_mult :
   forall x y, gen_phiPOS1 (x * y) == gen_phiPOS1 x * gen_phiPOS1 y.
 Proof.
  induction x;intros;simpl;norm.
  rewrite ARgen_phiPOS_add;simpl;rewrite IHx;norm.
  rewrite IHx;rrefl.
 Qed.

 End ALMOST_RING.

 Variable Rth : ring_theory 0 1 radd rmul rsub ropp req.
 Let ARth := Rth_ARth Rsth Reqe Rth.
   Add Morphism rsub : rsub_ext4. exact (ARsub_ext Rsth Reqe ARth). Qed.
   Ltac norm := gen_srewrite 0 1 radd rmul rsub ropp req Rsth Reqe ARth.
   Ltac add_push := gen_add_push radd Rsth Reqe ARth.
  
(*morphisms are extensionaly equal*)
 Lemma same_genZ : forall x, [x] == gen_phiZ1 x.
 Proof.
  destruct x;simpl; try rewrite (same_gen ARth);rrefl.
 Qed.
 
 Lemma gen_Zeqb_ok : forall x y, 
   Zeq_bool x y = true -> [x] == [y].
 Proof.
  intros x y H.
  assert (H1 := Zeqb_ok x y H);unfold IDphi in H1.
  rewrite H1;rrefl.
 Qed.
  
 Lemma gen_phiZ1_add_pos_neg : forall x y,
 gen_phiZ1
    match (x ?= y)%positive Eq with
    | Eq => Z0
    | Lt => Zneg (y - x)
    | Gt => Zpos (x - y)
    end 
 == gen_phiPOS1 x + -gen_phiPOS1 y.
 Proof.
  intros x y.
  assert (H:= (Pcompare_Eq_eq x y)); assert (H0 := Pminus_mask_Gt x y).
  generalize (Pminus_mask_Gt y x).
  replace Eq with (CompOpp Eq);[intro H1;simpl|trivial].
  rewrite <- Pcompare_antisym in H1.
  destruct ((x ?= y)%positive Eq).
  rewrite H;trivial. rewrite (Ropp_def Rth);rrefl.
  destruct H1 as [h [Heq1 [Heq2 Hor]]];trivial.
  unfold Pminus; rewrite Heq1;rewrite <- Heq2.
  rewrite (ARgen_phiPOS_add ARth);simpl;norm.
  rewrite (Ropp_def Rth);norm.
  destruct H0 as [h [Heq1 [Heq2 Hor]]];trivial.
  unfold Pminus; rewrite Heq1;rewrite <- Heq2.
  rewrite (ARgen_phiPOS_add ARth);simpl;norm.
  add_push (gen_phiPOS1 h);rewrite (Ropp_def Rth); norm.
 Qed.

 Lemma match_compOpp : forall x (B:Type) (be bl bg:B),
  match CompOpp x with Eq => be | Lt => bl | Gt => bg end 
  = match x with Eq => be | Lt => bg | Gt => bl end.
 Proof. destruct x;simpl;intros;trivial. Qed.

 Lemma gen_phiZ_add : forall x y, [x + y] == [x] + [y].
 Proof.
  intros x y; repeat rewrite same_genZ; generalize x y;clear x y.
  induction x;destruct y;simpl;norm.
  apply (ARgen_phiPOS_add ARth).
  apply gen_phiZ1_add_pos_neg.
  replace Eq with (CompOpp Eq);trivial.
  rewrite <- Pcompare_antisym;simpl.
  rewrite match_compOpp.    
  rewrite (Radd_comm Rth).
  apply gen_phiZ1_add_pos_neg.
  rewrite (ARgen_phiPOS_add ARth); norm.
 Qed.

 Lemma gen_phiZ_mul : forall x y, [x * y] == [x] * [y].
 Proof.
  intros x y;repeat rewrite same_genZ.
  destruct x;destruct y;simpl;norm;
  rewrite  (ARgen_phiPOS_mult ARth);try (norm;fail).
  rewrite (Ropp_opp Rsth Reqe Rth);rrefl.
 Qed.

 Lemma gen_phiZ_ext : forall x y : Z, x = y -> [x] == [y].
 Proof. intros;subst;rrefl. Qed.

(*proof that [.] satisfies morphism specifications*)
 Lemma gen_phiZ_morph : 
  ring_morph 0 1 radd rmul rsub ropp req Z0 (Zpos xH) 
   Zplus Zmult Zminus Zopp Zeq_bool gen_phiZ.
 Proof. 
  assert ( SRmorph : semi_morph 0 1 radd rmul req Z0 (Zpos xH) 
                  Zplus Zmult Zeq_bool gen_phiZ).
   apply mkRmorph;simpl;try rrefl.
   apply gen_phiZ_add.  apply gen_phiZ_mul. apply gen_Zeqb_ok.
  apply  (Smorph_morph Rsth Reqe Rth Zsth Zth SRmorph gen_phiZ_ext).
 Qed.

End ZMORPHISM.

(** N is a semi-ring and a setoid*)
Lemma Nsth : Setoid_Theory N (@eq N).
Proof (Eqsth N).

Lemma Nseqe : sring_eq_ext Nplus Nmult (@eq N).
Proof (Eq_s_ext Nplus Nmult).

Lemma Nth : semi_ring_theory N0 (Npos xH) Nplus Nmult (@eq N).
Proof.
 constructor. exact Nplus_0_l. exact Nplus_comm. exact Nplus_assoc.
 exact Nmult_1_l. exact Nmult_0_l. exact Nmult_comm. exact Nmult_assoc.
 exact Nmult_plus_distr_r. 
Qed.

Definition Nsub := SRsub Nplus.
Definition Nopp := (@SRopp N).

Lemma Neqe : ring_eq_ext Nplus Nmult Nopp (@eq N).
Proof (SReqe_Reqe Nseqe).

Lemma Nath : 
 almost_ring_theory N0 (Npos xH) Nplus Nmult Nsub Nopp (@eq N).
Proof (SRth_ARth Nsth Nth).
 
Definition Neq_bool (x y:N) := 
  match Ncompare x y with
  | Eq => true
  | _ => false
  end.

Lemma Neq_bool_ok : forall x y, Neq_bool x y = true -> x = y.
 Proof.
  intros x y;unfold Neq_bool.
  assert (H:=Ncompare_Eq_eq x y); 
   destruct (Ncompare x y);intros;try discriminate.
  rewrite H;trivial. 
 Qed.

Lemma Neq_bool_complete : forall x y, Neq_bool x y = true -> x = y.
 Proof.
  intros x y;unfold Neq_bool.
  assert (H:=Ncompare_Eq_eq x y); 
   destruct (Ncompare x y);intros;try discriminate.
  rewrite H;trivial. 
 Qed.

(**Same as above : definition of two,extensionaly equal, generic morphisms *)
(**from N to any semi-ring*)
Section NMORPHISM.
 Variable R : Type.
 Variable  (rO rI : R) (radd rmul: R->R->R).
 Variable req : R -> R -> Prop.
  Notation "0" := rO.  Notation "1" := rI.
  Notation "x + y" := (radd x y).  Notation "x * y " := (rmul x y).
 Variable Rsth : Setoid_Theory R req.
     Add Setoid R req Rsth as R_setoid4.
     Ltac rrefl := gen_reflexivity Rsth.
 Variable SReqe : sring_eq_ext radd rmul req.
 Variable SRth : semi_ring_theory 0 1 radd rmul req. 
 Let ARth := SRth_ARth Rsth SRth.
 Let Reqe := SReqe_Reqe SReqe.
 Let ropp := (@SRopp R).
 Let rsub := (@SRsub R radd).
  Notation "x - y " := (rsub x y).  Notation "- x" := (ropp x).
  Notation "x == y" := (req x y).
   Add Morphism radd : radd_ext4.  exact (Radd_ext Reqe). Qed.
   Add Morphism rmul : rmul_ext4.  exact (Rmul_ext Reqe). Qed.
   Add Morphism ropp : ropp_ext4.  exact (Ropp_ext Reqe). Qed.
   Add Morphism rsub : rsub_ext5.  exact (ARsub_ext Rsth Reqe ARth). Qed.
   Ltac norm := gen_srewrite 0 1 radd rmul rsub ropp req Rsth Reqe ARth.
  
 Definition gen_phiN1 x :=
  match x with
  | N0 => 0
  | Npos x => gen_phiPOS1 1 radd rmul x
  end. 

 Definition gen_phiN x :=
  match x with
  | N0 => 0
  | Npos x => gen_phiPOS 1 radd rmul x
  end. 
 Notation "[ x ]" := (gen_phiN x).   
  
 Lemma same_genN : forall x, [x] == gen_phiN1 x.
 Proof.
  destruct x;simpl. rrefl.
  rewrite (same_gen Rsth Reqe ARth);rrefl.
 Qed.

 Lemma gen_phiN_add : forall x y, [x + y] == [x] + [y].
 Proof.
  intros x y;repeat rewrite same_genN.
  destruct x;destruct y;simpl;norm.
  apply (ARgen_phiPOS_add Rsth Reqe ARth).
 Qed.
 
 Lemma gen_phiN_mult : forall x y, [x * y] == [x] * [y].
 Proof.
  intros x y;repeat rewrite same_genN.
  destruct x;destruct y;simpl;norm.
  apply (ARgen_phiPOS_mult Rsth Reqe ARth).
 Qed.

 Lemma gen_phiN_sub : forall x y, [Nsub x y] == [x] - [y].
 Proof. exact gen_phiN_add. Qed.

(*gen_phiN satisfies morphism specifications*)
 Lemma gen_phiN_morph : ring_morph 0 1 radd rmul rsub ropp req
                           N0 (Npos xH) Nplus Nmult Nsub Nopp Neq_bool gen_phiN.
 Proof.
  constructor;intros;simpl; try rrefl.
  apply gen_phiN_add. apply gen_phiN_sub.  apply gen_phiN_mult.
  rewrite (Neq_bool_ok x y);trivial. rrefl.
 Qed.

End NMORPHISM.

(* Words on N : initial structure for almost-rings. *)
Definition Nword := list N.
Definition NwO : Nword := nil.
Definition NwI : Nword := 1%N :: nil.

Definition Nwcons n (w : Nword) : Nword :=
  match w, n with
  | nil, 0%N => nil
  | _, _ => n :: w
  end.

Fixpoint Nwadd (w1 w2 : Nword) {struct w1} : Nword :=
  match w1, w2 with
  | n1::w1', n2:: w2' => (n1+n2)%N :: Nwadd w1' w2'
  | nil, _ => w2
  | _, nil => w1
  end.

Definition Nwopp (w:Nword) : Nword := Nwcons 0%N w.

Definition Nwsub w1 w2 := Nwadd w1 (Nwopp w2).

Fixpoint Nwscal (n : N) (w : Nword) {struct w} : Nword :=
  match w with
  | m :: w' => (n*m)%N :: Nwscal n w'
  | nil => nil
  end.

Fixpoint Nwmul (w1 w2 : Nword) {struct w1} : Nword :=
  match w1 with
  | 0%N::w1' => Nwopp (Nwmul w1' w2)
  | n1::w1' => Nwsub (Nwscal n1 w2) (Nwmul w1' w2)
  | nil => nil
  end.
Fixpoint Nw_is0 (w : Nword) : bool :=
  match w with
  | nil => true
  | 0%N :: w' => Nw_is0 w'
  | _ => false
  end. 

Fixpoint Nweq_bool (w1 w2 : Nword) {struct w1} : bool :=
  match w1, w2 with
  | n1::w1', n2::w2' =>
     if Neq_bool n1 n2 then Nweq_bool w1' w2' else false
  | nil, _ => Nw_is0 w2
  | _, nil => Nw_is0 w1
  end.

Section NWORDMORPHISM.
 Variable R : Type.
 Variable (rO rI : R) (radd rmul rsub: R->R->R) (ropp : R -> R).
 Variable req : R -> R -> Prop.
  Notation "0" := rO.  Notation "1" := rI.
  Notation "x + y" := (radd x y).  Notation "x * y " := (rmul x y).
  Notation "x - y " := (rsub x y).  Notation "- x" := (ropp x).
  Notation "x == y" := (req x y).
  Variable Rsth : Setoid_Theory R req.
     Add Setoid R req Rsth as R_setoid5.
     Ltac rrefl := gen_reflexivity Rsth.
 Variable Reqe : ring_eq_ext radd rmul ropp req.
   Add Morphism radd : radd_ext5.  exact (Radd_ext Reqe). Qed.
   Add Morphism rmul : rmul_ext5.  exact (Rmul_ext Reqe). Qed.
   Add Morphism ropp : ropp_ext5.  exact (Ropp_ext Reqe). Qed.

 Variable ARth : almost_ring_theory 0 1 radd rmul rsub ropp req.
   Add Morphism rsub : rsub_ext7. exact (ARsub_ext Rsth Reqe ARth). Qed.
   Ltac norm := gen_srewrite 0 1 radd rmul rsub ropp req Rsth Reqe ARth.
   Ltac add_push := gen_add_push radd Rsth Reqe ARth.

 Fixpoint gen_phiNword (w : Nword) : R :=
  match w with
  | nil => 0
  | n :: nil => gen_phiN rO rI radd rmul n
  | N0 :: w' => - gen_phiNword w'
  | n::w' => gen_phiN rO rI radd rmul n - gen_phiNword w'
  end.

 Lemma gen_phiNword0_ok : forall w, Nw_is0 w = true -> gen_phiNword w == 0.
Proof.
induction w; simpl in |- *; intros; auto.
 reflexivity.

 destruct a.
  destruct w.
   reflexivity.

   rewrite IHw in |- *; trivial.
   apply (ARopp_zero Rsth Reqe ARth).

   discriminate.
Qed.

  Lemma gen_phiNword_cons : forall w n,
    gen_phiNword (n::w) == gen_phiN rO rI radd rmul n - gen_phiNword w.
induction w.
 destruct n; simpl in |- *; norm.

 intros.
 destruct n; norm.
Qed.

  Lemma gen_phiNword_Nwcons : forall w n,
    gen_phiNword (Nwcons n w) == gen_phiN rO rI radd rmul n - gen_phiNword w.
destruct w; intros.
 destruct n; norm.

 unfold Nwcons in |- *.
 rewrite gen_phiNword_cons in |- *.
 reflexivity.
Qed.

 Lemma gen_phiNword_ok : forall w1 w2,
   Nweq_bool w1 w2 = true -> gen_phiNword w1 == gen_phiNword w2.
induction w1; intros.
 simpl in |- *.
 rewrite (gen_phiNword0_ok _ H) in |- *.
 reflexivity.

 rewrite gen_phiNword_cons in |- *.
 destruct w2.
  simpl in H.
  destruct a; try  discriminate.
  rewrite (gen_phiNword0_ok _ H) in |- *.
  norm.

  simpl in H.
  rewrite gen_phiNword_cons in |- *.
  case_eq (Neq_bool a n); intros.
   rewrite H0 in H.
   rewrite <- (Neq_bool_ok _ _ H0) in |- *.
   rewrite (IHw1 _ H) in |- *.
   reflexivity.

   rewrite H0 in H;  discriminate H.
Qed.


Lemma Nwadd_ok : forall x y,
   gen_phiNword (Nwadd x y) == gen_phiNword x + gen_phiNword y.
induction x; intros.
 simpl in |- *.
 norm.

 destruct y.
  simpl Nwadd; norm.

  simpl Nwadd in |- *.
  repeat rewrite gen_phiNword_cons in |- *.
  rewrite (fun sreq => gen_phiN_add Rsth sreq (ARth_SRth ARth)) in |- *.
   destruct Reqe; constructor; trivial.

   rewrite IHx in |- *.
   norm.
   add_push (- gen_phiNword x); reflexivity.
Qed.

Lemma Nwopp_ok : forall x, gen_phiNword (Nwopp x) == - gen_phiNword x.
simpl in |- *.
unfold Nwopp in |- *; simpl in |- *.
intros.
rewrite gen_phiNword_Nwcons in |- *; norm.
Qed.

Lemma Nwscal_ok : forall n x,
  gen_phiNword (Nwscal n x) == gen_phiN rO rI radd rmul n * gen_phiNword x.
induction x; intros.
 norm.

 simpl Nwscal in |- *.
 repeat rewrite gen_phiNword_cons in |- *.
 rewrite (fun sreq => gen_phiN_mult Rsth sreq (ARth_SRth ARth)) in |- *.
  destruct Reqe; constructor; trivial.

  rewrite IHx in |- *.
  norm.
Qed.

Lemma Nwmul_ok : forall x y,
   gen_phiNword (Nwmul x y) == gen_phiNword x * gen_phiNword y.
induction x; intros.
 norm.

 destruct a.
  simpl Nwmul in |- *.
  rewrite Nwopp_ok in |- *.
  rewrite IHx in |- *.
  rewrite gen_phiNword_cons in |- *.
  norm.

  simpl Nwmul in |- *.
  unfold Nwsub in |- *.
  rewrite Nwadd_ok in |- *.
  rewrite Nwscal_ok in |- *.
  rewrite Nwopp_ok in |- *.
  rewrite IHx in |- *.
  rewrite gen_phiNword_cons in |- *.
  norm.
Qed.

(* Proof that [.] satisfies morphism specifications *)
 Lemma gen_phiNword_morph : 
  ring_morph 0 1 radd rmul rsub ropp req
   NwO NwI Nwadd Nwmul Nwsub Nwopp Nweq_bool gen_phiNword.
constructor.
 reflexivity.

 reflexivity.

 exact Nwadd_ok.

 intros.
 unfold Nwsub in |- *.
 rewrite Nwadd_ok in |- *.
 rewrite Nwopp_ok in |- *.
 norm.

 exact Nwmul_ok.

 exact Nwopp_ok.

 exact gen_phiNword_ok.
Qed.

End NWORDMORPHISM.

Section GEN_DIV.
  
  Variables  (R : Type) (rO : R) (rI : R) (radd : R -> R -> R)
              (rmul : R -> R -> R) (rsub : R -> R -> R) (ropp : R -> R)
              (req : R -> R -> Prop) (C : Type) (cO : C) (cI : C)
              (cadd : C -> C -> C) (cmul : C -> C -> C) (csub : C -> C -> C)
              (copp : C -> C) (ceqb : C -> C -> bool) (phi : C -> R).
 Variable Rsth : Setoid_Theory R req.
 Variable Reqe : ring_eq_ext radd rmul ropp req.
 Variable ARth : almost_ring_theory rO rI radd rmul rsub ropp req.
 Variable morph : ring_morph rO rI radd rmul rsub ropp req cO cI cadd cmul csub copp ceqb phi.
 
  (* Useful tactics *)		  
  Add Setoid R req Rsth as R_set1.
 Ltac rrefl := gen_reflexivity Rsth.
  Add Morphism radd : radd_ext.  exact (Radd_ext Reqe). Qed.
  Add Morphism rmul : rmul_ext.  exact (Rmul_ext Reqe). Qed.
  Add Morphism ropp : ropp_ext.  exact (Ropp_ext Reqe). Qed.
  Add Morphism rsub : rsub_ext. exact (ARsub_ext Rsth Reqe ARth). Qed.
 Ltac rsimpl := gen_srewrite 0 1 radd rmul rsub ropp req Rsth Reqe ARth.

 Definition triv_div x y :=  
   if ceqb x y then (cI, cO)
   else (cO, x).

 Ltac Esimpl :=repeat (progress (
   match goal with
   | |- context [phi cO] => rewrite (morph0 morph)
   | |- context [phi cI] => rewrite (morph1 morph)
   | |- context [phi (cadd ?x  ?y)] => rewrite ((morph_add morph) x y)
   | |- context [phi (cmul ?x  ?y)] => rewrite ((morph_mul morph) x y)
   | |- context [phi (csub ?x  ?y)] => rewrite ((morph_sub morph) x y)
   | |- context [phi (copp ?x)] => rewrite ((morph_opp morph) x)
   end)).

 Lemma triv_div_th : Ring_theory.div_theory  req cadd cmul phi triv_div.
 Proof.
  constructor.
  intros a b;unfold triv_div.
  assert (X:= morph.(morph_eq) a b);destruct (ceqb a b).
  Esimpl.
  rewrite X; trivial.
  rsimpl.
  Esimpl;  rsimpl.
Qed.

 Variable zphi : Z -> R.

 Lemma Ztriv_div_th : div_theory req Zplus Zmult zphi ZOdiv_eucl.
 Proof.
  constructor.
  intros; generalize (ZOdiv_eucl_correct a b); case ZOdiv_eucl; intros; subst.
  rewrite Zmult_comm; rsimpl.
 Qed.

 Variable nphi : N -> R.

 Lemma Ntriv_div_th : div_theory req Nplus Nmult nphi Ndiv_eucl.
  constructor.
  intros; generalize (Ndiv_eucl_correct a b); case Ndiv_eucl; intros; subst.
  rewrite Nmult_comm; rsimpl.
 Qed.

End GEN_DIV.

 (* syntaxification of constants in an abstract ring:
    the inverse of gen_phiPOS *)
 Ltac inv_gen_phi_pos rI add mul t :=
   let rec inv_cst t :=
   match t with
     rI => constr:1%positive
   | (add rI rI) => constr:2%positive
   | (add rI (add rI rI)) => constr:3%positive
   | (mul (add rI rI) ?p) => (* 2p *)
       match inv_cst p with
         NotConstant => NotConstant
       | 1%positive => NotConstant (* 2*1 is not convertible to 2 *)
       | ?p => constr:(xO p)
       end
   | (add rI (mul (add rI rI) ?p)) => (* 1+2p *)
       match inv_cst p with
         NotConstant => NotConstant
       | 1%positive => NotConstant
       | ?p => constr:(xI p)
       end
   | _ => NotConstant
   end in
   inv_cst t.

(* The (partial) inverse of gen_phiNword *)
 Ltac inv_gen_phiNword rO rI add mul opp t :=
   match t with
     rO => constr:NwO
   | _ =>
     match inv_gen_phi_pos rI add mul t with
       NotConstant => NotConstant
     | ?p => constr:(Npos p::nil)
     end
   end.


(* The inverse of gen_phiN *)
 Ltac inv_gen_phiN rO rI add mul t :=
   match t with
     rO => constr:0%N
   | _ =>
     match inv_gen_phi_pos rI add mul t with
       NotConstant => NotConstant
     | ?p => constr:(Npos p)
     end
   end.

(* The inverse of gen_phiZ *)
 Ltac inv_gen_phiZ rO rI add mul opp t :=
   match t with
     rO => constr:0%Z
   | (opp ?p) =>
     match inv_gen_phi_pos rI add mul p with
       NotConstant => NotConstant
     | ?p => constr:(Zneg p)
     end
   | _ =>
     match inv_gen_phi_pos rI add mul t with
       NotConstant => NotConstant
     | ?p => constr:(Zpos p)
     end
   end.

(* A simple tactic recognizing only 0 and 1. The inv_gen_phiX above
   are only optimisations that directly returns the reifid constant
   instead of resorting to the constant propagation of the simplification
   algorithm. *) 
Ltac inv_gen_phi rO rI cO cI t :=
  match t with
  | rO => cO
  | rI => cI
  end.

(* A simple tactic recognizing no constant *)
 Ltac inv_morph_nothing t := constr:(NotConstant).

Ltac coerce_to_almost_ring set ext rspec :=
  match type of rspec with
  | ring_theory _ _ _ _ _ _ _ => constr:(Rth_ARth set ext rspec)
  | semi_ring_theory _ _ _ _ _ => constr:(SRth_ARth set rspec)
  | almost_ring_theory _ _ _ _ _ _ _ => rspec
  | _ => fail 1 "not a valid ring theory"
  end.

Ltac coerce_to_ring_ext ext :=
  match type of ext with
  | ring_eq_ext _ _ _ _ => ext
  | sring_eq_ext _ _ _ => constr:(SReqe_Reqe ext)
  | _ => fail 1 "not a valid ring_eq_ext theory"
  end.

Ltac abstract_ring_morphism set ext rspec :=
  match type of rspec with
  | ring_theory _ _ _ _ _ _ _ => constr:(gen_phiZ_morph set ext rspec)
  | semi_ring_theory _ _ _ _ _ => constr:(gen_phiN_morph set ext rspec)
  | almost_ring_theory _ _ _ _ _ _ _ =>
      constr:(gen_phiNword_morph set ext rspec)
  | _ => fail 1 "bad ring structure"
  end.

Record hypo : Type := mkhypo {
   hypo_type : Type;
   hypo_proof : hypo_type
 }.

Ltac gen_ring_pow set arth pspec :=
 match pspec with
 | None =>
   match type of arth with
   | @almost_ring_theory ?R ?rO ?rI ?radd ?rmul ?rsub ?ropp ?req =>
     constr:(mkhypo (@pow_N_th R rI rmul req set))
   | _ => fail 1 "gen_ring_pow"
   end
 | Some ?t => constr:(t)
 end.

Ltac gen_ring_sign morph sspec :=
  match sspec with
  | None =>
    match type of morph with
    | @ring_morph ?R ?r0 ?rI ?radd ?rmul ?rsub ?ropp ?req  
               Z ?c0 ?c1 ?cadd ?cmul ?csub ?copp ?ceqb ?phi =>
       constr:(@mkhypo (sign_theory copp ceqb get_signZ) get_signZ_th)
    | @ring_morph ?R ?r0 ?rI ?radd ?rmul ?rsub ?ropp ?req  
               ?C  ?c0 ?c1 ?cadd ?cmul ?csub ?copp ?ceqb ?phi =>
        constr:(mkhypo (@get_sign_None_th C copp ceqb))
    | _ => fail 2 "ring anomaly : default_sign_spec"
    end
 | Some ?t => constr:(t)
 end.

Ltac default_div_spec set reqe arth morph :=
 match type of morph with
 | @ring_morph ?R ?r0 ?rI ?radd ?rmul ?rsub ?ropp ?req 
               Z ?c0 ?c1 Zplus Zmult ?csub ?copp ?ceq_b ?phi =>
      constr:(mkhypo (Ztriv_div_th set phi))
 | @ring_morph ?R ?r0 ?rI ?radd ?rmul ?rsub ?ropp ?req 
               N ?c0 ?c1 Nplus Nmult ?csub ?copp ?ceq_b ?phi =>
      constr:(mkhypo (Ntriv_div_th set phi)) 
 | @ring_morph ?R ?r0 ?rI ?radd ?rmul ?rsub ?ropp ?req 
               ?C ?c0 ?c1 ?cadd ?cmul ?csub ?copp ?ceq_b ?phi =>
      constr:(mkhypo (triv_div_th set reqe arth morph))
 | _ => fail 1 "ring anomaly : default_sign_spec" 
 end.

Ltac gen_ring_div set reqe arth morph dspec  :=
 match dspec with
 | None => default_div_spec set reqe arth morph   
 | Some ?t => constr:(t)
 end.
 
Ltac ring_elements set ext rspec pspec sspec dspec rk :=
  let arth := coerce_to_almost_ring set ext rspec in
  let ext_r := coerce_to_ring_ext ext in
  let morph :=
    match rk with
    | Abstract => abstract_ring_morphism set ext rspec
    | @Computational ?reqb_ok =>
        match type of arth with
        | almost_ring_theory ?rO ?rI ?add ?mul ?sub ?opp _ =>
            constr:(IDmorph rO rI add mul sub opp set _ reqb_ok)
        | _ => fail 2 "ring anomaly"
        end
    | @Morphism ?m =>
       match type of m with 
       | ring_morph _ _ _ _ _ _ _  _ _ _ _ _ _  _ _ => m 
       | @semi_morph _ _ _ _ _ _  _ _ _ _ _  _ _   => 
           constr:(SRmorph_Rmorph set m) 
       | _ => fail 2 "ring anomaly"
       end
    | _ => fail 1 "ill-formed ring kind"
    end in
  let p_spec := gen_ring_pow set arth pspec in
  let s_spec := gen_ring_sign morph sspec in
  let d_spec := gen_ring_div set ext_r arth morph dspec in
  fun f => f arth ext_r morph p_spec s_spec d_spec.

(* Given a ring structure and the kind of morphism,
   returns 2 lemmas (one for ring, and one for ring_simplify). *)

 Ltac ring_lemmas set ext rspec pspec sspec dspec rk :=
  let gen_lemma2 :=
    match pspec with
    | None => constr:(ring_rw_correct) 
    | Some _ => constr:(ring_rw_pow_correct)
    end in
  ring_elements set ext rspec pspec sspec dspec rk
    ltac:(fun arth ext_r morph p_spec s_spec d_spec =>
       match type of morph with
       | @ring_morph ?R ?r0 ?rI ?radd ?rmul ?rsub ?ropp ?req 
               ?C ?c0 ?c1 ?cadd ?cmul ?csub ?copp ?ceq_b ?phi =>
          let gen_lemma2_0 := 
              constr:(gen_lemma2 R  r0 rI  radd rmul rsub ropp req set ext_r arth 
                                C  c0 c1 cadd cmul csub copp ceq_b phi morph) in
          match p_spec with
          | @mkhypo (power_theory _ _ _ ?Cp_phi ?rpow) ?pp_spec =>      
             let gen_lemma2_1 := constr:(gen_lemma2_0 _ Cp_phi rpow pp_spec) in
             match d_spec with
             | @mkhypo (div_theory _ _ _ _  ?cdiv) ?dd_spec =>
                let gen_lemma2_2 := constr:(gen_lemma2_1 cdiv dd_spec) in
                match s_spec with
                | @mkhypo (sign_theory _ _ ?get_sign) ?ss_spec =>    
                  let lemma2 := constr:(gen_lemma2_2 get_sign ss_spec) in 
                  let lemma1 := 
                    constr:(ring_correct set ext_r arth morph pp_spec dd_spec) in
                  fun f => f arth ext_r morph lemma1 lemma2
                | _ => fail 4 "ring: bad sign specification"
                end
             | _ => fail 3 "ring: bad coefficiant division specification"
             end
          | _ => fail 2 "ring: bad power specification"
          end
       | _ => fail 1 "ring internal error: ring_lemmas, please report"
       end).

(* Tactic for constant *)
Ltac isnatcst t :=
  match t with
    O => true
  | S ?p => isnatcst p
  | _ => false
  end.

Ltac isPcst t :=
  match t with
  | xI ?p => isPcst p
  | xO ?p => isPcst p
  | xH => constr:true
  (* nat -> positive *)
  | P_of_succ_nat ?n => isnatcst n 
  | _ => false
  end.

Ltac isNcst t :=
  match t with
    N0 => constr:true
  | Npos ?p => isPcst p
  | _ => constr:false
  end.

Ltac isZcst t :=
  match t with
    Z0 => true
  | Zpos ?p => isPcst p
  | Zneg ?p => isPcst p
  (* injection nat -> Z *)
  | Z_of_nat ?n => isnatcst n
  (* injection N -> Z *)
  | Z_of_N ?n => isNcst n
  (* *)
  | _ => false
  end.





