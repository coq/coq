(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Zbool.
Require Import BinInt.
Require Import BinNat.
Require Import Setoid.
Require Import Ring_theory.
Require Import Ring_polynom.
Import List.

Set Implicit Arguments.
(* Set Universe Polymorphism. *)

Import RingSyntax.

(* An object to return when an expression is not recognized as a constant *)
Definition NotConstant := false.

(** Z is a ring and a setoid*)

Lemma Zsth : Setoid_Theory Z (@eq Z).
Proof (Eqsth Z).

Lemma Zeqe : ring_eq_ext Z.add Z.mul Z.opp (@eq Z).
Proof (Eq_ext Z.add Z.mul Z.opp).

Lemma Zth : ring_theory Z0 (Zpos xH) Z.add Z.mul Z.sub Z.opp (@eq Z).
Proof.
 constructor. exact Z.add_0_l. exact Z.add_comm. exact Z.add_assoc.
 exact Z.mul_1_l. exact Z.mul_comm. exact Z.mul_assoc.
 exact Z.mul_add_distr_r. trivial. exact Z.sub_diag.
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
     Add Parametric Relation : R req
       reflexivity  proved by Rsth.(@Equivalence_Reflexive _ _)
       symmetry     proved by Rsth.(@Equivalence_Symmetric _ _)
       transitivity proved by Rsth.(@Equivalence_Transitive _ _)
      as R_setoid3.
     Ltac rrefl := gen_reflexivity Rsth.
 Variable Reqe : ring_eq_ext radd rmul ropp req.
   Add Morphism radd with signature (req ==> req ==> req) as radd_ext3.
   Proof. exact (Radd_ext Reqe). Qed.
   Add Morphism rmul with signature (req ==> req ==> req) as rmul_ext3.
   Proof. exact (Rmul_ext Reqe). Qed.
   Add Morphism ropp with signature (req ==> req) as ropp_ext3.
   Proof. exact (Ropp_ext Reqe). Qed.

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

 Lemma get_signZ_th : sign_theory Z.opp Zeq_bool get_signZ.
 Proof.
  constructor.
  destruct c;intros;try discriminate.
  injection H as <-.
  simpl. unfold Zeq_bool. rewrite Z.compare_refl. trivial.
 Qed.


 Section ALMOST_RING.
 Variable ARth : almost_ring_theory 0 1 radd rmul rsub ropp req.
   Add Morphism rsub with signature (req ==> req ==> req) as rsub_ext3.
   Proof. exact (ARsub_ext Rsth Reqe ARth). Qed.
   Ltac norm := gen_srewrite Rsth Reqe ARth.
   Ltac add_push := gen_add_push radd Rsth Reqe ARth.

 Lemma same_gen : forall x, gen_phiPOS1 x == gen_phiPOS x.
 Proof.
  induction x;simpl.
  rewrite IHx;destruct x;simpl;norm.
  rewrite IHx;destruct x;simpl;norm.
  rrefl.
 Qed.

 Lemma ARgen_phiPOS_Psucc : forall x,
   gen_phiPOS1 (Pos.succ x) == 1 + (gen_phiPOS1 x).
 Proof.
  induction x;simpl;norm.
  rewrite IHx;norm.
  add_push 1;rrefl.
 Qed.

 Lemma ARgen_phiPOS_add : forall x y,
   gen_phiPOS1 (x + y) == (gen_phiPOS1 x) + (gen_phiPOS1 y).
 Proof.
  induction x;destruct y;simpl;norm.
  rewrite Pos.add_carry_spec.
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
   Add Morphism rsub with signature (req ==> req ==> req) as rsub_ext4.
   Proof. exact (ARsub_ext Rsth Reqe ARth). Qed.
   Ltac norm := gen_srewrite Rsth Reqe ARth.
   Ltac add_push := gen_add_push radd Rsth Reqe ARth.

(*morphisms are extensionally equal*)
 Lemma same_genZ : forall x, [x] == gen_phiZ1 x.
 Proof.
  destruct x;simpl; try rewrite (same_gen ARth);rrefl.
 Qed.

 Lemma gen_Zeqb_ok : forall x y,
   Zeq_bool x y = true -> [x] == [y].
 Proof.
  intros x y H.
  assert (H1 := Zeq_bool_eq x y H);unfold IDphi in H1.
  rewrite H1;rrefl.
 Qed.

 Lemma gen_phiZ1_pos_sub : forall x y,
 gen_phiZ1 (Z.pos_sub x y) == gen_phiPOS1 x + -gen_phiPOS1 y.
 Proof.
  intros x y.
  rewrite Z.pos_sub_spec.
  case Pos.compare_spec; intros H; simpl.
  rewrite H. rewrite (Ropp_def Rth);rrefl.
  rewrite <- (Pos.sub_add y x H) at 2. rewrite Pos.add_comm.
  rewrite (ARgen_phiPOS_add ARth);simpl;norm.
  rewrite (Ropp_def Rth);norm.
  rewrite <- (Pos.sub_add x y H) at 2.
  rewrite (ARgen_phiPOS_add ARth);simpl;norm.
  add_push (gen_phiPOS1 (x-y));rewrite (Ropp_def Rth); norm.
 Qed.

 Lemma gen_phiZ_add : forall x y, [x + y] == [x] + [y].
 Proof.
  intros x y; repeat rewrite same_genZ; generalize x y;clear x y.
  destruct x, y; simpl; norm.
  apply (ARgen_phiPOS_add ARth).
  apply gen_phiZ1_pos_sub.
  rewrite gen_phiZ1_pos_sub. apply (Radd_comm Rth).
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
   Z.add Z.mul Z.sub Z.opp Zeq_bool gen_phiZ.
 Proof.
  assert ( SRmorph : semi_morph 0 1 radd rmul req Z0 (Zpos xH)
                  Z.add Z.mul Zeq_bool gen_phiZ).
   apply mkRmorph;simpl;try rrefl.
   apply gen_phiZ_add.  apply gen_phiZ_mul. apply gen_Zeqb_ok.
  apply  (Smorph_morph Rsth Reqe Rth Zth SRmorph gen_phiZ_ext).
 Qed.

End ZMORPHISM.

(** N is a semi-ring and a setoid*)
Lemma Nsth : Setoid_Theory N (@eq N).
Proof (Eqsth N).

Lemma Nseqe : sring_eq_ext N.add N.mul (@eq N).
Proof (Eq_s_ext N.add N.mul).

Lemma Nth : semi_ring_theory 0%N 1%N N.add N.mul (@eq N).
Proof.
 constructor. exact N.add_0_l. exact N.add_comm. exact N.add_assoc.
 exact N.mul_1_l. exact N.mul_0_l. exact N.mul_comm. exact N.mul_assoc.
 exact N.mul_add_distr_r.
Qed.

Definition Nsub := SRsub N.add.
Definition Nopp := (@SRopp N).

Lemma Neqe : ring_eq_ext N.add N.mul Nopp (@eq N).
Proof (SReqe_Reqe Nseqe).

Lemma Nath :
 almost_ring_theory 0%N 1%N N.add N.mul Nsub Nopp (@eq N).
Proof (SRth_ARth Nsth Nth).

Lemma Neqb_ok : forall x y, N.eqb x y = true -> x = y.
Proof. exact (fun x y => proj1 (N.eqb_eq x y)). Qed.

(**Same as above : definition of two, extensionally equal, generic morphisms *)
(**from N to any semi-ring*)
Section NMORPHISM.
 Variable R : Type.
 Variable  (rO rI : R) (radd rmul: R->R->R).
 Variable req : R -> R -> Prop.
  Notation "0" := rO.  Notation "1" := rI.
  Notation "x + y" := (radd x y).  Notation "x * y " := (rmul x y).
 Variable Rsth : Setoid_Theory R req.
     Add Parametric Relation : R req
       reflexivity  proved by Rsth.(@Equivalence_Reflexive _ _)
       symmetry     proved by Rsth.(@Equivalence_Symmetric _ _)
       transitivity proved by Rsth.(@Equivalence_Transitive _ _)
       as R_setoid4.
     Ltac rrefl := gen_reflexivity Rsth.
 Variable SReqe : sring_eq_ext radd rmul req.
 Variable SRth : semi_ring_theory 0 1 radd rmul req.
 Let ARth := SRth_ARth Rsth SRth.
 Let Reqe := SReqe_Reqe SReqe.
 Let ropp := (@SRopp R).
 Let rsub := (@SRsub R radd).
  Notation "x - y " := (rsub x y).  Notation "- x" := (ropp x).
  Notation "x == y" := (req x y).
   Add Morphism radd with signature (req ==> req ==> req) as radd_ext4.
   Proof. exact (Radd_ext Reqe). Qed.
   Add Morphism rmul with signature (req ==> req ==> req) as rmul_ext4.
   Proof. exact (Rmul_ext Reqe). Qed.
   Ltac norm := gen_srewrite_sr Rsth Reqe ARth.

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
  destruct x;simpl. reflexivity.
  now rewrite (same_gen Rsth Reqe ARth).
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
                           0%N 1%N N.add N.mul Nsub Nopp N.eqb gen_phiN.
 Proof.
  constructor; simpl; try reflexivity.
  apply gen_phiN_add. apply gen_phiN_sub. apply gen_phiN_mult.
  intros x y EQ. apply N.eqb_eq in EQ. now subst.
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
     if N.eqb n1 n2 then Nweq_bool w1' w2' else false
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
     Add Parametric Relation : R req
       reflexivity  proved by Rsth.(@Equivalence_Reflexive _ _)
       symmetry     proved by Rsth.(@Equivalence_Symmetric _ _)
       transitivity proved by Rsth.(@Equivalence_Transitive _ _)
      as R_setoid5.
     Ltac rrefl := gen_reflexivity Rsth.
 Variable Reqe : ring_eq_ext radd rmul ropp req.
   Add Morphism radd with signature (req ==> req ==> req) as radd_ext5.
   Proof. exact (Radd_ext Reqe). Qed.
   Add Morphism rmul with signature (req ==> req ==> req) as rmul_ext5.
   Proof. exact (Rmul_ext Reqe). Qed.
   Add Morphism ropp with signature (req ==> req) as ropp_ext5.
   Proof. exact (Ropp_ext Reqe). Qed.

 Variable ARth : almost_ring_theory 0 1 radd rmul rsub ropp req.
   Add Morphism rsub with signature (req ==> req ==> req) as rsub_ext7.
   Proof. exact (ARsub_ext Rsth Reqe ARth). Qed.
   Ltac norm := gen_srewrite Rsth Reqe ARth.
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
induction w; simpl; intros; auto.
 reflexivity.

 destruct a.
  destruct w.
   reflexivity.

   rewrite IHw; trivial.
   apply (ARopp_zero Rsth Reqe ARth).

   discriminate.
Qed.

  Lemma gen_phiNword_cons : forall w n,
    gen_phiNword (n::w) == gen_phiN rO rI radd rmul n - gen_phiNword w.
induction w.
 destruct n; simpl; norm.

 intros.
 destruct n; norm.
Qed.

  Lemma gen_phiNword_Nwcons : forall w n,
    gen_phiNword (Nwcons n w) == gen_phiN rO rI radd rmul n - gen_phiNword w.
destruct w; intros.
 destruct n; norm.

 unfold Nwcons.
 rewrite gen_phiNword_cons.
 reflexivity.
Qed.

 Lemma gen_phiNword_ok : forall w1 w2,
   Nweq_bool w1 w2 = true -> gen_phiNword w1 == gen_phiNword w2.
induction w1; intros.
 simpl.
 rewrite (gen_phiNword0_ok _ H).
 reflexivity.

 rewrite gen_phiNword_cons.
 destruct w2.
  simpl in H.
  destruct a; try  discriminate.
  rewrite (gen_phiNword0_ok _ H).
  norm.

  simpl in H.
  rewrite gen_phiNword_cons.
  case_eq (N.eqb a n); intros H0.
   rewrite H0 in H.
   apply N.eqb_eq in H0. rewrite <- H0.
   rewrite (IHw1 _ H).
   reflexivity.

   rewrite H0 in H;  discriminate H.
Qed.


Lemma Nwadd_ok : forall x y,
   gen_phiNword (Nwadd x y) == gen_phiNword x + gen_phiNword y.
induction x; intros.
 simpl.
 norm.

 destruct y.
  simpl Nwadd; norm.

  simpl Nwadd.
  repeat rewrite gen_phiNword_cons.
  rewrite (fun sreq => gen_phiN_add Rsth sreq (ARth_SRth ARth)) by
    (destruct Reqe; constructor; trivial).

  rewrite IHx.
  norm.
  add_push (- gen_phiNword x); reflexivity.
Qed.

Lemma Nwopp_ok : forall x, gen_phiNword (Nwopp x) == - gen_phiNword x.
simpl.
unfold Nwopp; simpl.
intros.
rewrite gen_phiNword_Nwcons; norm.
Qed.

Lemma Nwscal_ok : forall n x,
  gen_phiNword (Nwscal n x) == gen_phiN rO rI radd rmul n * gen_phiNword x.
induction x; intros.
 norm.

 simpl Nwscal.
 repeat rewrite gen_phiNword_cons.
 rewrite (fun sreq => gen_phiN_mult Rsth sreq (ARth_SRth ARth))
   by (destruct Reqe; constructor; trivial).

  rewrite IHx.
  norm.
Qed.

Lemma Nwmul_ok : forall x y,
   gen_phiNword (Nwmul x y) == gen_phiNword x * gen_phiNword y.
induction x; intros.
 norm.

 destruct a.
  simpl Nwmul.
  rewrite Nwopp_ok.
  rewrite IHx.
  rewrite gen_phiNword_cons.
  norm.

  simpl Nwmul.
  unfold Nwsub.
  rewrite Nwadd_ok.
  rewrite Nwscal_ok.
  rewrite Nwopp_ok.
  rewrite IHx.
  rewrite gen_phiNword_cons.
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
 unfold Nwsub.
 rewrite Nwadd_ok.
 rewrite Nwopp_ok.
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
  Add Parametric Relation : R req
    reflexivity  proved by Rsth.(@Equivalence_Reflexive _ _)
    symmetry     proved by Rsth.(@Equivalence_Symmetric _ _)
    transitivity proved by Rsth.(@Equivalence_Transitive _ _)
   as R_set1.
 Ltac rrefl := gen_reflexivity Rsth.
  Add Morphism radd with signature (req ==> req ==> req) as radd_ext.
  Proof. exact (Radd_ext Reqe). Qed.
  Add Morphism rmul with signature (req ==> req ==> req) as rmul_ext.
  Proof. exact (Rmul_ext Reqe). Qed.
  Add Morphism ropp with signature (req ==> req) as ropp_ext.
  Proof. exact (Ropp_ext Reqe). Qed.
  Add Morphism rsub with signature (req ==> req ==> req) as rsub_ext.
  Proof. exact (ARsub_ext Rsth Reqe ARth). Qed.
 Ltac rsimpl := gen_srewrite Rsth Reqe ARth.

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

 Lemma Ztriv_div_th : div_theory req Z.add Z.mul zphi Z.quotrem.
 Proof.
  constructor.
  intros; generalize (Z.quotrem_eq a b); case Z.quotrem; intros; subst.
  rewrite Z.mul_comm; rsimpl.
 Qed.

 Variable nphi : N -> R.

 Lemma Ntriv_div_th : div_theory req N.add N.mul nphi N.div_eucl.
  constructor.
  intros; generalize (N.div_eucl_spec a b); case N.div_eucl; intros; subst.
  rewrite N.mul_comm; rsimpl.
 Qed.

End GEN_DIV.

 (* syntaxification of constants in an abstract ring:
    the inverse of gen_phiPOS *)
 Ltac inv_gen_phi_pos rI add mul t :=
   let rec inv_cst t :=
   match t with
     rI => constr:(1%positive)
   | (add rI rI) => constr:(2%positive)
   | (add rI (add rI rI)) => constr:(3%positive)
   | (mul (add rI rI) ?p) => (* 2p *)
       match inv_cst p with
         NotConstant => constr:(NotConstant)
       | 1%positive => constr:(NotConstant) (* 2*1 is not convertible to 2 *)
       | ?p => constr:(xO p)
       end
   | (add rI (mul (add rI rI) ?p)) => (* 1+2p *)
       match inv_cst p with
         NotConstant => constr:(NotConstant)
       | 1%positive => constr:(NotConstant)
       | ?p => constr:(xI p)
       end
   | _ => constr:(NotConstant)
   end in
   inv_cst t.

(* The (partial) inverse of gen_phiNword *)
 Ltac inv_gen_phiNword rO rI add mul opp t :=
   match t with
     rO => constr:(NwO)
   | _ =>
     match inv_gen_phi_pos rI add mul t with
       NotConstant => constr:(NotConstant)
     | ?p => constr:(Npos p::nil)
     end
   end.


(* The inverse of gen_phiN *)
 Ltac inv_gen_phiN rO rI add mul t :=
   match t with
     rO => constr:(0%N)
   | _ =>
     match inv_gen_phi_pos rI add mul t with
       NotConstant => constr:(NotConstant)
     | ?p => constr:(Npos p)
     end
   end.

(* The inverse of gen_phiZ *)
 Ltac inv_gen_phiZ rO rI add mul opp t :=
   match t with
     rO => constr:(0%Z)
   | (opp ?p) =>
     match inv_gen_phi_pos rI add mul p with
       NotConstant => constr:(NotConstant)
     | ?p => constr:(Zneg p)
     end
   | _ =>
     match inv_gen_phi_pos rI add mul t with
       NotConstant => constr:(NotConstant)
     | ?p => constr:(Zpos p)
     end
   end.

(* A simple tactic recognizing only 0 and 1. The inv_gen_phiX above
   are only optimisations that directly returns the reified constant
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
               Z ?c0 ?c1 Z.add Z.mul ?csub ?copp ?ceq_b ?phi =>
      constr:(mkhypo (Ztriv_div_th set phi))
 | @ring_morph ?R ?r0 ?rI ?radd ?rmul ?rsub ?ropp ?req
               N ?c0 ?c1 N.add N.mul ?csub ?copp ?ceq_b ?phi =>
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
             | _ => fail 3 "ring: bad coefficient division specification"
             end
          | _ => fail 2 "ring: bad power specification"
          end
       | _ => fail 1 "ring internal error: ring_lemmas, please report"
       end).

(* Tactic for constant *)
Ltac isnatcst t :=
  match t with
    O => constr:(true)
  | S ?p => isnatcst p
  | _ => constr:(false)
  end.

Ltac isPcst t :=
  match t with
  | xI ?p => isPcst p
  | xO ?p => isPcst p
  | xH => constr:(true)
  (* nat -> positive *)
  | Pos.of_succ_nat ?n => isnatcst n
  | _ => constr:(false)
  end.

Ltac isNcst t :=
  match t with
    N0 => constr:(true)
  | Npos ?p => isPcst p
  | _ => constr:(false)
  end.

Ltac isZcst t :=
  match t with
    Z0 => constr:(true)
  | Zpos ?p => isPcst p
  | Zneg ?p => isPcst p
  (* injection nat -> Z *)
  | Z.of_nat ?n => isnatcst n
  (* injection N -> Z *)
  | Z.of_N ?n => isNcst n
  (* *)
  | _ => constr:(false)
  end.
