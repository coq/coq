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

 Lemma get_signZ_th : sign_theory ropp req gen_phiZ get_signZ.
 Proof.
  constructor.
  destruct c;intros;try discriminate.
  injection H;clear H;intros H1;subst c'.
  simpl;rrefl.
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
  intros x y H; repeat rewrite same_genZ.
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

 (* syntaxification of constants in an abstract ring:
    the inverse of gen_phiPOS 
    Why we do not reconnize only rI ?????? *)
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

(* A simpl tactic reconninzing nothing *)
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
      fail 1 "an almost ring cannot be abstract"
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

Ltac default_sign_spec morph :=
 match type of morph with
 | @ring_morph ?R ?r0 ?rI ?radd ?rmul ?rsub ?ropp ?req 
               ?C ?c0 ?c1 ?cadd ?cmul ?csub ?copp ?ceq_b ?phi =>
      constr:(mkhypo (@get_sign_None_th R ropp req C phi))
 | _ => fail 1 "ring anomaly : default_sign_spec" 
 end.

Ltac gen_ring_sign set rspec morph sspec rk :=
 match sspec with
 | None =>
   match rk with
   | Abstract =>
     match type of rspec with
     | @ring_theory ?R ?rO ?rI ?radd ?rmul ?rsub ?ropp ?req =>
       constr:(mkhypo (@get_signZ_th R rO rI radd rmul ropp req set))
     | _ => default_sign_spec morph 
     end
   | _ => default_sign_spec morph 
   end
 | Some ?t => constr:(t)
 end.


Ltac ring_elements set ext rspec pspec sspec rk :=
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
       | _ => fail 2 " ici"
       end
    | _ => fail 1 "ill-formed ring kind"
    end in
  let p_spec := gen_ring_pow set arth pspec in
  let s_spec := gen_ring_sign set rspec morph sspec rk in
  fun f => f arth ext_r morph p_spec s_spec.

(* Given a ring structure and the kind of morphism,
   returns 2 lemmas (one for ring, and one for ring_simplify). *)
Ltac ring_lemmas set ext rspec pspec sspec rk :=
  let gen_lemma2 :=
    match pspec with
    | None => constr:(ring_rw_correct) 
    | Some _ => constr:(ring_rw_pow_correct)
    end in
  ring_elements set ext rspec pspec sspec rk
    ltac:(fun arth ext_r morph p_spec s_spec =>
        match p_spec with
        | mkhypo ?pp_spec =>
        match s_spec with
        | mkhypo ?ps_spec =>
          let lemma1 := 
            constr:(ring_correct set ext_r arth morph pp_spec) in
          let lemma2 := 
            constr:(gen_lemma2 _  _ _  _ _ _  _  _ set ext_r arth 
                           _  _ _  _ _ _  _  _  _ morph 
                           _ _ _ pp_spec
                           _ ps_spec) in 
          fun f => f arth ext_r morph lemma1 lemma2
        | _ => fail 2 "bad sign specification"
       end
       | _ => fail 1 "bad power specification" 
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





