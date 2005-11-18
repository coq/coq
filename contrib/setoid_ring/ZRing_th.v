Require Import Ring_th.
Require Import Pol.
Require Import Ring_tac.
Require Import ZArith_base.
Require Import BinInt.
Require Import BinNat.
Require Import Setoid.
 Set Implicit Arguments.

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
   Add Morphism radd : radd_ext3.  exact Reqe.(Radd_ext). Qed.
   Add Morphism rmul : rmul_ext3.  exact Reqe.(Rmul_ext). Qed.
   Add Morphism ropp : ropp_ext3.  exact Reqe.(Ropp_ext). Qed.

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
  rewrite H;trivial. rewrite Rth.(Ropp_def);rrefl.
  destruct H1 as [h [Heq1 [Heq2 Hor]]];trivial.
  unfold Pminus; rewrite Heq1;rewrite <- Heq2.
  rewrite (ARgen_phiPOS_add ARth);simpl;norm.
  rewrite Rth.(Ropp_def);norm.
  destruct H0 as [h [Heq1 [Heq2 Hor]]];trivial.
  unfold Pminus; rewrite Heq1;rewrite <- Heq2.
  rewrite (ARgen_phiPOS_add ARth);simpl;norm.
  add_push (gen_phiPOS1 h);rewrite Rth.(Ropp_def); norm.
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
  rewrite Rth.(Radd_sym).
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
   Add Morphism radd : radd_ext4.  exact Reqe.(Radd_ext). Qed.
   Add Morphism rmul : rmul_ext4.  exact Reqe.(Rmul_ext). Qed.
   Add Morphism ropp : ropp_ext4.  exact Reqe.(Ropp_ext). Qed.
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
(*
Section NNMORPHISM.
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
   Add Morphism radd : radd_ext5.  exact Reqe.(Radd_ext). Qed.
   Add Morphism rmul : rmul_ext5.  exact Reqe.(Rmul_ext). Qed.
   Add Morphism ropp : ropp_ext5.  exact Reqe.(Ropp_ext). Qed.

 Lemma SReqe : sring_eq_ext radd rmul req.
  case Reqe; constructor; trivial.
 Qed.

 Variable ARth : almost_ring_theory 0 1 radd rmul rsub ropp req.
   Add Morphism rsub : rsub_ext6. exact (ARsub_ext Rsth Reqe ARth). Qed.
   Ltac norm := gen_srewrite 0 1 radd rmul rsub ropp req Rsth Reqe ARth.
   Ltac add_push := gen_add_push radd Rsth Reqe ARth.

 Lemma SRth : semi_ring_theory 0 1 radd rmul req. 
  case ARth; constructor; trivial.
 Qed.

  Definition NN := prod N N.
  Definition gen_phiNN (x:NN) :=
    rsub (gen_phiN rO rI radd rmul (fst x)) (gen_phiN rO rI radd rmul (snd x)).
  Notation "[ x ]" := (gen_phiNN x).   

  Definition NNadd (x y : NN) : NN :=
    (fst x + fst y, snd x + snd y)%N.
  Definition NNmul (x y : NN) : NN :=
    (fst x * fst y + snd x * snd y, fst y * snd x + fst x * snd y)%N.
  Definition NNopp (x:NN) : NN := (snd x, fst x)%N.
  Definition NNsub (x y:NN) : NN := (fst x + snd y, fst y + snd x)%N.


 Lemma gen_phiNN_add : forall x y, [NNadd x y] == [x] + [y].
 Proof.
intros.
unfold NNadd, gen_phiNN in |- *; simpl in |- *.
repeat  rewrite (gen_phiN_add Rsth SReqe SRth).
norm.
add_push (- gen_phiN 0 1 radd rmul (snd x)).
rrefl.
Qed.
 
  Hypothesis ropp_involutive : forall x, - - x == x.


 Lemma gen_phiNN_mult : forall x y, [NNmul x y] == [x] * [y].
 Proof.
intros.
unfold NNmul, gen_phiNN in |- *; simpl in |- *.
repeat  rewrite (gen_phiN_add Rsth SReqe SRth).
repeat  rewrite (gen_phiN_mult Rsth SReqe SRth).
norm.
rewrite ropp_involutive.
add_push (- (gen_phiN 0 1 radd rmul (fst y) * gen_phiN 0 1 radd rmul (snd x))).
add_push ( gen_phiN 0 1 radd rmul (snd x) * gen_phiN 0 1 radd rmul (snd y)).
rewrite (ARmul_sym ARth (gen_phiN 0 1 radd rmul (fst y))
            (gen_phiN 0 1 radd rmul (snd x))).
rrefl.
Qed.

 Lemma gen_phiNN_sub : forall x y, [NNsub x y] == [x] - [y].
intros.
unfold NNsub, gen_phiNN; simpl.
repeat rewrite (gen_phiN_add Rsth SReqe SRth).
repeat rewrite (ARsub_def ARth).
repeat rewrite (ARopp_add ARth).
repeat rewrite (ARadd_assoc ARth).
rewrite ropp_involutive.
add_push (- gen_phiN 0 1 radd rmul (fst y)).
add_push ( - gen_phiN 0 1 radd rmul (snd x)).
rrefl.
Qed.


Definition NNeqbool (x y: NN) :=
  andb (Neq_bool (fst x) (fst y)) (Neq_bool (snd x) (snd y)).

Lemma NNeqbool_ok0 : forall x y,
  NNeqbool x y = true -> x = y.
unfold NNeqbool in |- *.
intros.
assert (Neq_bool (fst x) (fst y) = true).
 generalize H.
   case (Neq_bool (fst x) (fst y)); simpl in |- *; trivial.
 assert (Neq_bool (snd x) (snd y) = true).
   rewrite H0 in H; simpl in |- *; trivial.
  generalize H0 H1.
    destruct x; destruct y; simpl in |- *.
    intros.
     replace n with n1.
    replace n2 with n0; trivial.
     apply Neq_bool_ok; trivial.
   symmetry  in |- *.
     apply Neq_bool_ok; trivial.
Qed.


(*gen_phiN satisfies morphism specifications*)
 Lemma gen_phiNN_morph : ring_morph 0 1 radd rmul rsub ropp req
                        (N0,N0) (Npos xH,N0) NNadd NNmul NNsub NNopp NNeqbool gen_phiNN.
 Proof.
  constructor;intros;simpl; try rrefl.
  apply gen_phiN_add. apply gen_phiN_sub.  apply gen_phiN_mult.
  rewrite (Neq_bool_ok x y);trivial. rrefl.
 Qed.

End NNMORPHISM.

Section NSTARMORPHISM.
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
   Add Morphism radd : radd_ext3.  exact Reqe.(Radd_ext). Qed.
   Add Morphism rmul : rmul_ext3.  exact Reqe.(Rmul_ext). Qed.
   Add Morphism ropp : ropp_ext3.  exact Reqe.(Ropp_ext). Qed.

 Lemma SReqe : sring_eq_ext radd rmul req.
  case Reqe; constructor; trivial.
 Qed.

 Variable ARth : almost_ring_theory 0 1 radd rmul rsub ropp req.
   Add Morphism rsub : rsub_ext7. exact (ARsub_ext Rsth Reqe ARth). Qed.
   Ltac norm := gen_srewrite 0 1 radd rmul rsub ropp req Rsth Reqe ARth.
   Ltac add_push := gen_add_push radd Rsth Reqe ARth.

 Lemma SRth : semi_ring_theory 0 1 radd rmul req. 
  case ARth; constructor; trivial.
 Qed.

  Inductive Nword : Set :=
    Nlast (p:positive)
  | Ndigit (n:N) (w:Nword).

  Fixpoint opp_iter (n:nat) (t:R) {struct n} : R :=
    match n with 
      O => t
    | S k => ropp (opp_iter k t)
    end.

  Fixpoint gen_phiNword (x:Nword) (n:nat) {struct x} : R :=
    match x with
      Nlast p => opp_iter n (gen_phi_pos p)
    | Ndigit N0 w => gen_phiNword w (S n)
    | Ndigit m w => radd (opp_iter n (gen_phiN m)) (gen_phiNword w (S n))
    end.
  Notation "[ x ]" := (gen_phiNword x).   

  Fixpoint Nwadd (x y : Nword) {struct x} : Nword :=
    match x, y with
      Nlast p1, Nlast p2 => Nlast (p1+p2)%positive
    | Nlast p1, Ndigit n w => Ndigit (Npos p1 + n)%N w
    | Ndigit n w, Nlast p1 => Ndigit (n + Npos p1)%N w
    | Ndigit n1 w1, Ndigit n2 w2 => Ndigit (n1+n2)%N (Nwadd w1 w2)
    end.
  Fixpoint Nwmulp (x:positive) (y:Nword) {struct y} : Nword :=
    match y with
      Nlast p => Nlast (x*p)%positive
    | Ndigit n w => Ndigit (Npos x * n)%N (Nwmulp x w)
    end.
  Definition Nwmul (x y : Nword) {struct x} : Nword :=
    match x with
      Nlast k => Nmulp k y
    | Ndigit N0 w => Ndigit N0 (Nwmul w y)
    | Ndigit (Npos k) w =>
        Nwadd (Nwmulp k y) (Ndigit N0 (Nwmul w y))
   end.

  Definition Nwopp (x:Nword) : Nword := Ndigit N0 x.
  Definition Nwsub (x y:NN) : NN := (Nwadd x (Ndigit N0 y)).


 Lemma gen_phiNN_add : forall x y, [NNadd x y] == [x] + [y].
 Proof.
intros.
unfold NNadd, gen_phiNN in |- *; simpl in |- *.
repeat  rewrite (gen_phiN_add Rsth SReqe SRth).
norm.
add_push (- gen_phiN 0 1 radd rmul (snd x)).
rrefl.
Qed.

 Lemma gen_phiNN_mult : forall x y, [NNmul x y] == [x] * [y].
 Proof.
intros.
unfold NNmul, gen_phiNN in |- *; simpl in |- *.
repeat  rewrite (gen_phiN_add Rsth SReqe SRth).
repeat  rewrite (gen_phiN_mult Rsth SReqe SRth).
norm.
rewrite ropp_involutive.
add_push (- (gen_phiN 0 1 radd rmul (fst y) * gen_phiN 0 1 radd rmul (snd x))).
add_push ( gen_phiN 0 1 radd rmul (snd x) * gen_phiN 0 1 radd rmul (snd y)).
rewrite (ARmul_sym ARth (gen_phiN 0 1 radd rmul (fst y))
            (gen_phiN 0 1 radd rmul (snd x))).
rrefl.
Qed.

 Lemma gen_phiNN_sub : forall x y, [NNsub x y] == [x] - [y].
intros.
unfold NNsub, gen_phiNN; simpl.
repeat rewrite (gen_phiN_add Rsth SReqe SRth).
repeat rewrite (ARsub_def ARth).
repeat rewrite (ARopp_add ARth).
repeat rewrite (ARadd_assoc ARth).
rewrite ropp_involutive.
add_push (- gen_phiN 0 1 radd rmul (fst y)).
add_push ( - gen_phiN 0 1 radd rmul (snd x)).
rrefl.
Qed.


Definition NNeqbool (x y: NN) :=
  andb (Neq_bool (fst x) (fst y)) (Neq_bool (snd x) (snd y)).

Lemma NNeqbool_ok0 : forall x y,
  NNeqbool x y = true -> x = y.
unfold NNeqbool in |- *.
intros.
assert (Neq_bool (fst x) (fst y) = true).
 generalize H.
   case (Neq_bool (fst x) (fst y)); simpl in |- *; trivial.
 assert (Neq_bool (snd x) (snd y) = true).
   rewrite H0 in H; simpl in |- *; trivial.
  generalize H0 H1.
    destruct x; destruct y; simpl in |- *.
    intros.
     replace n with n1.
    replace n2 with n0; trivial.
     apply Neq_bool_ok; trivial.
   symmetry  in |- *.
     apply Neq_bool_ok; trivial.
Qed.


(*gen_phiN satisfies morphism specifications*)
 Lemma gen_phiNN_morph : ring_morph 0 1 radd rmul rsub ropp req
                        (N0,N0) (Npos xH,N0) NNadd NNmul NNsub NNopp NNeqbool gen_phiNN.
 Proof.
  constructor;intros;simpl; try rrefl.
  apply gen_phiN_add. apply gen_phiN_sub.  apply gen_phiN_mult.
  rewrite (Neq_bool_ok x y);trivial. rrefl.
 Qed.

End NSTARMORPHISM.
*)

 (* syntaxification of constants in an abstract ring *)
 Ltac inv_gen_phi_pos rI add mul t :=
   let rec inv_cst t :=
   match t with
     rI => constr:1%positive
   | (add rI rI) => constr:2%positive
   | (add rI (add rI rI)) => constr:3%positive
   | (mul (add rI rI) ?p) => (* 2p *)
       match inv_cst p with
         NotConstant => NotConstant
       | 1%positive => NotConstant
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

 Ltac inv_gen_phiN rO rI add mul t :=
   match t with
     rO => constr:0%N
   | _ =>
     match inv_gen_phi_pos rI add mul t with
       NotConstant => NotConstant
     | ?p => constr:(Npos p)
     end
   end.

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
(* coefs = Z (abstract ring) *)
Module Zpol.

Definition ring_gen_correct
  R rO rI radd rmul rsub ropp req rSet req_th Rth :=
  @ring_correct R rO rI radd rmul rsub ropp req rSet req_th
                (Rth_ARth rSet req_th Rth)
                Z 0%Z 1%Z Zplus Zmult Zminus Zopp Zeq_bool
                (@gen_phiZ R rO rI radd rmul ropp)
            (@gen_phiZ_morph R rO rI radd rmul rsub ropp req rSet req_th Rth).

Definition ring_rw_gen_correct
  R rO rI radd rmul rsub ropp req rSet req_th Rth :=
  @Pphi_dev_ok  R rO rI radd rmul rsub ropp req rSet req_th
                (Rth_ARth rSet req_th Rth)
                Z 0%Z 1%Z Zplus Zmult Zminus Zopp Zeq_bool
                (@gen_phiZ R rO rI radd rmul ropp)
            (@gen_phiZ_morph R rO rI radd rmul rsub ropp req rSet req_th Rth).

Definition ring_rw_gen_correct'
  R rO rI radd rmul rsub ropp req rSet req_th Rth :=
  @Pphi_dev_ok'  R rO rI radd rmul rsub ropp req rSet req_th
                 (Rth_ARth rSet req_th Rth)
                 Z 0%Z 1%Z Zplus Zmult Zminus Zopp Zeq_bool
                 (@gen_phiZ R rO rI radd rmul ropp)
            (@gen_phiZ_morph R rO rI radd rmul rsub ropp req rSet req_th Rth).

Definition ring_gen_eq_correct R rO rI radd rmul rsub ropp Rth :=
  @ring_gen_correct
     R rO rI radd rmul rsub ropp (@eq R) (Eqsth R) (Eq_ext _ _ _) Rth.

Definition ring_rw_gen_eq_correct R rO rI radd rmul rsub ropp Rth :=
  @ring_rw_gen_correct
     R rO rI radd rmul rsub ropp (@eq R) (Eqsth R) (Eq_ext _ _ _) Rth.

Definition ring_rw_gen_eq_correct' R rO rI radd rmul rsub ropp Rth :=
  @ring_rw_gen_correct'
     R rO rI radd rmul rsub ropp (@eq R) (Eqsth R) (Eq_ext _ _ _) Rth.

End Zpol.

(* coefs = N (abstract semi-ring) *)
Module Npol.

Definition ring_gen_correct
  R rO rI radd rmul req rSet req_th SRth :=
  @ring_correct R rO rI radd rmul (SRsub radd) (@SRopp R) req rSet
                (SReqe_Reqe req_th)
                (SRth_ARth rSet SRth)
                N 0%N 1%N Nplus Nmult (SRsub Nplus) (@SRopp N) Neq_bool
                (@gen_phiN R rO rI radd rmul)
            (@gen_phiN_morph R rO rI radd rmul req rSet req_th SRth).

Definition ring_rw_gen_correct
  R rO rI radd rmul req rSet req_th SRth :=
  @Pphi_dev_ok  R rO rI radd rmul (SRsub radd) (@SRopp R) req rSet
                (SReqe_Reqe req_th)
                (SRth_ARth rSet SRth)
                N 0%N 1%N Nplus Nmult (SRsub Nplus) (@SRopp N) Neq_bool
                (@gen_phiN R rO rI radd rmul)
            (@gen_phiN_morph R rO rI radd rmul req rSet req_th SRth).

Definition ring_rw_gen_correct'
  R rO rI radd rmul req rSet req_th SRth :=
  @Pphi_dev_ok'  R rO rI radd rmul (SRsub radd) (@SRopp R) req rSet
                 (SReqe_Reqe req_th)
                 (SRth_ARth rSet SRth)
                 N 0%N 1%N Nplus Nmult (SRsub Nplus) (@SRopp N) Neq_bool
                 (@gen_phiN R rO rI radd rmul)
            (@gen_phiN_morph R rO rI radd rmul req rSet req_th SRth).

Definition ring_gen_eq_correct R rO rI radd rmul SRth :=
  @ring_gen_correct
     R rO rI radd rmul (@eq R) (Eqsth R) (Eq_s_ext _ _) SRth.

Definition ring_rw_gen_eq_correct R rO rI radd rmul SRth :=
  @ring_rw_gen_correct
     R rO rI radd rmul (@eq R) (Eqsth R) (Eq_s_ext _ _) SRth.

Definition ring_rw_gen_eq_correct' R rO rI radd rmul SRth :=
  @ring_rw_gen_correct'
     R rO rI radd rmul (@eq R) (Eqsth R) (Eq_s_ext _ _) SRth.

End Npol.

(* Z *)

Ltac isZcst t :=
  match t with
    Z0 => constr:true
  | Zpos ?p => isZcst p
  | Zneg ?p => isZcst p
  | xI ?p => isZcst p
  | xO ?p => isZcst p
  | xH => constr:true
  | _ => constr:false
  end.
Ltac Zcst t :=
  match isZcst t with
    true => t
  | _ => NotConstant
  end.

Add New Ring Zr : Zth Computational Zeqb_ok Constant Zcst.

(* N *)

Ltac isNcst t :=
  match t with
    N0 => constr:true
  | Npos ?p => isNcst p
  | xI ?p => isNcst p
  | xO ?p => isNcst p
  | xH => constr:true
  | _ => constr:false
  end.
Ltac Ncst t :=
  match isNcst t with
    true => t
  | _ => NotConstant
  end.

Add New Ring Nr : Nth Computational Neq_bool_ok Constant Ncst.

(* nat *)

Ltac isnatcst t :=
  match t with
    O => true
  | S ?p => isnatcst p
  | _ => false
  end.
Ltac natcst t :=
  match isnatcst t with
    true => t
  | _ => NotConstant
  end.

 Lemma natSRth : semi_ring_theory O (S O) plus mult (@eq nat).
 Proof.
  constructor. exact plus_0_l. exact plus_comm. exact plus_assoc.
  exact mult_1_l. exact mult_0_l. exact mult_comm. exact mult_assoc.
  exact mult_plus_distr_r. 
 Qed.


Unboxed Fixpoint nateq (n m:nat) {struct m} : bool :=
  match n, m with
  | O, O => true
  | S n', S m' => nateq n' m'
  | _, _ => false
  end.

Lemma nateq_ok : forall n m:nat, nateq n m = true -> n = m.
Proof.
  simple induction n; simple induction m; simpl; intros; try discriminate.
  trivial.
  rewrite (H n1 H1).
  trivial.
Qed.

Add New Ring natr : natSRth Computational nateq_ok Constant natcst.

