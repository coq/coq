(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

Require Import OrderedRing.
Require Import RingMicromega.
Require Import ZCoeff.
Require Import Refl.
Require Import ZArith.
Require Import List.
Require Import Bool.
(*Declare ML Module "micromega_plugin".*)

Ltac flatten_bool :=
  repeat match goal with
           [ id : (_ && _)%bool = true |- _ ] =>  destruct (andb_prop _ _ id); clear id
           |  [ id : (_ || _)%bool = true |- _ ] =>  destruct (orb_prop _ _ id); clear id
         end.

Ltac inv H := inversion H ; try subst ; clear H.


Require Import EnvRing.

Open Scope Z_scope.
  
Lemma Zsor : SOR 0 1 Zplus Zmult Zminus Zopp (@eq Z) Zle Zlt.
Proof.
  constructor ; intros ; subst ; try (intuition (auto  with zarith)).
  apply Zsth.
  apply Zth.
  destruct (Ztrichotomy n m) ; intuition (auto with zarith).
  apply Zmult_lt_0_compat ; auto.
Qed.

Lemma ZSORaddon :
  SORaddon 0 1 Zplus Zmult Zminus Zopp  (@eq Z) Zle (* ring elements *)
  0%Z 1%Z Zplus Zmult Zminus Zopp (* coefficients *)
  Zeq_bool Zle_bool
  (fun x => x) (fun x => x) (pow_N 1 Zmult).
Proof.
  constructor.
  constructor ; intros ; try reflexivity.
  apply Zeq_bool_eq ; auto.
  constructor.
  reflexivity.
  intros x y.
  apply Zeq_bool_neq ; auto.
  apply Zle_bool_imp_le.
Qed.

Fixpoint Zeval_expr (env : PolEnv Z) (e: PExpr Z) : Z :=
  match e with
    | PEc c => c
    | PEX x => env x
    | PEadd e1 e2 => Zeval_expr env e1 + Zeval_expr env e2
    | PEmul e1 e2 => Zeval_expr env e1 * Zeval_expr env e2
    | PEpow e1 n  => Zpower (Zeval_expr env e1) (Z_of_N n)
    | PEsub e1 e2 => (Zeval_expr env e1) - (Zeval_expr env e2)
    | PEopp e   => Zopp (Zeval_expr env e)
  end.

Definition eval_expr := eval_pexpr  Zplus Zmult Zminus Zopp (fun x => x) (fun x => x) (pow_N 1 Zmult).

Lemma ZNpower : forall r n, r ^ Z_of_N n = pow_N 1 Zmult r n.
Proof.
  destruct n.
  reflexivity.
  simpl.
  unfold Zpower_pos.
  replace (pow_pos Zmult r p) with (1 * (pow_pos Zmult r p)) by ring.
  generalize 1.
  induction p; simpl ; intros ; repeat rewrite IHp ; ring.
Qed.

Lemma Zeval_expr_compat : forall env e, Zeval_expr env e = eval_expr env e.
Proof.
  induction e ; simpl ; try congruence.
  reflexivity.
  rewrite ZNpower. congruence.
Qed.

Definition Zeval_op2 (o : Op2) : Z -> Z -> Prop :=
match o with
| OpEq =>  @eq Z
| OpNEq => fun x y  => ~ x = y
| OpLe => Zle
| OpGe => Zge
| OpLt => Zlt
| OpGt => Zgt
end.

Definition Zeval_formula (env : PolEnv Z) (f : Formula Z):=   
  let (lhs, op, rhs) := f in
    (Zeval_op2 op) (Zeval_expr env lhs) (Zeval_expr env rhs).

Definition Zeval_formula' :=
  eval_formula  Zplus Zmult Zminus Zopp (@eq Z) Zle Zlt (fun x => x) (fun x => x) (pow_N 1 Zmult).

Lemma Zeval_formula_compat : forall env f, Zeval_formula env f <-> Zeval_formula' env f.
Proof.
  destruct f ; simpl. 
  rewrite Zeval_expr_compat. rewrite Zeval_expr_compat.
  unfold eval_expr.
  generalize (eval_pexpr Zplus Zmult Zminus Zopp (fun x : Z => x) 
        (fun x : N => x) (pow_N 1 Zmult) env Flhs).
  generalize ((eval_pexpr Zplus Zmult Zminus Zopp (fun x : Z => x) 
        (fun x : N => x) (pow_N 1 Zmult) env Frhs)).
  destruct Fop ; simpl; intros ; intuition (auto with zarith).
Qed.
  

Definition eval_nformula :=
  eval_nformula 0 Zplus Zmult  (@eq Z) Zle Zlt (fun x => x) .

Definition Zeval_op1 (o : Op1) : Z -> Prop :=
match o with
| Equal => fun x : Z => x = 0
| NonEqual => fun x : Z => x <> 0
| Strict => fun x : Z => 0 < x
| NonStrict => fun x : Z => 0 <= x
end.

  
Lemma Zeval_nformula_dec : forall env d, (eval_nformula env d) \/ ~ (eval_nformula env d).
Proof.
  intros.
  apply (eval_nformula_dec Zsor).
Qed.

Definition ZWitness := Psatz Z.

Definition ZWeakChecker := check_normalised_formulas 0 1 Zplus Zmult Zeq_bool Zle_bool.

Lemma ZWeakChecker_sound :   forall (l : list (NFormula Z)) (cm : ZWitness),
  ZWeakChecker l cm = true ->
  forall env, make_impl (eval_nformula env) l False.
Proof.
  intros l cm H.
  intro.
  unfold eval_nformula.
  apply (checker_nf_sound Zsor ZSORaddon l cm).
  unfold ZWeakChecker in H.
  exact H.
Qed.

Definition psub  := psub Z0  Zplus Zminus Zopp Zeq_bool.

Definition padd  := padd Z0  Zplus Zeq_bool.

Definition norm  := norm 0 1 Zplus Zmult Zminus Zopp Zeq_bool.

Definition eval_pol := eval_pol 0  Zplus Zmult (fun x => x).

Lemma eval_pol_sub : forall env lhs rhs, eval_pol env (psub  lhs rhs) = eval_pol env lhs - eval_pol env rhs.
Proof.
  intros.
  apply (eval_pol_sub Zsor ZSORaddon).
Qed.

Lemma eval_pol_add : forall env lhs rhs, eval_pol env (padd  lhs rhs) = eval_pol env lhs + eval_pol env rhs.
Proof.
  intros.
  apply (eval_pol_add Zsor ZSORaddon).
Qed.

Lemma eval_pol_norm : forall env e, eval_expr env e = eval_pol env (norm e) .
Proof.
  intros.
  apply (eval_pol_norm Zsor ZSORaddon).
Qed.
  
Definition xnormalise (t:Formula Z) : list (NFormula Z)  :=
  let (lhs,o,rhs) := t in
    let lhs := norm lhs in
      let rhs := norm rhs in
    match o with
      | OpEq => 
        ((psub lhs (padd  rhs (Pc 1))),NonStrict)::((psub rhs (padd lhs (Pc 1))),NonStrict)::nil
      | OpNEq => (psub lhs rhs,Equal) :: nil
      | OpGt   => (psub rhs lhs,NonStrict) :: nil
      | OpLt => (psub lhs rhs,NonStrict) :: nil
      | OpGe => (psub rhs (padd lhs (Pc 1)),NonStrict) :: nil
      | OpLe => (psub lhs (padd rhs (Pc 1)),NonStrict) :: nil
    end.

Require Import Tauto.

Definition normalise (t:Formula Z) : cnf (NFormula Z) :=
  List.map  (fun x => x::nil) (xnormalise t).


Lemma normalise_correct : forall env t, eval_cnf (eval_nformula env) (normalise t) <-> Zeval_formula env t.
Proof.
  Opaque padd.
  unfold normalise, xnormalise  ; simpl; intros env t.
  rewrite Zeval_formula_compat.
  unfold eval_cnf.
  destruct t as [lhs o rhs]; case_eq o; simpl;
    repeat rewrite eval_pol_sub;
      repeat rewrite eval_pol_add;
      repeat rewrite <- eval_pol_norm ; simpl in *;
  unfold eval_expr;
  generalize (   eval_pexpr  Zplus Zmult Zminus Zopp (fun x : Z => x)
    (fun x : BinNat.N => x) (pow_N 1 Zmult) env lhs);
  generalize (eval_pexpr  Zplus Zmult Zminus Zopp (fun x : Z => x)
    (fun x : BinNat.N => x) (pow_N 1 Zmult) env rhs) ; intros z1 z2 ; intros ; subst;
    intuition (auto with zarith).
  Transparent padd.
Qed.
  
Definition xnegate (t:RingMicromega.Formula Z) : list (NFormula Z)  :=
  let (lhs,o,rhs) := t in
    let lhs := norm lhs in
      let rhs := norm rhs in
    match o with
      | OpEq  => (psub lhs rhs,Equal) :: nil
      | OpNEq => ((psub lhs (padd rhs (Pc 1))),NonStrict)::((psub rhs (padd lhs (Pc 1))),NonStrict)::nil
      | OpGt  => (psub lhs (padd rhs (Pc 1)),NonStrict) :: nil
      | OpLt  => (psub rhs (padd lhs (Pc 1)),NonStrict) :: nil
      | OpGe  => (psub lhs rhs,NonStrict) :: nil
      | OpLe  => (psub rhs lhs,NonStrict) :: nil
    end.

Definition negate (t:RingMicromega.Formula Z) : cnf (NFormula Z) :=
  List.map  (fun x => x::nil) (xnegate t).

Lemma negate_correct : forall env t, eval_cnf (eval_nformula env) (negate t) <-> ~ Zeval_formula env t.
Proof.
Proof.
  Opaque padd.
  intros env t.
  rewrite Zeval_formula_compat.
  unfold negate, xnegate  ; simpl.
  unfold eval_cnf.
  destruct t as [lhs o rhs]; case_eq o; simpl;
    repeat rewrite eval_pol_sub;
      repeat rewrite eval_pol_add;
      repeat rewrite <- eval_pol_norm ; simpl in *;
  unfold eval_expr;
  generalize (   eval_pexpr  Zplus Zmult Zminus Zopp (fun x : Z => x)
    (fun x : BinNat.N => x) (pow_N 1 Zmult) env lhs);
  generalize (eval_pexpr  Zplus Zmult Zminus Zopp (fun x : Z => x)
    (fun x : BinNat.N => x) (pow_N 1 Zmult) env rhs) ; intros z1 z2 ; intros ; subst;
    intuition (auto with zarith).
  Transparent padd.
Qed.



Definition ZweakTautoChecker (w: list ZWitness) (f : BFormula (Formula Z)) : bool :=
  @tauto_checker (Formula Z) (NFormula Z) normalise negate  ZWitness ZWeakChecker f w.

(* To get a complete checker, the proof format has to be enriched *)

Require Import Zdiv.
Open Scope Z_scope.

Definition ceiling (a b:Z) : Z :=
  let (q,r) := Zdiv_eucl a b in
    match r with
      | Z0 => q
      | _  => q + 1
    end.

Lemma narrow_interval_lower_bound : forall a b x, a > 0 -> a * x  >= b -> x >= ceiling b a.
Proof.
  unfold ceiling.
  intros.
  generalize (Z_div_mod b a H).
  destruct (Zdiv_eucl b a).
  intros.
  destruct H1.
  destruct H2.
  subst.
  destruct (Ztrichotomy z0 0) as [ HH1 | [HH2 | HH3]]; destruct z0 ; try auto with zarith ; try discriminate.
  assert (HH :x >= z \/ x < z) by (destruct (Ztrichotomy x z) ; auto with zarith).
  destruct HH ;auto.
  generalize (Zmult_lt_compat_l _ _ _ H3 H1).
  auto with zarith.
  clear H2.
  assert (HH :x >= z +1 \/ x <= z) by (destruct (Ztrichotomy x z) ; intuition (auto with zarith)).
  destruct HH ;auto.
  assert (0 < a) by auto with zarith.
  generalize (Zmult_lt_0_le_compat_r _ _ _ H2 H1).
  intros.
  rewrite Zmult_comm  in H4.
  rewrite (Zmult_comm z)  in H4.
  auto with zarith.
Qed.

Lemma narrow_interval_upper_bound : forall a b x, a > 0 -> a * x  <= b -> x <= Zdiv b a.
Proof.
  unfold Zdiv.
  intros.
  generalize (Z_div_mod b a H).
  destruct (Zdiv_eucl b a).
  intros.
  destruct H1.
  destruct H2.
  subst.
  assert (HH :x <= z \/ z <= x -1) by (destruct (Ztrichotomy x z) ; intuition (auto with zarith)).
  destruct HH ;auto.
  assert (0 < a) by auto with zarith.
  generalize (Zmult_lt_0_le_compat_r _ _ _ H4 H1).
  intros.
  ring_simplify in H5.
  rewrite Zmult_comm in H5.
  auto with zarith.
Qed.

Require Import QArith.

Inductive ZArithProof : Type :=
| DoneProof
| RatProof : ZWitness -> ZArithProof -> ZArithProof
| CutProof : ZWitness -> ZArithProof -> ZArithProof
| EnumProof : ZWitness -> ZWitness -> list ZArithProof -> ZArithProof.

(* n/d <= x  -> d*x - n >= 0 *)
(*
Definition makeLb (v:PExpr Z) (q:Q) : NFormula Z :=
  let (n,d) := q in (PEsub (PEmul (PEc (Zpos d)) v) (PEc  n),NonStrict).

(* x <= n/d  -> d * x <= d  *)
Definition makeUb (v:PExpr Z) (q:Q) : NFormula Z :=
  let (n,d) := q in
    (PEsub (PEc n) (PEmul (PEc (Zpos d)) v), NonStrict).

Definition qceiling (q:Q) : Z :=
  let (n,d) := q in ceiling n (Zpos d).

Definition qfloor (q:Q) : Z :=
  let (n,d) := q in Zdiv n (Zpos d).

Definition makeLbCut (v:PExprC Z) (q:Q) : NFormula Z :=
  (PEsub v  (PEc (qceiling  q)), NonStrict).

Definition neg_nformula (f : NFormula Z) :=
  let (e,o) := f in
    (PEopp (PEadd e (PEc 1%Z)), o).
    
Lemma neg_nformula_sound : forall env f, snd f = NonStrict ->( ~ (Zeval_nformula env (neg_nformula f)) <-> Zeval_nformula env f).
Proof.
  unfold neg_nformula.
  destruct f. 
  simpl.
  intros ; subst ; simpl in *.
  split;  auto with zarith.
Qed.
*)

(* In order to compute the 'cut', we need to express a polynomial P as a * Q + b.
   - b is the constant
   - a is the gcd of the other coefficient.
*)
Require Import Znumtheory. 

Definition isZ0 (x:Z) := 
  match x with
    | Z0 => true
    | _  => false
  end.

Lemma isZ0_0 : forall x, isZ0 x = true <-> x = 0.
Proof.
  destruct x ; simpl ; intuition congruence.
Qed.

Lemma isZ0_n0 : forall x, isZ0 x = false <-> x <> 0.
Proof.
  destruct x ; simpl ; intuition congruence.
Qed.

Definition ZgcdM (x y : Z) := Zmax (Zgcd x y) 1.


Fixpoint Zgcd_pol (p : PolC Z) : (Z * Z) :=
  match p with
    | Pc c => (0,c)
    | Pinj _ p => Zgcd_pol p
    | PX p _ q => 
      let (g1,c1) := Zgcd_pol p in
        let (g2,c2) := Zgcd_pol q in
          (ZgcdM (ZgcdM g1 c1) g2 , c2)
  end.

(*Eval compute in (Zgcd_pol ((PX (Pc (-2)) 1 (Pc 4)))).*)


Fixpoint Zdiv_pol (p:PolC Z) (x:Z) : PolC Z :=
  match p with
    | Pc c => Pc (Zdiv c x)
    | Pinj j p => Pinj j (Zdiv_pol p x)
    | PX p j q => PX (Zdiv_pol p x) j (Zdiv_pol q x)
  end.

Inductive Zdivide_pol (x:Z): PolC Z -> Prop :=
| Zdiv_Pc : forall c, (x | c) -> Zdivide_pol x (Pc c)
| Zdiv_Pinj : forall p, Zdivide_pol x p ->  forall j, Zdivide_pol x (Pinj j p)
| Zdiv_PX   : forall p q, Zdivide_pol x p -> Zdivide_pol x q -> forall j, Zdivide_pol x (PX p j q).


Lemma Zdiv_pol_correct : forall a p, 0 < a -> Zdivide_pol a p  -> 
  forall env, eval_pol env p =  a * eval_pol env (Zdiv_pol p a).
Proof.
  intros until 2.
  induction H0.
  (* Pc *)
  simpl.
  intros.
  apply Zdivide_Zdiv_eq ; auto.
  (* Pinj *)
  simpl.
  intros.
  apply IHZdivide_pol.
  (* PX *)
  simpl.
  intros.
  rewrite IHZdivide_pol1.
  rewrite IHZdivide_pol2.
  ring.
Qed.

Lemma Zgcd_pol_ge : forall p, fst (Zgcd_pol p) >= 0.
Proof.
  induction p.
  simpl. auto with zarith.
  simpl. auto.
  simpl.
  case_eq (Zgcd_pol p1).
  case_eq (Zgcd_pol p3).
  intros.
  simpl.
  unfold ZgcdM.
  generalize (Zgcd_is_pos z1 z2).
  generalize (Zmax_spec (Zgcd z1 z2) 1).
  generalize (Zgcd_is_pos (Zmax (Zgcd z1 z2) 1) z).
  generalize (Zmax_spec (Zgcd (Zmax (Zgcd z1 z2) 1) z) 1).
  auto with zarith.
Qed.

Lemma Zdivide_pol_Zdivide : forall p x y, Zdivide_pol x p -> (y | x) ->  Zdivide_pol y p.
Proof.
  intros.
  induction H.
  constructor.
  apply Zdivide_trans with (1:= H0) ; assumption.
  constructor. auto.
  constructor ; auto.
Qed.
  
Lemma Zdivide_pol_one : forall p, Zdivide_pol 1 p.
Proof.
  induction p ; constructor ; auto.
  exists c. ring.
Qed.
  

Lemma Zgcd_minus : forall a b c,  0 < Zgcd a b -> (a | c - b ) -> (Zgcd a b  | c).
Proof.
  intros.
  destruct H0.
  exists  (q * (a / (Zgcd a b)) + (b / (Zgcd a b))).
  rewrite Zmult_comm.
   rewrite Zmult_plus_distr_r.
   replace  (Zgcd a b * (q * (a / Zgcd a b))) with (q * ((Zgcd a b) * (a / Zgcd a b))) by ring.
  rewrite <- Zdivide_Zdiv_eq ; auto.
  rewrite <- Zdivide_Zdiv_eq ; auto.
  auto with zarith.
  destruct (Zgcd_is_gcd a b) ; auto.
  destruct (Zgcd_is_gcd a b) ; auto.
Qed.
  
Lemma Zdivide_pol_sub : forall p a b, 
  0 < Zgcd a b -> 
  Zdivide_pol a (PsubC Zminus p b) -> 
   Zdivide_pol (Zgcd a b) p.
Proof.
  induction p.
  simpl.
  intros. inversion H0.
  constructor. 
  apply Zgcd_minus ; auto.
  intros.
  constructor.
  simpl in H0. inversion H0 ; subst; clear H0.
  apply IHp ; auto.
  simpl. intros.
  inv H0.
  constructor.
  apply Zdivide_pol_Zdivide with (1:= H3).
  destruct (Zgcd_is_gcd a b) ; assumption.
  apply IHp2 ; assumption.
Qed.

Lemma Zgcd_com : forall a b, Zgcd a b = Zgcd b a.
Proof.
  intros.
  apply Zis_gcd_gcd.
  apply Zgcd_is_pos.
  destruct (Zgcd_is_gcd b a).
  constructor ; auto.
Qed.

Lemma Zgcd_ass : forall a b c, Zgcd (Zgcd a b) c = Zgcd a (Zgcd b c).
Proof.
  intros.
  apply Zis_gcd_gcd.
  apply (Zgcd_is_pos a (Zgcd b c)).
  constructor ; auto.
  destruct (Zgcd_is_gcd  a b).
  apply H1.
  destruct (Zgcd_is_gcd  a (Zgcd b c)) ; auto.
  destruct (Zgcd_is_gcd  a (Zgcd b c)) ; auto.
  destruct (Zgcd_is_gcd  b c) ; auto.
  apply Zdivide_trans with (2:= H5);auto.
  destruct (Zgcd_is_gcd b c).
  destruct (Zgcd_is_gcd a  (Zgcd b c)).
  apply Zdivide_trans with (2:= H0);auto.
  (* 3 *)
  intros.
  destruct (Zgcd_is_gcd a (Zgcd b c)).
  apply H3.
  destruct (Zgcd_is_gcd a b).
  apply Zdivide_trans with (2:= H4) ; auto.
  destruct (Zgcd_is_gcd b c).
  apply H6. 
  destruct (Zgcd_is_gcd a b).
  apply Zdivide_trans with (2:= H8) ; auto.
  auto.  
Qed.


Lemma Zdivide_pol_sub_0 : forall p a, 
  Zdivide_pol a (PsubC Zminus p 0) -> 
   Zdivide_pol a p.
Proof.
  induction p.
  simpl.
  intros. inversion H.
  constructor.  replace (c - 0) with c in H1 ; auto with zarith.
  intros.
  constructor.
  simpl in H. inversion H ; subst; clear H.
  apply IHp ; auto.
  simpl. intros.
  inv H.
  constructor. auto.
  apply IHp2 ; assumption.
Qed.


Lemma Zgcd_pol_div : forall p g c, 
  Zgcd_pol p = (g, c) -> Zdivide_pol g (PsubC Zminus p c).
Proof.
  induction p ; simpl.
  (* Pc *)
  intros. inv H.
  constructor.
  exists 0. now ring.
  (* Pinj *)
  intros.
  constructor.  apply IHp ; auto.
  (* PX *)
  intros g c.
  case_eq (Zgcd_pol p1) ; case_eq (Zgcd_pol p3) ; intros.
  inv H1.
  unfold ZgcdM at 1.
  destruct (Zmax_spec (Zgcd (ZgcdM z1 z2) z) 1) as [HH1 | HH1];
  destruct HH1 as [HH1 HH1'] ; rewrite HH1'.
  constructor.
  apply Zdivide_pol_Zdivide with (x:= ZgcdM z1 z2).
  unfold ZgcdM.
  destruct (Zmax_spec  (Zgcd z1 z2)  1) as [HH2 | HH2].
  destruct HH2.
  rewrite H2.
  apply Zdivide_pol_sub ; auto.
  auto with zarith.
  destruct HH2. rewrite H2.
  apply Zdivide_pol_one.
  unfold ZgcdM in HH1. unfold ZgcdM.
  destruct (Zmax_spec  (Zgcd z1 z2)  1) as [HH2 | HH2].
  destruct HH2. rewrite H2 in *.
  destruct (Zgcd_is_gcd (Zgcd z1 z2) z); auto.
  destruct HH2. rewrite H2.
  destruct (Zgcd_is_gcd 1  z); auto.
  apply Zdivide_pol_Zdivide with (x:= z).
  apply (IHp2 _ _ H); auto.
  destruct (Zgcd_is_gcd (ZgcdM z1 z2) z); auto.
  constructor. apply Zdivide_pol_one.
  apply Zdivide_pol_one.
Qed.


  

Lemma Zgcd_pol_correct_lt : forall p env g c, Zgcd_pol p = (g,c) -> 0 < g -> eval_pol env p = g * (eval_pol env (Zdiv_pol (PsubC Zminus p c) g))  + c.
Proof.
  intros.
  rewrite <- Zdiv_pol_correct ; auto.
  rewrite (RingMicromega.PsubC_ok Zsor ZSORaddon).
  unfold eval_pol. ring.
  (**)
  apply Zgcd_pol_div ; auto.
Qed.



Definition makeCuttingPlane (p : PolC Z) : PolC  Z * Z := 
  let (g,c) := Zgcd_pol p in
    if Zgt_bool g Z0 
      then (Zdiv_pol (PsubC Zminus p c) g , Zopp (ceiling (Zopp c) g))
      else (p,Z0).


Definition genCuttingPlane (f : NFormula Z) : option (PolC Z * Z * Op1) :=
  let (e,op) := f in
    match op with
      | Equal => let (g,c) := Zgcd_pol e in
        if andb (Zgt_bool g Z0) (andb (Zgt_bool c Z0) (negb (Zeq_bool (Zgcd g c) g)))
          then None (* inconsistent *)
          else Some (e, Z0,op) (* It could still be inconsistent -- but not a cut *)
      | NonEqual => Some (e,Z0,op)
      | Strict   =>  let (p,c) := makeCuttingPlane (PsubC Zminus e 1) in
        Some (p,c,NonStrict)
      | NonStrict => let (p,c) := makeCuttingPlane e  in
        Some (p,c,NonStrict)
    end.

Definition nformula_of_cutting_plane (t : PolC Z * Z * Op1) : NFormula Z :=
  let (e_z, o) := t in
    let (e,z) := e_z in
      (padd e (Pc z) , o).

Definition is_pol_Z0 (p : PolC Z) : bool :=
  match p with
    | Pc Z0 => true
    |   _   => false
  end.

Lemma is_pol_Z0_eval_pol : forall p, is_pol_Z0 p = true -> forall env, eval_pol env p = 0.
Proof.
  unfold is_pol_Z0.
  destruct p ; try discriminate.
  destruct z ; try discriminate.
  reflexivity.
Qed.
  




Definition eval_Psatz  : list (NFormula Z) -> ZWitness ->  option (NFormula Z) :=
  eval_Psatz 0 1 Zplus Zmult Zeq_bool Zle_bool.


Definition check_inconsistent := check_inconsistent 0 Zeq_bool Zle_bool.



Fixpoint ZChecker (l:list (NFormula Z)) (pf : ZArithProof)  {struct pf} : bool :=
  match pf with
    | DoneProof => false 
    | RatProof w pf => 
      match eval_Psatz l w  with
        | None => false
        | Some f => 
          if check_inconsistent f then true
            else ZChecker (f::l) pf
      end
    | CutProof w pf => 
      match eval_Psatz l w with
        | None => false
        | Some f => 
          match genCuttingPlane f with
            | None => true
            | Some cp => ZChecker (nformula_of_cutting_plane cp::l) pf
          end
      end
    | EnumProof w1 w2 pf => 
      match eval_Psatz l w1 , eval_Psatz l w2 with
        |  Some f1 , Some f2 => 
          match genCuttingPlane f1 , genCuttingPlane f2 with
            |Some (e1,z1,op1) , Some (e2,z2,op2) => 
              match op1 , op2 with
                | NonStrict , NonStrict => 
                  if is_pol_Z0 (padd e1 e2)
                    then
                      (fix label (pfs:list ZArithProof) :=
                        fun lb ub => 
                          match pfs with
                            | nil => if Zgt_bool lb ub then true else false
                            | pf::rsr => andb (ZChecker  ((psub e1 (Pc lb), Equal) :: l) pf) (label rsr (Zplus lb 1%Z) ub) 
                          end)
                      pf (Zopp z1)  z2
                    else false
                |   _    ,   _   => false
              end
            |   _   ,  _ => false
          end
        |   _   , _  => false
      end
      end.



Fixpoint bdepth (pf : ZArithProof) : nat :=
  match pf with
    | DoneProof  => O
    | RatProof _ p =>  S (bdepth p)
    | CutProof _  p =>   S  (bdepth p)
    | EnumProof _ _ l => S (List.fold_right (fun pf x => Max.max (bdepth pf) x)   O l)
  end.

Require Import Wf_nat.

Lemma in_bdepth : forall l a b  y, In y l ->  ltof ZArithProof bdepth y (EnumProof a b  l).
Proof.
  induction l.
  (* nil *)
  simpl.
  tauto.
  (* cons *)
  simpl.
  intros.
  destruct H.
  subst.
  unfold ltof.
  simpl.
  generalize (         (fold_right
            (fun (pf : ZArithProof) (x : nat) => Max.max (bdepth pf) x) 0%nat l)).
  intros.
  generalize (bdepth y) ; intros.
  generalize (Max.max_l n0 n) (Max.max_r n0 n).
  auto with zarith.
  generalize (IHl a0 b  y  H).
  unfold ltof.
  simpl.
  generalize (      (fold_right (fun (pf : ZArithProof) (x : nat) => Max.max (bdepth pf) x) 0%nat
         l)).
  intros.
  generalize (Max.max_l (bdepth a) n) (Max.max_r (bdepth a) n).
  auto with zarith.
Qed.


Lemma eval_Psatz_sound : forall env w l f', 
  make_conj (eval_nformula env) l -> 
  eval_Psatz l w  = Some f' ->  eval_nformula env f'.
Proof.
  intros.
  apply (eval_Psatz_Sound Zsor ZSORaddon) with (l:=l) (e:= w) ; auto.
  apply make_conj_in ; auto.  
Qed.

Lemma makeCuttingPlane_sound : forall env e e' c, 
  eval_nformula env (e, NonStrict) -> 
  makeCuttingPlane e = (e',c) -> 
  eval_nformula env (nformula_of_cutting_plane (e', c, NonStrict)).
Proof.
  unfold nformula_of_cutting_plane.
  unfold eval_nformula. unfold RingMicromega.eval_nformula.
  unfold eval_op1.
  intros.
  rewrite (RingMicromega.eval_pol_add Zsor ZSORaddon).
  simpl.
  (**)
  unfold makeCuttingPlane in H0.
  revert H0.
  case_eq (Zgcd_pol e) ; intros g c0.
  generalize (Zgt_cases g 0) ; destruct (Zgt_bool g 0).
  intros.
  inv H2.
  change (RingMicromega.eval_pol 0 Zplus Zmult (fun x : Z => x)) with eval_pol in *.
  apply Zgcd_pol_correct_lt with (env:=env) in H1.
  generalize (narrow_interval_lower_bound g (- c0) (eval_pol env (Zdiv_pol (PsubC Zminus e c0) g)) H0).
  auto with zarith.
  auto with zarith.
  (* g <= 0 *)
  intros. inv H2. auto with zarith.
Qed.
  

Lemma cutting_plane_sound : forall env f p, 
  eval_nformula env f -> 
  genCuttingPlane f = Some p ->
   eval_nformula env (nformula_of_cutting_plane p).
Proof.
  unfold genCuttingPlane.
  destruct f as [e op].
  destruct op.
  (* Equal *)
  destruct p as [[e' z] op].
  case_eq (Zgcd_pol e) ; intros g c.
  destruct (Zgt_bool g 0 && (Zgt_bool c 0 && negb (Zeq_bool (Zgcd g c) g))) ; [discriminate|].
  intros. inv H1. unfold nformula_of_cutting_plane.
  unfold eval_nformula in *.
  unfold RingMicromega.eval_nformula in *.
  unfold eval_op1 in *.
  rewrite (RingMicromega.eval_pol_add Zsor ZSORaddon).
  simpl. rewrite H0. reflexivity.
  (* NonEqual *)
  intros.
  inv H0.
  unfold eval_nformula in *.
  unfold RingMicromega.eval_nformula in *.
  unfold nformula_of_cutting_plane.
  unfold eval_op1 in *.
  rewrite (RingMicromega.eval_pol_add Zsor ZSORaddon).
  simpl. auto with zarith.
  (* Strict *)
  destruct p as [[e' z] op].  
  case_eq (makeCuttingPlane (PsubC Zminus e 1)).
  intros.
  inv H1.
  apply makeCuttingPlane_sound with (env:=env) (2:= H).
  simpl in *.
  rewrite (RingMicromega.PsubC_ok Zsor ZSORaddon).  
  auto with zarith.
  (* NonStrict *)
  destruct p as [[e' z] op].  
  case_eq (makeCuttingPlane e).
  intros.
  inv H1.
  apply makeCuttingPlane_sound with (env:=env) (2:= H).
  assumption.
Qed.  

Lemma negb_true : forall x, negb x = true <-> x = false.
Proof.
  destruct x ; simpl; intuition.
Qed.


Lemma Zgcd_not_max : forall a b, 0 <=  a -> Zgcd a b <> a -> ~ (a | b).
Proof.
  intros.
  intro. apply H0.
  apply Zis_gcd_gcd; auto.
  constructor ; auto.
  exists 1. ring.
Qed.

Lemma  Zmod_Zopp_Zdivide : forall a b , a <> 0 -> (- b) mod a = 0 -> (a | b). 
Proof.
  unfold Zmod.
  intros a b.
  generalize (Z_div_mod_full (-b) a).
  destruct (Zdiv_eucl (-b) a).
  intros.
  subst.
  exists (-z). 
  apply H in H0. destruct H0.
  rewrite <- Zopp_mult_distr_l.
  rewrite Zmult_comm. auto with zarith.
Qed.

Lemma ceiling_not_div : forall a b, a <> 0 -> ~ (a | b) -> ceiling (- b) a = Zdiv (-b) a + 1.
Proof.
  unfold ceiling.
  intros.
  assert ((-b) mod a <> 0).
   generalize (Zmod_Zopp_Zdivide a b) ; tauto.
  revert H1.
  unfold Zdiv, Zmod.
  generalize (Z_div_mod_full (-b) a).
  destruct (Zdiv_eucl (-b) a).
  intros.
  destruct z0 ; congruence.
Qed.


Lemma  genCuttingPlaneNone : forall env f, 
  genCuttingPlane f = None -> 
  eval_nformula env f -> False.
Proof.
  unfold genCuttingPlane.
  destruct f.
  destruct o.
  case_eq (Zgcd_pol p) ; intros g c.
  case_eq (Zgt_bool g 0 && (Zgt_bool c 0 && negb (Zeq_bool (Zgcd g c) g))).
  intros. 
  flatten_bool.
  rewrite negb_true in H5.
  apply Zeq_bool_neq in H5.
  rewrite <- Zgt_is_gt_bool in H3.
  rewrite <- Zgt_is_gt_bool in H.
  simpl in H2.
  change (RingMicromega.eval_pol 0 Zplus Zmult (fun z => z)) with eval_pol in H2.
  rewrite Zgcd_pol_correct_lt with (1:= H0) in H2; auto with zarith.
  revert H2.
  generalize (eval_pol env (Zdiv_pol (PsubC Zminus p c) g)) ; intro x.
  intros.
  assert (g * x >= -c) by auto with zarith.
  assert (g * x <= -c) by auto with zarith.
  apply narrow_interval_lower_bound in H4 ; auto.
  apply narrow_interval_upper_bound in H6 ; auto.
  apply Zgcd_not_max in H5; auto with zarith.
  rewrite ceiling_not_div in H4. 
  auto with zarith.
  auto with zarith.
  auto.
  (**)
  discriminate.
  discriminate.
  destruct (makeCuttingPlane (PsubC Zminus p 1)) ; discriminate.
  destruct (makeCuttingPlane p) ; discriminate.
Qed.


  
Lemma ZChecker_sound : forall w l, ZChecker l w = true -> forall env, make_impl  (eval_nformula env)  l False.
Proof.
  induction w    using (well_founded_ind (well_founded_ltof _ bdepth)).
  destruct w as [ | w pf | w pf | w1 w2 pf].
  (* DoneProof *)
  simpl. discriminate.
  (* RatProof *)
  simpl.
  intro l. case_eq (eval_Psatz l w) ; [| discriminate].
  intros f Hf. 
  case_eq (check_inconsistent f).
  intros.
  apply (checker_nf_sound Zsor ZSORaddon l w).
  unfold check_normalised_formulas.  unfold eval_Psatz in Hf. rewrite Hf.
  unfold check_inconsistent in H0. assumption.
  intros.
  assert (make_impl  (eval_nformula env) (f::l) False).
   apply H with (2:= H1).
   unfold ltof.
   simpl.
   auto with arith.
  destruct f.
  rewrite <- make_conj_impl in H2.
  rewrite make_conj_cons in H2.
  rewrite <- make_conj_impl.
  intro. 
  apply H2.
  split ; auto.
  apply eval_Psatz_sound with (2:= Hf) ; assumption.
  (* CutProof *)
  simpl.
  intro l.
  case_eq (eval_Psatz l w) ; [ | discriminate].
  intros f' Hlc.
  case_eq (genCuttingPlane f'). 
  intros.
  assert (make_impl (eval_nformula env) (nformula_of_cutting_plane p::l) False).
   eapply (H pf) ; auto.
   unfold ltof.
   simpl.
   auto with arith.
  rewrite <- make_conj_impl in H2.
  rewrite make_conj_cons in H2.
  rewrite <- make_conj_impl.
  intro. 
  apply H2.
  split ; auto.
  apply eval_Psatz_sound with (env:=env) in Hlc.
  apply cutting_plane_sound with (1:= Hlc) (2:= H0).
  auto.
  (* genCuttingPlane = None *)
  intros.
  rewrite <- make_conj_impl.
  intros.
  apply eval_Psatz_sound with (2:= Hlc) in H2.
  apply genCuttingPlaneNone with (2:= H2) ; auto.
  (* EnumProof *)
  intro.
  simpl.
  case_eq (eval_Psatz l w1) ; [  | discriminate].
  case_eq (eval_Psatz l w2) ; [  | discriminate].
  intros f1 Hf1 f2 Hf2.
  case_eq (genCuttingPlane f2) ;  [  | discriminate].
  destruct p as [ [p1 z1] op1].
  case_eq (genCuttingPlane f1) ;  [  | discriminate].
  destruct p as [ [p2 z2] op2].
  case_eq op1 ; case_eq op2 ; try discriminate.
  case_eq (is_pol_Z0 (padd p1 p2)) ; try discriminate.
  intros.
  (* get the bounds of the enum *)
  rewrite <- make_conj_impl.
  intro.
  assert (-z1 <= eval_pol env p1 <= z2).
   split.
   apply  eval_Psatz_sound with (env:=env) in Hf2 ; auto.
   apply cutting_plane_sound with (1:= Hf2) in H4.
   unfold nformula_of_cutting_plane in H4.
   unfold eval_nformula in H4.
   unfold RingMicromega.eval_nformula in H4.
   change (RingMicromega.eval_pol 0 Zplus Zmult (fun x : Z => x)) with eval_pol in H4.
   unfold eval_op1 in H4.
   rewrite eval_pol_add in H4. simpl in H4. 
   auto with zarith.
   (**)
   apply is_pol_Z0_eval_pol with (env := env) in H0.
   rewrite eval_pol_add in H0.
   replace (eval_pol env p1) with (- eval_pol env p2) by omega.
   apply  eval_Psatz_sound with (env:=env) in Hf1 ; auto.
   apply cutting_plane_sound with (1:= Hf1) in H3.
   unfold nformula_of_cutting_plane in H3.
   unfold eval_nformula in H3.
   unfold RingMicromega.eval_nformula in H3.
   change (RingMicromega.eval_pol 0 Zplus Zmult (fun x : Z => x)) with eval_pol in H3.
   unfold eval_op1 in H3.
   rewrite eval_pol_add in H3. simpl in H3. 
   omega.
  revert H5.
  set (FF := (fix label (pfs : list ZArithProof) (lb ub : Z) {struct pfs} : bool :=
    match pfs with
      | nil => if Z_gt_dec lb ub then true else false
      | pf :: rsr =>
        (ZChecker ((PsubC Zminus p1  lb, Equal) :: l) pf &&
          label rsr (lb + 1)%Z ub)%bool
    end)).
  intros.
  assert (HH :forall x, -z1 <= x <= z2 -> exists pr, 
    (In pr pf /\
      ZChecker  ((PsubC Zminus p1 x,Equal) :: l) pr = true)%Z).
  clear H.
  clear H0 H1 H2 H3 H4 H7.
  revert H5.
  generalize (-z1). clear z1. intro z1.
  revert z1 z2.
  induction pf;simpl ;intros.
  generalize (Zgt_cases z1 z2).
  destruct (Zgt_bool z1 z2).
  intros.
  apply False_ind ; omega.
  discriminate.
  flatten_bool.
  assert (HH:(x = z1 \/ z1 +1 <=x)%Z) by omega.
  destruct HH.
  subst.
  exists a ; auto.
  assert (z1 + 1 <= x <= z2)%Z by omega.
  destruct (IHpf _ _ H1 _ H3).
  destruct H4.
  exists x0 ; split;auto.
  (*/asser *)
  destruct (HH _ H7) as [pr [Hin Hcheker]].
  assert (make_impl (eval_nformula env) ((PsubC Zminus p1 (eval_pol env p1),Equal) :: l) False).
   apply (H pr);auto.
   apply in_bdepth ; auto.
  rewrite <- make_conj_impl in H8.
  apply H8.
  rewrite  make_conj_cons.
  split ;auto.
  unfold  eval_nformula.
  unfold RingMicromega.eval_nformula.
  simpl.
  rewrite (RingMicromega.PsubC_ok Zsor ZSORaddon).
  unfold eval_pol. ring.
Qed.

Definition ZTautoChecker  (f : BFormula (Formula Z)) (w: list ZArithProof): bool :=
  @tauto_checker (Formula Z) (NFormula Z) normalise negate  ZArithProof ZChecker f w.

Lemma ZTautoChecker_sound : forall f w, ZTautoChecker f w = true -> forall env, eval_f  (Zeval_formula env)  f.
Proof.
  intros f w.
  unfold ZTautoChecker.
  apply (tauto_checker_sound  Zeval_formula eval_nformula).
  apply Zeval_nformula_dec.
  intros env t.
  rewrite normalise_correct ; auto.
  intros env t.
  rewrite negate_correct ; auto.
  intros t w0.
  apply ZChecker_sound.
Qed.


Open Scope Z_scope.

  
(** To ease bindings from ml code **)
(*Definition varmap := Quote.varmap.*)
Definition make_impl := Refl.make_impl.
Definition make_conj := Refl.make_conj.

Require VarMap.

(*Definition varmap_type := VarMap.t Z. *)
Definition env := PolEnv Z.
Definition node := @VarMap.Node Z.
Definition empty := @VarMap.Empty Z.
Definition leaf := @VarMap.Leaf Z.

Definition coneMember := ZWitness.

Definition eval := eval_formula.

Definition prod_pos_nat := prod positive nat.

Definition n_of_Z (z:Z) : BinNat.N :=
  match z with
    | Z0 => N0
    | Zpos p => Npos p
    | Zneg p => N0
  end.

(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
 

