(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2011                             *)
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

Lemma Zsor : SOR 0 1 Z.add Z.mul Z.sub Z.opp (@eq Z) Z.le Z.lt.
Proof.
  constructor ; intros ; subst ; try (intuition (auto  with zarith)).
  apply Zsth.
  apply Zth.
  destruct (Z.lt_trichotomy n m) ; intuition.
  apply Z.mul_pos_pos ; auto.
Qed.

Lemma ZSORaddon :
  SORaddon 0 1 Z.add Z.mul Z.sub Z.opp  (@eq Z) Z.le (* ring elements *)
  0%Z 1%Z Z.add Z.mul Z.sub Z.opp (* coefficients *)
  Zeq_bool Z.leb
  (fun x => x) (fun x => x) (pow_N 1 Z.mul).
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
    | PEX _ x => env x
    | PEadd e1 e2 => Zeval_expr env e1 + Zeval_expr env e2
    | PEmul e1 e2 => Zeval_expr env e1 * Zeval_expr env e2
    | PEpow e1 n  => Z.pow (Zeval_expr env e1) (Z.of_N n)
    | PEsub e1 e2 => (Zeval_expr env e1) - (Zeval_expr env e2)
    | PEopp e   => Z.opp (Zeval_expr env e)
  end.

Definition eval_expr := eval_pexpr  Z.add Z.mul Z.sub Z.opp (fun x => x) (fun x => x) (pow_N 1 Z.mul).

Lemma ZNpower : forall r n, r ^ Z.of_N n = pow_N 1 Z.mul r n.
Proof.
  destruct n.
  reflexivity.
  simpl.
  unfold Z.pow_pos.
  replace (pow_pos Z.mul r p) with (1 * (pow_pos Z.mul r p)) by ring.
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
| OpLe => Z.le
| OpGe => Z.ge
| OpLt => Z.lt
| OpGt => Z.gt
end.

Definition Zeval_formula (env : PolEnv Z) (f : Formula Z):=
  let (lhs, op, rhs) := f in
    (Zeval_op2 op) (Zeval_expr env lhs) (Zeval_expr env rhs).

Definition Zeval_formula' :=
  eval_formula  Z.add Z.mul Z.sub Z.opp (@eq Z) Z.le Z.lt (fun x => x) (fun x => x) (pow_N 1 Z.mul).

Lemma Zeval_formula_compat : forall env f, Zeval_formula env f <-> Zeval_formula' env f.
Proof.
  destruct f ; simpl.
  rewrite Zeval_expr_compat. rewrite Zeval_expr_compat.
  unfold eval_expr.
  generalize (eval_pexpr Z.add Z.mul Z.sub Z.opp (fun x : Z => x)
        (fun x : N => x) (pow_N 1 Z.mul) env Flhs).
  generalize ((eval_pexpr Z.add Z.mul Z.sub Z.opp (fun x : Z => x)
        (fun x : N => x) (pow_N 1 Z.mul) env Frhs)).
  destruct Fop ; simpl; intros ; intuition (auto with zarith).
Qed.


Definition eval_nformula :=
  eval_nformula 0 Z.add Z.mul  (@eq Z) Z.le Z.lt (fun x => x) .

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

Definition ZWeakChecker := check_normalised_formulas 0 1 Z.add Z.mul Zeq_bool Z.leb.

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

Definition psub  := psub Z0  Z.add Z.sub Z.opp Zeq_bool.
Declare Equivalent Keys psub RingMicromega.psub.

Definition padd  := padd Z0  Z.add Zeq_bool.
Declare Equivalent Keys padd RingMicromega.padd.

Definition norm  := norm 0 1 Z.add Z.mul Z.sub Z.opp Zeq_bool.
Declare Equivalent Keys norm RingMicromega.norm.

Definition eval_pol := eval_pol Z.add Z.mul (fun x => x).
Declare Equivalent Keys eval_pol RingMicromega.eval_pol.

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

Require Import Coq.micromega.Tauto BinNums.

Definition normalise (t:Formula Z) : cnf (NFormula Z) :=
  List.map  (fun x => x::nil) (xnormalise t).


Lemma normalise_correct : forall env t, eval_cnf eval_nformula env (normalise t) <-> Zeval_formula env t.
Proof.
  unfold normalise, xnormalise; cbn -[padd]; intros env t.
  rewrite Zeval_formula_compat.
  unfold eval_cnf, eval_clause.
  destruct t as [lhs o rhs]; case_eq o; cbn -[padd];
    repeat rewrite eval_pol_sub;
      repeat rewrite eval_pol_add;
      repeat rewrite <- eval_pol_norm ; simpl in *;
  unfold eval_expr;
  generalize (   eval_pexpr  Z.add Z.mul Z.sub Z.opp (fun x : Z => x)
    (fun x : N => x) (pow_N 1 Z.mul) env lhs);
  generalize (eval_pexpr  Z.add Z.mul Z.sub Z.opp (fun x : Z => x)
    (fun x : N => x) (pow_N 1 Z.mul) env rhs) ; intros z1 z2 ; intros ; subst;
    intuition (auto with zarith).
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

Lemma negate_correct : forall env t, eval_cnf eval_nformula env (negate t) <-> ~ Zeval_formula env t.
Proof.
Proof.
  Opaque padd.
  intros env t.
  rewrite Zeval_formula_compat.
  unfold negate, xnegate  ; simpl.
  unfold eval_cnf,eval_clause.
  destruct t as [lhs o rhs]; case_eq o; simpl;
    repeat rewrite eval_pol_sub;
      repeat rewrite eval_pol_add;
      repeat rewrite <- eval_pol_norm ; simpl in *;
  unfold eval_expr;
  generalize (   eval_pexpr  Z.add Z.mul Z.sub Z.opp (fun x : Z => x)
    (fun x : N => x) (pow_N 1 Z.mul) env lhs);
  generalize (eval_pexpr  Z.add Z.mul Z.sub Z.opp (fun x : Z => x)
    (fun x : N => x) (pow_N 1 Z.mul) env rhs) ; intros z1 z2 ; intros ; subst;
    intuition (auto with zarith).
  Transparent padd.
Qed.

Definition Zunsat := check_inconsistent 0  Zeq_bool Z.leb.

Definition Zdeduce := nformula_plus_nformula 0 Z.add Zeq_bool.


Definition ZweakTautoChecker (w: list ZWitness) (f : BFormula (Formula Z)) : bool :=
  @tauto_checker (Formula Z) (NFormula Z) Zunsat Zdeduce normalise negate  ZWitness ZWeakChecker f w.

(* To get a complete checker, the proof format has to be enriched *)

Require Import Zdiv.
Open Scope Z_scope.

Definition ceiling (a b:Z) : Z :=
  let (q,r) := Z.div_eucl a b in
    match r with
      | Z0 => q
      | _  => q + 1
    end.


Require Import Znumtheory.

Lemma Zdivide_ceiling : forall a b, (b | a) -> ceiling a b = Z.div a b.
Proof.
  unfold ceiling.
  intros.
  apply Zdivide_mod in H.
  case_eq (Z.div_eucl a b).
  intros.
  change z with (fst (z,z0)).
  rewrite <- H0.
  change (fst (Z.div_eucl a b)) with (Z.div a b).
  change z0 with (snd (z,z0)).
  rewrite <- H0.
  change (snd (Z.div_eucl a b)) with (Z.modulo a b).
  rewrite H.
  reflexivity.
Qed.

Lemma narrow_interval_lower_bound a b x :
  a > 0 -> a * x  >= b -> x >= ceiling b a.
Proof.
  rewrite !Z.ge_le_iff.
  unfold ceiling.
  intros Ha H.
  generalize (Z_div_mod b a Ha).
  destruct (Z.div_eucl b a) as (q,r). intros (->,(H1,H2)).
  destruct r as [|r|r].
  - rewrite Z.add_0_r in H.
    apply Z.mul_le_mono_pos_l in H; auto with zarith.
  - assert (0 < Z.pos r) by easy.
    rewrite Z.add_1_r, Z.le_succ_l.
    apply Z.mul_lt_mono_pos_l with a; auto with zarith.
  - now elim H1.
Qed.

(** NB: narrow_interval_upper_bound is Zdiv.Zdiv_le_lower_bound *)

Require Import QArith.

Inductive ZArithProof :=
| DoneProof
| RatProof : ZWitness -> ZArithProof -> ZArithProof
| CutProof : ZWitness -> ZArithProof -> ZArithProof
| EnumProof : ZWitness -> ZWitness -> list ZArithProof -> ZArithProof
(*| SplitProof :   PolC Z -> ZArithProof -> ZArithProof -> ZArithProof*).



(* n/d <= x  -> d*x - n >= 0 *)


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

Definition ZgcdM (x y : Z) := Z.max (Z.gcd x y) 1.


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
    | Pc c => Pc (Z.div c x)
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
  generalize (Z.gcd_nonneg z1 z2).
  generalize (Zmax_spec (Z.gcd z1 z2) 1).
  generalize (Z.gcd_nonneg (Z.max (Z.gcd z1 z2) 1) z).
  generalize (Zmax_spec (Z.gcd (Z.max (Z.gcd z1 z2) 1) z) 1).
  auto with zarith.
Qed.

Lemma Zdivide_pol_Zdivide : forall p x y, Zdivide_pol x p -> (y | x) ->  Zdivide_pol y p.
Proof.
  intros.
  induction H.
  constructor.
  apply Z.divide_trans with (1:= H0) ; assumption.
  constructor. auto.
  constructor ; auto.
Qed.

Lemma Zdivide_pol_one : forall p, Zdivide_pol 1 p.
Proof.
  induction p ; constructor ; auto.
  exists c. ring.
Qed.

Lemma Zgcd_minus : forall a b c, (a | c - b ) -> (Z.gcd a b | c).
Proof.
  intros a b c (q,Hq).
  destruct (Zgcd_is_gcd a b) as [(a',Ha) (b',Hb) _].
  set (g:=Z.gcd a b) in *; clearbody g.
  exists (q * a' + b').
  symmetry in Hq. rewrite <- Z.add_move_r in Hq.
  rewrite <- Hq, Hb, Ha. ring.
Qed.

Lemma Zdivide_pol_sub : forall p a b,
  0 < Z.gcd a b ->
  Zdivide_pol a (PsubC Z.sub p b) ->
   Zdivide_pol (Z.gcd a b) p.
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

Lemma Zdivide_pol_sub_0 : forall p a,
  Zdivide_pol a (PsubC Z.sub p 0) ->
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
  Zgcd_pol p = (g, c) -> Zdivide_pol g (PsubC Z.sub p c).
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
  destruct (Zmax_spec (Z.gcd (ZgcdM z1 z2) z) 1) as [HH1 | HH1];
  destruct HH1 as [HH1 HH1'] ; rewrite HH1'.
  constructor.
  apply Zdivide_pol_Zdivide with (x:= ZgcdM z1 z2).
  unfold ZgcdM.
  destruct (Zmax_spec  (Z.gcd z1 z2)  1) as [HH2 | HH2].
  destruct HH2.
  rewrite H2.
  apply Zdivide_pol_sub ; auto.
  auto with zarith.
  destruct HH2. rewrite H2.
  apply Zdivide_pol_one.
  unfold ZgcdM in HH1. unfold ZgcdM.
  destruct (Zmax_spec  (Z.gcd z1 z2)  1) as [HH2 | HH2].
  destruct HH2. rewrite H2 in *.
  destruct (Zgcd_is_gcd (Z.gcd z1 z2) z); auto.
  destruct HH2. rewrite H2.
  destruct (Zgcd_is_gcd 1  z); auto.
  apply Zdivide_pol_Zdivide with (x:= z).
  apply (IHp2 _ _ H); auto.
  destruct (Zgcd_is_gcd (ZgcdM z1 z2) z); auto.
  constructor. apply Zdivide_pol_one.
  apply Zdivide_pol_one.
Qed.




Lemma Zgcd_pol_correct_lt : forall p env g c, Zgcd_pol p = (g,c) -> 0 < g -> eval_pol env p = g * (eval_pol env (Zdiv_pol (PsubC Z.sub p c) g))  + c.
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
    if Z.gtb g Z0
      then (Zdiv_pol (PsubC Z.sub p c) g , Z.opp (ceiling (Z.opp c) g))
      else (p,Z0).


Definition genCuttingPlane (f : NFormula Z) : option (PolC Z * Z * Op1) :=
  let (e,op) := f in
    match op with
      | Equal => let (g,c) := Zgcd_pol e in
        if andb (Z.gtb g Z0) (andb (negb (Zeq_bool c Z0)) (negb (Zeq_bool (Z.gcd g c) g)))
          then None (* inconsistent *)
          else (* Could be optimised Zgcd_pol is recomputed *)
            let (p,c) := makeCuttingPlane e  in
              Some (p,c,Equal)
      | NonEqual => Some (e,Z0,op)
      | Strict   =>  let (p,c) := makeCuttingPlane (PsubC Z.sub e 1) in
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
  eval_Psatz 0 1 Z.add Z.mul Zeq_bool Z.leb.


Definition valid_cut_sign (op:Op1) :=
  match op with 
    | Equal => true
    | NonStrict => true
    | _         => false
  end.

Fixpoint ZChecker (l:list (NFormula Z)) (pf : ZArithProof)  {struct pf} : bool :=
  match pf with
    | DoneProof => false
    | RatProof w pf =>
      match eval_Psatz l w  with
        | None => false
        | Some f =>
          if Zunsat f then true
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
               if (valid_cut_sign op1 && valid_cut_sign op2 && is_pol_Z0 (padd e1 e2))
                 then 
                   (fix label (pfs:list ZArithProof) :=
                   fun lb ub =>
                     match pfs with
                       | nil => if Z.gtb lb ub then true else false
                       | pf::rsr => andb (ZChecker  ((psub e1 (Pc lb), Equal) :: l) pf) (label rsr (Z.add lb 1%Z) ub)
                     end)   pf (Z.opp z1)  z2
                  else false
              |   _    ,   _   => true
           end
          |   _   ,  _ => false
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

Lemma makeCuttingPlane_ns_sound : forall env e e' c,
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
  generalize (Zgt_cases g 0) ; destruct (Z.gtb g 0).
  intros.
  inv H2.
  change (RingMicromega.eval_pol Z.add Z.mul (fun x : Z => x)) with eval_pol in *.
  apply Zgcd_pol_correct_lt with (env:=env) in H1.
  generalize (narrow_interval_lower_bound g (- c0) (eval_pol env (Zdiv_pol (PsubC Z.sub e c0) g)) H0).
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
  case_eq (Z.gtb g 0 && (negb (Zeq_bool c 0) && negb (Zeq_bool (Z.gcd g c) g))) ; [discriminate|].
  case_eq (makeCuttingPlane e).
  intros.
  inv H3.
  unfold makeCuttingPlane in H.
  rewrite H1 in H.
  revert H.
  change (eval_pol env e = 0) in H2.
  case_eq (Z.gtb g 0).
  intros.
  rewrite <- Zgt_is_gt_bool in H.  
  rewrite Zgcd_pol_correct_lt with (1:= H1)  in H2; auto with zarith.
  unfold nformula_of_cutting_plane.  
  change (eval_pol env (padd e' (Pc z)) = 0).
  inv H3.
  rewrite eval_pol_add.
  set (x:=eval_pol env (Zdiv_pol (PsubC Z.sub e c) g)) in *; clearbody x.
  simpl.
  rewrite andb_false_iff in H0.
  destruct H0.
  rewrite Zgt_is_gt_bool in H ; congruence.
  rewrite andb_false_iff in H0.
  destruct H0.
  rewrite negb_false_iff in H0.
  apply Zeq_bool_eq in H0.
  subst. simpl.
  rewrite Z.add_0_r, Z.mul_eq_0 in H2.
  intuition auto with zarith.
  rewrite negb_false_iff in H0.
  apply Zeq_bool_eq in H0.
  assert (HH := Zgcd_is_gcd g c).
  rewrite H0 in HH.
  inv HH.
  apply Zdivide_opp_r in H4.
  rewrite Zdivide_ceiling ; auto.
  apply Z.sub_move_0_r.
  apply Z.div_unique_exact ; auto with zarith.
  intros.
  unfold nformula_of_cutting_plane.
  inv H3.
  change (eval_pol env (padd e' (Pc 0)) = 0).
  rewrite eval_pol_add.
  simpl.
  auto with zarith.
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
  case_eq (makeCuttingPlane (PsubC Z.sub e 1)).
  intros.
  inv H1.
  apply makeCuttingPlane_ns_sound with (env:=env) (2:= H).
  simpl in *.
  rewrite (RingMicromega.PsubC_ok Zsor ZSORaddon).
  auto with zarith.
  (* NonStrict *)
  destruct p as [[e' z] op].
  case_eq (makeCuttingPlane e).
  intros.
  inv H1.
  apply makeCuttingPlane_ns_sound with (env:=env) (2:= H).
  assumption.
Qed.

Lemma  genCuttingPlaneNone : forall env f,
  genCuttingPlane f = None ->
  eval_nformula env f -> False.
Proof.
  unfold genCuttingPlane.
  destruct f.
  destruct o.
  case_eq (Zgcd_pol p) ; intros g c.
  case_eq (Z.gtb g 0 && (negb (Zeq_bool c 0) && negb (Zeq_bool (Z.gcd g c) g))).
  intros.
  flatten_bool.
  rewrite negb_true_iff in H5.
  apply Zeq_bool_neq in H5.
  rewrite <- Zgt_is_gt_bool in H3.
  rewrite negb_true_iff in H.
  apply Zeq_bool_neq in H.
  change (eval_pol env p = 0) in H2.
  rewrite Zgcd_pol_correct_lt with (1:= H0) in H2; auto with zarith.
  set (x:=eval_pol env (Zdiv_pol (PsubC Z.sub p c) g)) in *; clearbody x.
  contradict H5.
  apply Zis_gcd_gcd; auto with zarith.
  constructor; auto with zarith.
  exists (-x).
  rewrite Z.mul_opp_l, Z.mul_comm; auto with zarith.
  (**)
  destruct (makeCuttingPlane p);  discriminate.
  discriminate.
  destruct (makeCuttingPlane (PsubC Z.sub p 1)) ; discriminate.
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
  case_eq (Zunsat f).
  intros.
  apply (checker_nf_sound Zsor ZSORaddon l w).
  unfold check_normalised_formulas.  unfold eval_Psatz in Hf. rewrite Hf.
  unfold Zunsat in H0. assumption.
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
  case_eq (genCuttingPlane f2).
  destruct p as [ [p1 z1] op1].
  case_eq (genCuttingPlane f1).
  destruct p as [ [p2 z2] op2].
  case_eq (valid_cut_sign op1 && valid_cut_sign op2 && is_pol_Z0 (padd p1 p2)).
  intros Hcond.
  flatten_bool.
  rename H1 into HZ0.
  rename H2 into Hop1.
  rename H3 into Hop2.
  intros HCutL HCutR Hfix env.
  (* get the bounds of the enum *)
  rewrite <- make_conj_impl.
  intro.
  assert (-z1 <= eval_pol env p1 <= z2).
   split.
   apply  eval_Psatz_sound with (env:=env) in Hf2 ; auto.
   apply cutting_plane_sound with (1:= Hf2) in HCutR.
   unfold nformula_of_cutting_plane in HCutR.
   unfold eval_nformula in HCutR.
   unfold RingMicromega.eval_nformula in HCutR.
   change (RingMicromega.eval_pol Z.add Z.mul (fun x : Z => x)) with eval_pol in HCutR.
   unfold eval_op1 in HCutR.
   destruct op1 ; simpl in Hop1 ; try discriminate;
     rewrite eval_pol_add in HCutR; simpl in HCutR; auto with zarith.
   (**)
   apply is_pol_Z0_eval_pol with (env := env) in HZ0.
   rewrite eval_pol_add in HZ0.
   replace (eval_pol env p1) with (- eval_pol env p2) by omega.
   apply  eval_Psatz_sound with (env:=env) in Hf1 ; auto.
   apply cutting_plane_sound with (1:= Hf1) in HCutL.
   unfold nformula_of_cutting_plane in HCutL.
   unfold eval_nformula in HCutL.
   unfold RingMicromega.eval_nformula in HCutL.
   change (RingMicromega.eval_pol Z.add Z.mul (fun x : Z => x)) with eval_pol in HCutL.
   unfold eval_op1 in HCutL.
   rewrite eval_pol_add in HCutL. simpl in HCutL.
   destruct op2 ; simpl in Hop2 ; try discriminate ;  omega.
  revert Hfix.
  match goal with
    | |- context[?F pf (-z1) z2 = true] => set (FF := F)
  end.
  intros.
  assert (HH :forall x, -z1 <= x <= z2 -> exists pr,
    (In pr pf /\
      ZChecker  ((PsubC Z.sub p1 x,Equal) :: l) pr = true)%Z).
  clear HZ0 Hop1 Hop2 HCutL HCutR H0 H1.
  revert Hfix.
  generalize (-z1). clear z1. intro z1.
  revert z1 z2.
  induction pf;simpl ;intros.
  generalize (Zgt_cases z1 z2).
  destruct (Z.gtb z1 z2).
  intros.
  apply False_ind ; omega.
  discriminate.
  flatten_bool.
  assert (HH:(x = z1 \/ z1 +1 <=x)%Z) by omega.
  destruct HH.
  subst.
  exists a ; auto.
  assert (z1 + 1 <= x <= z2)%Z by omega.
  elim IHpf with (2:=H2) (3:= H4).
  destruct H4.
  intros.
  exists x0 ; split;tauto.
  intros until 1. 
  apply H ; auto. 
  unfold ltof in *.
  simpl in *.
  zify. omega.
  (*/asser *)
  destruct (HH _ H1) as [pr [Hin Hcheker]].
  assert (make_impl (eval_nformula env) ((PsubC Z.sub p1 (eval_pol env p1),Equal) :: l) False).
   apply (H pr);auto.
   apply in_bdepth ; auto.
  rewrite <- make_conj_impl in H2.
  apply H2.
  rewrite  make_conj_cons.
  split ;auto.
  unfold  eval_nformula.
  unfold RingMicromega.eval_nformula.
  simpl.
  rewrite (RingMicromega.PsubC_ok Zsor ZSORaddon).
  unfold eval_pol. ring.
  discriminate.
  (* No cutting plane *)
  intros.
  rewrite <- make_conj_impl.
  intros.
  apply eval_Psatz_sound with (2:= Hf1) in H3.
  apply genCuttingPlaneNone with (2:= H3) ; auto.
  (* No Cutting plane (bis) *)
  intros.
  rewrite <- make_conj_impl.
  intros.
  apply eval_Psatz_sound with (2:= Hf2) in H2.
  apply genCuttingPlaneNone with (2:= H2) ; auto.
Qed.

Definition ZTautoChecker  (f : BFormula (Formula Z)) (w: list ZArithProof): bool :=
  @tauto_checker (Formula Z) (NFormula Z) Zunsat Zdeduce normalise negate  ZArithProof ZChecker f w.

Lemma ZTautoChecker_sound : forall f w, ZTautoChecker f w = true -> forall env, eval_f  (Zeval_formula env)  f.
Proof.
  intros f w.
  unfold ZTautoChecker.
  apply (tauto_checker_sound  Zeval_formula eval_nformula).
  apply Zeval_nformula_dec.
  intros until env.
  unfold eval_nformula. unfold RingMicromega.eval_nformula.
  destruct t.
  apply (check_inconsistent_sound Zsor ZSORaddon) ; auto.
  unfold Zdeduce. apply (nformula_plus_nformula_correct Zsor ZSORaddon).
  intros env t.
  rewrite normalise_correct ; auto.
  intros env t.
  rewrite negate_correct ; auto.
  intros t w0.
  apply ZChecker_sound.
Qed.

Fixpoint xhyps_of_pt (base:nat) (acc : list nat) (pt:ZArithProof)  : list nat :=
  match pt with
    | DoneProof => acc
    | RatProof c pt => xhyps_of_pt (S base ) (xhyps_of_psatz base acc c) pt
    | CutProof c pt => xhyps_of_pt (S base ) (xhyps_of_psatz base acc c) pt
    | EnumProof c1 c2 l =>
      let acc := xhyps_of_psatz base (xhyps_of_psatz base acc c2) c1 in
        List.fold_left (xhyps_of_pt (S base)) l acc
  end.

Definition hyps_of_pt (pt : ZArithProof) : list nat := xhyps_of_pt 0 nil pt.


(*Lemma hyps_of_pt_correct : forall pt l, *)






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

Notation n_of_Z := Z.to_N (only parsing).

(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)


