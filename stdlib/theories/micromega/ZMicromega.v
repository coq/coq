(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

Require Import List.
Require Import Bool.
Require Import OrderedRing.
Require Import RingMicromega.
Require Import ZCoeff.
Require Import Refl.
Require Import BinInt.
Require InitialRing.
Require Import micromega.Tauto.
Local Open Scope Z_scope.

Ltac flatten_bool :=
  repeat match goal with
           [ id : (_ && _)%bool = true |- _ ] =>  destruct (andb_prop _ _ id); clear id
         |  [ id : (_ || _)%bool = true |- _ ] =>  destruct (orb_prop _ _ id); clear id
         end.

Ltac inv H := inversion H ; try subst ; clear H.

Lemma eq_le_iff : forall x, 0 = x  <-> (0 <= x /\ x <= 0).
Proof.
  intros.
  split ; intros H.
  - subst.
    split; reflexivity.
  - destruct H.
    apply Z.le_antisymm; auto.
Qed.

Lemma lt_le_iff x : 0 < x <-> 0 <= x - 1.
Proof. rewrite <-Z.lt_succ_r, Z.sub_1_r, Z.succ_pred; reflexivity. Qed.

Lemma le_0_iff x y : x <= y <-> 0 <= y - x.
Proof. symmetry. apply Z.le_0_sub. Qed.

Lemma le_neg x : ((0 <= x) -> False) <-> 0 < -x.
Proof. setoid_rewrite Z.nle_gt. rewrite Z.opp_pos_neg. reflexivity. Qed.

Lemma eq_cnf x : (0 <= x - 1 -> False) /\ (0 <= -1 - x -> False) <-> x = 0.
Proof.
  rewrite (Z.sub_opp_l 1).
  setoid_rewrite <-lt_le_iff.
  rewrite Z.opp_pos_neg.
  setoid_rewrite Z.nlt_ge.
  split; intros.
  { apply Z.le_antisymm; try apply H. }
  { subst x. split; reflexivity. }
Qed.




Require Import EnvRing.

Lemma Zsor : SOR 0 1 Z.add Z.mul Z.sub Z.opp (@eq Z) Z.le Z.lt.
Proof.
  constructor ; intros ; subst; try reflexivity.
  - apply InitialRing.Zsth.
  - apply InitialRing.Zth.
  - auto using Z.le_antisymm.
  - eauto using Z.le_trans.
  - apply Z.le_neq.
  - apply Z.lt_trichotomy.
  - apply Z.add_le_mono_l; assumption.
  - apply Z.mul_pos_pos ; auto.
  - discriminate.
Qed.

Lemma ZSORaddon :
  SORaddon 0 1 Z.add Z.mul Z.sub Z.opp  (@eq Z) Z.le (* ring elements *)
  0%Z 1%Z Z.add Z.mul Z.sub Z.opp (* coefficients *)
  Z.eqb Z.leb
  (fun x => x) (fun x => x) (pow_N 1 Z.mul).
Proof.
  constructor.
  - constructor ; intros ; try reflexivity.
    apply Z.eqb_eq ; auto.
  - constructor.
    reflexivity.
  - intros x y.
    rewrite <-Z.eqb_eq. congruence.
  - apply Z.leb_le.
Qed.

Fixpoint Zeval_expr (env : PolEnv Z) (e: PExpr Z) : Z :=
  match e with
    | PEc c => c
    | PEX x => env x
    | PEadd e1 e2 => Zeval_expr env e1 + Zeval_expr env e2
    | PEmul e1 e2 => Zeval_expr env e1 * Zeval_expr env e2
    | PEpow e1 n  => Z.pow (Zeval_expr env e1) (Z.of_N n)
    | PEsub e1 e2 => (Zeval_expr env e1) - (Zeval_expr env e2)
    | PEopp e   => Z.opp (Zeval_expr env e)
  end.

Strategy expand [ Zeval_expr ].

Definition eval_expr := eval_pexpr  Z.add Z.mul Z.sub Z.opp (fun x => x) (fun x => x) (pow_N 1 Z.mul).

Fixpoint Zeval_const  (e: PExpr Z) : option Z :=
  match e with
  | PEc c => Some c
  | PEX x => None
  | PEadd e1 e2 => map_option2 (fun x y => Some (x + y))
                               (Zeval_const e1) (Zeval_const e2)
  | PEmul e1 e2 => map_option2 (fun x y => Some (x * y))
                               (Zeval_const e1) (Zeval_const e2)
  | PEpow e1 n  => map_option (fun x => Some (Z.pow x (Z.of_N n)))
                                 (Zeval_const e1)
  | PEsub e1 e2 => map_option2 (fun x y => Some (x - y))
                               (Zeval_const e1)  (Zeval_const e2)
  | PEopp e   => map_option (fun x => Some (Z.opp x)) (Zeval_const e)
  end.

Lemma ZNpower : forall r n, r ^ Z.of_N n = pow_N 1 Z.mul r n.
Proof.
  intros r n; destruct n as [|p].
  - reflexivity.
  - simpl.
    unfold Z.pow_pos.
    rewrite <-Z.mul_1_l.
    generalize 1.
    induction p as [p IHp|p IHp|]; simpl; intros ;
      rewrite ?IHp, ?Z.mul_assoc; auto using Z.mul_comm, f_equal2.
Qed.

Lemma Zeval_expr_compat : forall env e, Zeval_expr env e = eval_expr env e.
Proof.
  intros env e; induction e ; simpl ; try congruence.
  - reflexivity.
  - rewrite ZNpower. congruence.
Qed.

Definition Zeval_pop2 (o : Op2) : Z -> Z -> Prop :=
match o with
| OpEq =>  @eq Z
| OpNEq => fun x y  => ~ x = y
| OpLe => Z.le
| OpGe => Z.ge
| OpLt => Z.lt
| OpGt => Z.gt
end.


Definition Zeval_bop2 (o : Op2) : Z -> Z -> bool :=
match o with
| OpEq =>  Z.eqb
| OpNEq => fun x y => negb (Z.eqb x y)
| OpLe => Z.leb
| OpGe => Z.geb
| OpLt => Z.ltb
| OpGt => Z.gtb
end.

Lemma pop2_bop2 :
  forall (op : Op2) (q1 q2 : Z), is_true (Zeval_bop2 op q1 q2) <-> Zeval_pop2 op q1 q2.
Proof.
  unfold is_true.
  intro op; destruct op ; simpl; intros q1 q2.
  - apply Z.eqb_eq.
  - rewrite <- Z.eqb_eq.
    rewrite negb_true_iff.
    destruct (q1 =? q2) ; intuition congruence.
  - apply Z.leb_le.
  - rewrite Z.geb_le. rewrite Z.ge_le_iff. tauto.
  - apply Z.ltb_lt.
  - rewrite <- Z.gtb_gt; tauto.
Qed.

Definition Zeval_op2 (k: Tauto.kind) :  Op2 ->  Z -> Z -> Tauto.rtyp k:=
  if k as k0 return (Op2 -> Z -> Z -> Tauto.rtyp k0)
  then Zeval_pop2 else Zeval_bop2.


Lemma Zeval_op2_hold : forall k op q1 q2,
    Tauto.hold k (Zeval_op2 k op q1 q2) <-> Zeval_pop2 op q1 q2.
Proof.
  intro k; destruct k.
  - simpl ; tauto.
  - simpl. apply pop2_bop2.
Qed.


Definition Zeval_formula (env : PolEnv Z) (k: Tauto.kind) (f : Formula Z):=
  let (lhs, op, rhs) := f in
    (Zeval_op2 k op) (Zeval_expr env lhs) (Zeval_expr env rhs).

Definition Zeval_formula' :=
  eval_formula  Z.add Z.mul Z.sub Z.opp (@eq Z) Z.le Z.lt (fun x => x) (fun x => x) (pow_N 1 Z.mul).

Lemma Zeval_formula_compat : forall env k f, Tauto.hold k (Zeval_formula env k f) <-> Zeval_formula env Tauto.isProp f.
Proof.
  intros env k; destruct k ; simpl.
  - tauto.
  - intros f; destruct f ; simpl.
    rewrite <- (Zeval_op2_hold Tauto.isBool).
    simpl. tauto.
Qed.

Lemma Zeval_formula_compat' : forall env f,  Zeval_formula env Tauto.isProp f <-> Zeval_formula' env f.
Proof.
  intros env f.
  unfold Zeval_formula.
  destruct f as [Flhs  Fop Frhs].
  repeat rewrite Zeval_expr_compat.
  unfold Zeval_formula' ; simpl.
  unfold eval_expr.
  generalize (eval_pexpr Z.add Z.mul Z.sub Z.opp (fun x : Z => x)
        (fun x : N => x) (pow_N 1 Z.mul) env Flhs).
  generalize ((eval_pexpr Z.add Z.mul Z.sub Z.opp (fun x : Z => x)
        (fun x : N => x) (pow_N 1 Z.mul) env Frhs)).
  destruct Fop ; simpl; intros;
    intuition auto using Z.le_ge, Z.ge_le, Z.lt_gt, Z.gt_lt.
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

Definition ZWeakChecker := check_normalised_formulas 0 1 Z.add Z.mul Z.eqb Z.leb.

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

Definition psub  := psub Z0  Z.add Z.sub Z.opp Z.eqb.
Declare Equivalent Keys psub RingMicromega.psub.

Definition popp  := popp Z.opp.
Declare Equivalent Keys popp RingMicromega.popp.

Definition padd  := padd Z0  Z.add Z.eqb.
Declare Equivalent Keys padd RingMicromega.padd.

Definition pmul := pmul 0 1 Z.add Z.mul Z.eqb.

Definition normZ  := norm 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb.
Declare Equivalent Keys normZ RingMicromega.norm.

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

Lemma eval_pol_mul : forall env lhs rhs, eval_pol env (pmul  lhs rhs) = eval_pol env lhs * eval_pol env rhs.
Proof.
  intros.
  apply (eval_pol_mul Zsor ZSORaddon).
Qed.


Lemma eval_pol_norm : forall env e, eval_expr env e = eval_pol env (normZ e) .
Proof.
  intros.
  apply (eval_pol_norm Zsor ZSORaddon).
Qed.

Definition Zunsat := check_inconsistent 0  Z.eqb Z.leb.

Definition Zdeduce := nformula_plus_nformula 0 Z.add Z.eqb.

Lemma Zunsat_sound : forall f,
    Zunsat f = true -> forall env, eval_nformula env f -> False.
Proof.
  unfold Zunsat.
  intros f H env ?.
  destruct f.
  eapply check_inconsistent_sound with (1 := Zsor) (2 := ZSORaddon) in H; eauto.
Qed.

Definition xnnormalise (t : Formula Z) : NFormula Z :=
  let (lhs,o,rhs) := t in
  let lhs := normZ lhs in
  let rhs := normZ rhs in
  match o with
  | OpEq  => (psub rhs lhs,  Equal)
  | OpNEq => (psub rhs lhs,  NonEqual)
  | OpGt  => (psub lhs rhs,  Strict)
  | OpLt  => (psub rhs lhs,  Strict)
  | OpGe  => (psub lhs rhs,  NonStrict)
  | OpLe =>  (psub rhs lhs,  NonStrict)
  end.

Lemma xnnormalise_correct :
  forall env f,
    eval_nformula env (xnnormalise f) <-> Zeval_formula env Tauto.isProp f.
Proof.
  intros env f.
  rewrite Zeval_formula_compat'.
  unfold xnnormalise.
  destruct f as [lhs o rhs].
  destruct o eqn:O ; cbn ; rewrite ?eval_pol_sub;
    rewrite <- !eval_pol_norm ; simpl in *;
      unfold eval_expr;
      generalize (   eval_pexpr  Z.add Z.mul Z.sub Z.opp (fun x : Z => x)
                                 (fun x : N => x) (pow_N 1 Z.mul) env lhs);
      generalize (eval_pexpr  Z.add Z.mul Z.sub Z.opp (fun x : Z => x)
                              (fun x : N => x) (pow_N 1 Z.mul) env rhs); intros z z0.
  - split ; intros.
    + assert (z0 + (z - z0) = z0 + 0) as H0 by congruence.
      rewrite Z.add_0_r in H0.
      rewrite <- H0.
      rewrite Z.add_sub_assoc, Z.add_comm, <-Z.add_sub_assoc, Z.sub_diag; apply Z.add_0_r.
    + subst.
      apply Z.sub_diag.
  - split ; intros H H0.
    + subst. apply H. apply Z.sub_diag.
    + apply H.
      assert (z0 + (z - z0) = z0 + 0) as H1 by congruence.
      rewrite Z.add_0_r in H1.
      rewrite <- H1.
      rewrite Z.add_sub_assoc, Z.add_comm, <-Z.add_sub_assoc, Z.sub_diag; apply Z.add_0_r.
  - symmetry. apply le_0_iff.
  - symmetry. apply le_0_iff.
  - apply Z.lt_0_sub.
  - apply Z.lt_0_sub.
Qed.

Definition xnormalise (f: NFormula Z) : list (NFormula Z) :=
  let (e,o) := f in
  match o with
  | Equal     => (psub e (Pc 1),NonStrict) :: (psub (Pc (-1)) e, NonStrict) :: nil
  | NonStrict =>  ((psub (Pc (-1)) e,NonStrict)::nil)
  | Strict    =>  ((psub (Pc 0)) e, NonStrict)::nil
  | NonEqual  =>  (e, Equal)::nil
  end.

Lemma eval_pol_Pc : forall env z,
    eval_pol env (Pc z) = z.
Proof.
  reflexivity.
Qed.

Lemma xnormalise_correct : forall env f,
    (make_conj (fun x => eval_nformula env x -> False) (xnormalise f)) <-> eval_nformula env f.
Proof.
  intros env f.
  destruct f as [e o]; destruct o eqn:Op; cbn - [psub];
    repeat rewrite eval_pol_sub; fold eval_pol; repeat rewrite eval_pol_Pc;
      generalize (eval_pol env e) as x; intro.
  - apply eq_cnf.
  - unfold not. tauto.
  - rewrite le_neg. rewrite (Z.sub_0_l x), Z.opp_involutive; reflexivity.
  - rewrite le_neg, lt_le_iff.
    rewrite Z.sub_opp_l, Z.sub_sub_distr. reflexivity.
Qed.



Require Import Stdlib.micromega.Tauto BinNums.

Definition cnf_of_list {T: Type} (tg : T) (l : list (NFormula Z)) :=
  List.fold_right (fun x acc =>
                     if Zunsat x then acc else ((x,tg)::nil)::acc)
                  (cnf_tt _ _)  l.

Lemma cnf_of_list_correct :
  forall {T : Type} (tg:T)  (f : list (NFormula Z)) env,
  eval_cnf eval_nformula env (cnf_of_list tg f) <->
  make_conj (fun x : NFormula Z => eval_nformula env x -> False) f.
Proof.
  unfold cnf_of_list.
  intros T tg f env.
  set (F := (fun (x : NFormula Z) (acc : list (list (NFormula Z * T))) =>
        if Zunsat x then acc else ((x, tg) :: nil) :: acc)).
  set (E := ((fun x : NFormula Z => eval_nformula env x -> False))).
  induction f as [|a f IHf].
  - compute.
    tauto.
  - rewrite make_conj_cons.
    simpl.
    unfold F at 1.
    destruct (Zunsat a) eqn:EQ.
    + rewrite IHf.
      unfold E at 1.
      specialize (Zunsat_sound _ EQ env).
      tauto.
    +
      rewrite <- eval_cnf_cons_iff.
      rewrite IHf.
      simpl.
      unfold E at 2.
      unfold eval_tt. simpl.
      tauto.
Qed.

Definition normalise {T : Type} (t:Formula Z) (tg:T) : cnf (NFormula Z) T :=
  let f := xnnormalise t in
  if Zunsat f then cnf_ff _ _
  else cnf_of_list tg (xnormalise f).

Lemma normalise_correct : forall (T: Type) env t (tg:T), eval_cnf eval_nformula env (normalise t tg) <-> Zeval_formula env Tauto.isProp t.
Proof.
  intros T env t tg.
  rewrite <- xnnormalise_correct.
  unfold normalise.
  generalize (xnnormalise t) as f;intro f.
  destruct (Zunsat f) eqn:U.
  - assert (US := Zunsat_sound _  U env).
    rewrite eval_cnf_ff.
    tauto.
  - rewrite cnf_of_list_correct.
    apply xnormalise_correct.
Qed.


Definition xnegate (f:NFormula Z) : list (NFormula Z)  :=
  let (e,o) := f in
    match o with
      | Equal  => (e,Equal) :: nil
      | NonEqual => (psub e (Pc 1),NonStrict) :: (psub (Pc (-1)) e, NonStrict) :: nil
      | NonStrict => (e,NonStrict)::nil
      | Strict    => (psub e (Pc 1),NonStrict)::nil
    end.

Definition negate {T : Type} (t:Formula Z) (tg:T) : cnf (NFormula Z) T :=
  let f := xnnormalise t in
  if Zunsat f then cnf_tt _ _
  else cnf_of_list tg (xnegate f).

Lemma xnegate_correct : forall env f,
    (make_conj (fun x => eval_nformula env x -> False) (xnegate f)) <-> ~ eval_nformula env f.
Proof.
  intros env f.
  destruct f as [e o]; destruct o eqn:Op; cbn - [psub];
    repeat rewrite eval_pol_sub; fold eval_pol; repeat rewrite eval_pol_Pc;
      generalize (eval_pol env e) as x; intro x.
  - tauto.
  - rewrite eq_cnf.
    destruct (Z.eq_decidable x 0);tauto.
  - rewrite lt_le_iff.
    tauto.
  - tauto.
Qed.

Lemma negate_correct : forall T env t (tg:T), eval_cnf eval_nformula env (negate t tg) <-> ~ Zeval_formula env Tauto.isProp t.
Proof.
  intros T env t tg.
  rewrite <- xnnormalise_correct.
  unfold negate.
  generalize (xnnormalise t) as f;intro f.
  destruct (Zunsat f) eqn:U.
  - assert (US := Zunsat_sound _  U env).
    rewrite eval_cnf_tt.
    tauto.
  - rewrite cnf_of_list_correct.
    apply xnegate_correct.
Qed.

Definition cnfZ (Annot: Type) (TX : Tauto.kind -> Type)  (AF : Type) (k: Tauto.kind) (f : TFormula (Formula Z) Annot TX AF k) :=
  rxcnf Zunsat Zdeduce normalise negate true f.

Definition ZweakTautoChecker (w: list ZWitness) (f : BFormula (Formula Z) Tauto.isProp) : bool :=
  @tauto_checker (Formula Z)  (NFormula Z) unit Zunsat Zdeduce normalise negate  ZWitness (fun cl => ZWeakChecker (List.map fst cl)) f w.

(* To get a complete checker, the proof format has to be enriched *)

Require Import Zdiv.
Local Open Scope Z_scope.

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
  intros a b H.
  apply Zdivide_mod in H.
  case_eq (Z.div_eucl a b).
  intros z z0 H0.
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
    apply Z.mul_lt_mono_pos_l with a.
    + auto using Z.gt_lt.
    + eapply Z.lt_le_trans. 2: eassumption.
      now apply Z.lt_add_pos_r.
  - now elim H1.
Qed.

(** NB: narrow_interval_upper_bound is Zdiv.Zdiv_le_lower_bound *)

Require Import QArith.

Inductive ZArithProof :=
| DoneProof
| RatProof : ZWitness -> ZArithProof -> ZArithProof
| CutProof : ZWitness -> ZArithProof -> ZArithProof
| SplitProof : PolC Z -> ZArithProof -> ZArithProof -> ZArithProof
| EnumProof : ZWitness -> ZWitness -> list ZArithProof -> ZArithProof
| ExProof   : positive -> ZArithProof -> ZArithProof
(*ExProof x : exists z t, x = z - t /\ z >= 0 /\ t >= 0 *)
.


Register ZArithProof as micromega.ZArithProof.type.
Register DoneProof   as micromega.ZArithProof.DoneProof.
Register RatProof    as micromega.ZArithProof.RatProof.
Register CutProof    as micromega.ZArithProof.CutProof.
Register SplitProof  as micromega.ZArithProof.SplitProof.
Register EnumProof   as micromega.ZArithProof.EnumProof.
Register ExProof     as micromega.ZArithProof.ExProof.



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
  intros x; destruct x ; simpl ; intuition congruence.
Qed.

Lemma isZ0_n0 : forall x, isZ0 x = false <-> x <> 0.
Proof.
  intros x; destruct x ; simpl ; intuition congruence.
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
  intros a p H H0.
  induction H0 as [? ?|? ? IHZdivide_pol j|? ? ? IHZdivide_pol1 ? IHZdivide_pol2 j].
  - (* Pc *)
    simpl.
    intros.
    apply Zdivide_Zdiv_eq ; auto.
  - (* Pinj *)
    simpl.
    intros.
    apply IHZdivide_pol.
  - (* PX *)
    simpl.
    intros.
    rewrite IHZdivide_pol1.
    rewrite IHZdivide_pol2.
    ring.
Qed.

Lemma Zgcd_pol_ge : forall p, fst (Zgcd_pol p) >= 0.
Proof.
  intros p; induction p as [c|p p1 IHp1|p1 IHp1 ? p3 IHp3]. 1-2: easy.
  simpl.
  case_eq (Zgcd_pol p1).
  case_eq (Zgcd_pol p3).
  intros.
  simpl.
  unfold ZgcdM.
  apply Z.le_ge; transitivity 1.
  - easy.
  - apply Z.le_max_r.
Qed.

Lemma Zdivide_pol_Zdivide : forall p x y, Zdivide_pol x p -> (y | x) ->  Zdivide_pol y p.
Proof.
  intros p x y H H0.
  induction H.
  - constructor.
    apply Z.divide_trans with (1:= H0) ; assumption.
  - constructor. auto.
  - constructor ; auto.
Qed.

Lemma Zdivide_pol_one : forall p, Zdivide_pol 1 p.
Proof.
  intros p; induction p as [c| |]; constructor ; auto.
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
  intros p; induction p as [c|? p IHp|p ? ? ? IHp2].
  - simpl.
    intros a b H H0. inversion H0.
    constructor.
    apply Zgcd_minus ; auto.
  - intros ? ? H H0.
    constructor.
    simpl in H0. inversion H0 ; subst; clear H0.
    apply IHp ; auto.
  - simpl. intros a b H H0.
    inv H0.
    constructor.
    + apply Zdivide_pol_Zdivide with (1:= (ltac:(assumption) : Zdivide_pol a p)).
      destruct (Zgcd_is_gcd a b) ; assumption.
    + apply IHp2 ; assumption.
Qed.

Lemma Zdivide_pol_sub_0 : forall p a,
  Zdivide_pol a (PsubC Z.sub p 0) ->
   Zdivide_pol a p.
Proof.
  intros p; induction p as [c|? p IHp|? IHp1 ? ? IHp2].
  - simpl.
    intros ? H. inversion H.
    constructor. rewrite Z.sub_0_r in *. assumption.
  - intros ? H.
    constructor.
    simpl in H. inversion H ; subst; clear H.
    apply IHp ; auto.
  - simpl. intros ? H.
    inv H.
    constructor.
    + auto.
    + apply IHp2 ; assumption.
Qed.


Lemma Zgcd_pol_div : forall p g c,
  Zgcd_pol p = (g, c) -> Zdivide_pol g (PsubC Z.sub p c).
Proof.
  intros p; induction p as [c|? ? IHp|p1 IHp1 ? p3 IHp2]; simpl.
  - (* Pc *)
    intros ? ? H. inv H.
    constructor.
    exists 0. now ring.
  - (* Pinj *)
    intros.
    constructor.  apply IHp ; auto.
  - (* PX *)
    intros g c.
    case_eq (Zgcd_pol p1) ; case_eq (Zgcd_pol p3) ; intros z z0 H z1 z2 H0 H1.
    inv H1.
    unfold ZgcdM at 1.
    destruct (Z.max_spec (Z.gcd (ZgcdM z1 z2) z) 1) as [HH1 | HH1]; cycle 1;
      destruct HH1 as [HH1 HH1'] ; rewrite HH1'.
    + constructor.
      * apply (Zdivide_pol_Zdivide _ (ZgcdM z1 z2)).
        -- unfold ZgcdM.
           destruct (Z.max_spec  (Z.gcd z1 z2)  1) as [HH2 | HH2]; cycle 1.
           ++ destruct HH2 as [H1 H2].
              rewrite H2.
              apply Zdivide_pol_sub ; auto.
              apply Z.lt_le_trans with 1.
              ** reflexivity.
              ** trivial.
           ++ destruct HH2 as [H1 H2]. rewrite H2.
              apply Zdivide_pol_one.
        -- unfold ZgcdM in HH1. unfold ZgcdM.
           destruct (Z.max_spec  (Z.gcd z1 z2)  1) as [HH2 | HH2]; cycle 1.
           ++ destruct HH2 as [H1 H2]. rewrite H2 in *.
              destruct (Zgcd_is_gcd (Z.gcd z1 z2) z); auto.
           ++ destruct HH2 as [H1 H2]. rewrite H2.
              destruct (Zgcd_is_gcd 1  z); auto.
      * apply (Zdivide_pol_Zdivide _ z).
        -- apply (IHp2 _ _ H); auto.
        -- destruct (Zgcd_is_gcd (ZgcdM z1 z2) z); auto.
    + constructor.
      * apply Zdivide_pol_one.
      * apply Zdivide_pol_one.
Qed.




Lemma Zgcd_pol_correct_lt : forall p env g c, Zgcd_pol p = (g,c) -> 0 < g -> eval_pol env p = g * (eval_pol env (Zdiv_pol (PsubC Z.sub p c) g))  + c.
Proof.
  intros.
  rewrite <- Zdiv_pol_correct ; auto.
  - rewrite (RingMicromega.PsubC_ok Zsor ZSORaddon).
    unfold eval_pol. ring.
    (**)
  - apply Zgcd_pol_div ; auto.
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
        if andb (Z.gtb g Z0) (andb (negb (Z.eqb c Z0)) (negb (Z.eqb (Z.gcd g c) g)))
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
  intros p; destruct p as [z| |]; try discriminate.
  destruct z ; try discriminate.
  reflexivity.
Qed.


Definition eval_Psatz  : list (NFormula Z) -> ZWitness ->  option (NFormula Z) :=
  eval_Psatz 0 1 Z.add Z.mul Z.eqb Z.leb.


Definition valid_cut_sign (op:Op1) :=
  match op with
    | Equal => true
    | NonStrict => true
    | _         => false
  end.


Definition bound_var (v : positive) : Formula Z :=
  Build_Formula (PEX v) OpGe (PEc 0).

Definition mk_eq_pos (x : positive) (y:positive) (t : positive) : Formula Z :=
  Build_Formula (PEX x) OpEq (PEsub (PEX y) (PEX t)).


Fixpoint vars (jmp : positive) (p : Pol Z) : list positive :=
  match p with
  | Pc c => nil
  | Pinj j p => vars (Pos.add j jmp) p
  | PX p j q => jmp::(vars jmp p)++vars (Pos.succ jmp) q
  end.

Fixpoint max_var (jmp : positive) (p : Pol Z) : positive :=
  match p with
  | Pc _ => jmp
  | Pinj j p => max_var (Pos.add j jmp) p
  | PX p j q => Pos.max (max_var jmp p) (max_var (Pos.succ jmp) q)
  end.

Lemma pos_le_add : forall y x,
    (x <= y + x)%positive.
Proof.
  intros y x.
  assert  ((Z.pos x) <= Z.pos (x + y))%Z as H.
  - rewrite <- (Z.add_0_r (Zpos x)).
    rewrite <- Pos2Z.add_pos_pos.
    apply Z.add_le_mono_l.
    compute. congruence.
  - rewrite Pos.add_comm in H.
    apply H.
Qed.


Lemma max_var_le : forall p v,
    (v <= max_var v p)%positive.
Proof.
  intros p; induction p as [?|p ? IHp|? IHp1 ? ? IHp2]; simpl.
  - intros.
    apply Pos.le_refl.
  - intros v.
    specialize (IHp (p+v)%positive).
    eapply Pos.le_trans ; eauto.
    assert (xH + v <= p + v)%positive.
    { apply Pos.add_le_mono.
      - apply Pos.le_1_l.
      - apply Pos.le_refl.
    }
    eapply Pos.le_trans ; eauto.
    apply pos_le_add.
  - intros v.
    apply Pos.max_case_strong;intros ; auto.
    specialize (IHp2 (Pos.succ v)%positive).
    eapply Pos.le_trans ; eauto.
Qed.

Lemma max_var_correct : forall p j v,
    In v (vars j p) -> Pos.le v (max_var j p).
Proof.
  intros p; induction p; simpl.
  - tauto.
  - auto.
  - intros j v H.
    rewrite in_app_iff in H.
    destruct H as [H |[ H | H]].
    + subst.
      apply Pos.max_case_strong;intros ; auto.
      * apply max_var_le.
      * eapply Pos.le_trans ; eauto.
        apply max_var_le.
    + apply Pos.max_case_strong;intros ; auto.
      eapply Pos.le_trans ; eauto.
    + apply Pos.max_case_strong;intros ; auto.
      eapply Pos.le_trans ; eauto.
Qed.

Definition max_var_nformulae (l : list (NFormula Z)) :=
  List.fold_left  (fun acc f => Pos.max acc (max_var xH (fst f))) l xH.

Section MaxVar.

  Definition F (acc : positive) (f : Pol Z * Op1) := Pos.max acc (max_var 1 (fst f)).

  Lemma max_var_nformulae_mono_aux :
    forall l v acc,
      (v <= acc ->
       v <= fold_left F l acc)%positive.
  Proof.
    intros l; induction l as [|a l IHl] ; simpl ; [easy|].
    intros.
    apply IHl.
    unfold F.
    apply Pos.max_case_strong;intros ; auto.
    eapply Pos.le_trans ; eauto.
  Qed.

  Lemma max_var_nformulae_mono_aux' :
    forall l acc acc',
      (acc <= acc' ->
       fold_left F l acc <= fold_left F l acc')%positive.
  Proof.
    intros l; induction l as [|a l IHl]; simpl ; [easy|].
    intros.
    apply IHl.
    unfold F.
    apply Pos.max_le_compat_r; auto.
  Qed.




  Lemma max_var_nformulae_correct_aux : forall l p o v,
      In (p,o) l -> In v (vars xH p) -> Pos.le v (fold_left F l 1)%positive.
  Proof.
  intros l p o v H H0.
  generalize 1%positive as acc.
  revert p o v H H0.
  induction l as [|a l IHl].
  - simpl. tauto.
  - simpl.
    intros p o v H H0 ?.
    destruct H ; subst.
    + unfold F at 2.
      simpl.
      apply max_var_correct in H0.
      apply max_var_nformulae_mono_aux.
      apply Pos.max_case_strong;intros ; auto.
      eapply Pos.le_trans ; eauto.
    + eapply IHl ; eauto.
  Qed.

End MaxVar.

Lemma max_var_nformalae_correct : forall l p o v,
      In (p,o) l -> In v (vars xH p) -> Pos.le v (max_var_nformulae l)%positive.
Proof.
  intros l p o v.
  apply max_var_nformulae_correct_aux.
Qed.


Fixpoint max_var_psatz (w : Psatz Z) : positive :=
  match w with
  | PsatzIn _ n => xH
  | PsatzSquare p => max_var xH (Psquare 0 1 Z.add Z.mul Z.eqb p)
  | PsatzMulC p w => Pos.max (max_var xH p) (max_var_psatz w)
  | PsatzMulE w1 w2 => Pos.max (max_var_psatz w1) (max_var_psatz w2)
  | PsatzAdd w1 w2  => Pos.max (max_var_psatz w1) (max_var_psatz w2)
  | _   => xH
  end.

Fixpoint max_var_prf (w : ZArithProof) : positive :=
  match w with
  | DoneProof => xH
  | RatProof w pf | CutProof w pf => Pos.max (max_var_psatz w) (max_var_prf pf)
  | SplitProof p pf1 pf2 => Pos.max (max_var xH p) (Pos.max (max_var_prf pf1) (max_var_prf pf1))
  | EnumProof w1 w2 l => List.fold_left
                           (fun acc prf => Pos.max acc (max_var_prf prf)) l
                           (Pos.max (max_var_psatz w1) (max_var_psatz w2))
  | ExProof _ pf => max_var_prf pf
  end.


Fixpoint ZChecker  (l:list (NFormula Z)) (pf : ZArithProof)  {struct pf} : bool :=
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
    | SplitProof p pf1 pf2 =>
      match genCuttingPlane (p,NonStrict) , genCuttingPlane (popp p, NonStrict) with
      | None , _ | _ , None => false
      | Some cp1 , Some cp2 =>
        ZChecker (nformula_of_cutting_plane cp1::l) pf1
        &&
        ZChecker (nformula_of_cutting_plane cp2::l) pf2
      end
    | ExProof x prf =>
      let fr := max_var_nformulae l in
      if Pos.leb x fr then
      let z    := Pos.succ fr in
      let t    := Pos.succ z in
      let nfx  := xnnormalise (mk_eq_pos x z t) in
      let posz := xnnormalise (bound_var z) in
      let post := xnnormalise (bound_var t) in
      ZChecker (nfx::posz::post::l) prf
      else false
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
                       | pf::rsr => andb (ZChecker ((psub e1 (Pc lb), Equal) :: l) pf) (label rsr (Z.add lb 1%Z) ub)
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
    | SplitProof _ p1 p2 => S (Nat.max (bdepth p1) (bdepth p2))
    | EnumProof _ _ l => S (List.fold_right (fun pf x => Nat.max (bdepth pf) x)   O l)
    | ExProof _ p   => S (bdepth p)
  end.

Require Import PeanoNat Wf_nat.

Lemma in_bdepth : forall l a b  y, In y l ->  ltof ZArithProof bdepth y (EnumProof a b  l).
Proof.
  intros l; induction l as [|a l IHl].
  - (* nil *)
    simpl.
    tauto.
  - (* cons *)
    simpl.
    intros a0 b y H.
    destruct H as [H|H].
    + subst.
      unfold ltof.
      simpl.
      generalize (         (fold_right
                              (fun (pf : ZArithProof) (x : nat) => Nat.max (bdepth pf) x) 0%nat l)).
      intros.
      generalize (bdepth y) ; intros.
      rewrite Nat.lt_succ_r. apply Nat.le_max_l.
    + generalize (IHl a0 b  y  H).
      unfold ltof.
      simpl.
      generalize (      (fold_right (fun (pf : ZArithProof) (x : nat) => Nat.max (bdepth pf) x) 0%nat
                                    l)).
      intros.
      eapply Nat.lt_le_trans.
      * eassumption.
      * rewrite <- Nat.succ_le_mono.
        apply Nat.le_max_r.
Qed.

Lemma ltof_bdepth_split_l :
  forall p pf1 pf2,
         ltof ZArithProof bdepth pf1 (SplitProof p pf1 pf2).
Proof.
  intros.
  unfold ltof. simpl.
  rewrite Nat.lt_succ_r.
  apply Nat.le_max_l.
Qed.

Lemma ltof_bdepth_split_r :
  forall p pf1 pf2,
         ltof ZArithProof bdepth pf2 (SplitProof p pf1 pf2).
Proof.
  intros.
  unfold ltof. simpl.
  rewrite Nat.lt_succ_r.
  apply Nat.le_max_r.
Qed.


Lemma eval_Psatz_sound : forall env w l f',
  make_conj (eval_nformula env) l ->
  eval_Psatz l w  = Some f' ->  eval_nformula env f'.
Proof.
  intros env w l f' H H0.
  apply (fun H => eval_Psatz_Sound Zsor ZSORaddon l _ H w) ; auto.
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
  intros env e e' c H H0.
  rewrite (RingMicromega.eval_pol_add Zsor ZSORaddon).
  simpl.
  (**)
  unfold makeCuttingPlane in H0.
  revert H0.
  case_eq (Zgcd_pol e) ; intros g c0.
  case Z.gtb_spec.
  - intros H0 H1 H2.
    inv H2.
    change (RingMicromega.eval_pol Z.add Z.mul (fun x : Z => x)) with eval_pol in *.
    apply (Zgcd_pol_correct_lt _ env) in H1. 2: auto using Z.gt_lt.
    apply Z.le_add_le_sub_l, Z.ge_le; rewrite Z.add_0_r.
    apply (narrow_interval_lower_bound g (- c0) (eval_pol env (Zdiv_pol (PsubC Z.sub e c0) g))); auto using Z.lt_gt.
    apply Z.le_ge.
    rewrite <- Z.sub_0_l.
    apply Z.le_sub_le_add_r.
    rewrite <- H1.
    assumption.
    (* g <= 0 *)
  - intros H0 H1 H2. inv H2. auto with zarith.
Qed.

Lemma cutting_plane_sound : forall env f p,
  eval_nformula env f ->
  genCuttingPlane f = Some p ->
   eval_nformula env (nformula_of_cutting_plane p).
Proof.
  unfold genCuttingPlane.
  intros env f; destruct f as [e op].
  destruct op.
  - (* Equal *)
    intros p; destruct p as [[e' z] op].
    case_eq (Zgcd_pol e) ; intros g c.
    case_eq (Z.gtb g 0 && (negb (Z.eqb c 0) && negb (Z.eqb (Z.gcd g c) g))) ; [discriminate|].
    case_eq (makeCuttingPlane e).
    intros ? ? H H0 H1 H2 H3.
    inv H3.
    unfold makeCuttingPlane in H.
    rewrite H1 in H.
    revert H.
    change (eval_pol env e = 0) in H2.
    case_eq (Z.gtb g 0).
    + intros H H3.
      rewrite Z.gtb_lt in H.
      rewrite Zgcd_pol_correct_lt with (1:= H1)  in H2. 2: auto using Z.gt_lt.
      unfold nformula_of_cutting_plane.
      change (eval_pol env (padd e' (Pc z)) = 0).
      inv H3.
      rewrite eval_pol_add.
      set (x:=eval_pol env (Zdiv_pol (PsubC Z.sub e c) g)) in *; clearbody x.
      simpl.
      rewrite andb_false_iff in H0.
      destruct H0 as [H0|H0].
      * rewrite <-Z.gtb_lt in H ; congruence.
      * rewrite andb_false_iff in H0.
        destruct H0 as [H0|H0].
        -- rewrite negb_false_iff in H0.
           apply Z.eqb_eq in H0.
           subst. simpl.
           rewrite Z.add_0_r, Z.mul_eq_0 in H2.
           intuition subst; easy.
        -- rewrite negb_false_iff in H0.
           apply Z.eqb_eq in H0.
           rewrite Zdivide_ceiling; cycle 1.
           { apply Z.divide_opp_r. rewrite <-H0. apply Z.gcd_divide_r. }
           apply Z.sub_move_0_r.
           apply Z.div_unique_exact.
           ++ now intros ->.
           ++ now rewrite Z.add_move_0_r in H2.
    + intros H H3.
      unfold nformula_of_cutting_plane.
      inv H3.
      change (eval_pol env (padd e' (Pc 0)) = 0).
      rewrite eval_pol_add.
      simpl.
      now rewrite Z.add_0_r.
  - (* NonEqual *)
    intros ? H H0.
    inv H0.
    unfold eval_nformula in *.
    unfold RingMicromega.eval_nformula in *.
    unfold nformula_of_cutting_plane.
    unfold eval_op1 in *.
    rewrite (RingMicromega.eval_pol_add Zsor ZSORaddon).
    simpl. now rewrite Z.add_0_r.
  - (* Strict *)
    intros p; destruct p as [[e' z] op].
    case_eq (makeCuttingPlane (PsubC Z.sub e 1)).
    intros ? ? H H0 H1.
    inv H1.
    apply (makeCuttingPlane_ns_sound env) with (2:= H).
    simpl in *.
    rewrite (RingMicromega.PsubC_ok Zsor ZSORaddon).
    now apply Z.lt_le_pred.
  - (* NonStrict *)
    intros p; destruct p as [[e' z] op].
    case_eq (makeCuttingPlane e).
    intros ? ? H H0 H1.
    inv H1.
    apply (makeCuttingPlane_ns_sound env) with (2:= H).
    assumption.
Qed.

Lemma  genCuttingPlaneNone : forall env f,
  genCuttingPlane f = None ->
  eval_nformula env f -> False.
Proof.
  unfold genCuttingPlane.
  intros env f; destruct f as [p o].
  destruct o.
  - case_eq (Zgcd_pol p) ; intros g c.
    case_eq (Z.gtb g 0 && (negb (Z.eqb c 0) && negb (Z.eqb (Z.gcd g c) g))).
    + intros H H0 H1 H2.
      flatten_bool.
      match goal with [ H' : (g >? 0) = true |- ?G ] => rename H' into H3 end.
      match goal with [ H' : negb (Z.eqb c 0) = true |- ?G ] => rename H' into H end.
      match goal with [ H' : negb (Z.eqb (Z.gcd g c) g) = true |- ?G ] => rename H' into H5 end.
      rewrite negb_true_iff in H5.
      apply Z.eqb_neq in H5.
      rewrite Z.gtb_lt in H3.
      rewrite negb_true_iff in H.
      apply Z.eqb_neq in H.
      change (eval_pol env p = 0) in H2.
      rewrite Zgcd_pol_correct_lt with (1:= H0) in H2. 2: auto using Z.gt_lt.
      set (x:=eval_pol env (Zdiv_pol (PsubC Z.sub p c) g)) in *; clearbody x.
      contradict H5.
      apply Zis_gcd_gcd.
      * apply Z.lt_le_incl; assumption.
      * constructor; auto with zarith.
        exists (-x).
        rewrite Z.mul_opp_l, Z.mul_comm.
        now apply Z.add_move_0_l.
        (**)
    + destruct (makeCuttingPlane p);  discriminate.
  - discriminate.
  - destruct (makeCuttingPlane (PsubC Z.sub p 1)) ; discriminate.
  - destruct (makeCuttingPlane p) ; discriminate.
Qed.

Lemma eval_nformula_mk_eq_pos : forall env x z t,
    env x = env z - env t ->
    eval_nformula env (xnnormalise (mk_eq_pos x z t)).
Proof.
  intros.
  rewrite xnnormalise_correct.
  simpl. auto.
Qed.

Lemma eval_nformula_bound_var : forall env x,
    env x >= 0 ->
    eval_nformula env (xnnormalise (bound_var x)).
Proof.
  intros.
  rewrite xnnormalise_correct.
  simpl. auto.
Qed.


Definition agree_env (fr : positive) (env env' : positive -> Z) : Prop :=
  forall x, Pos.le x fr -> env x = env' x.

Lemma agree_env_subset : forall v1 v2 env env',
    agree_env v1 env env' ->
    Pos.le v2 v1 ->
    agree_env v2 env env'.
Proof.
  unfold agree_env.
  intros v1 v2 env env' H ? ? ?.
  apply H.
  eapply Pos.le_trans ; eauto.
Qed.


Lemma agree_env_jump : forall fr j env env',
    agree_env (fr + j) env env' ->
    agree_env fr (Env.jump j env) (Env.jump j env').
Proof.
  intros fr j env env' H.
  unfold agree_env ; intro.
  intros.
  unfold Env.jump.
  apply H.
  apply Pos.add_le_mono_r; auto.
Qed.


Lemma agree_env_tail : forall fr env env',
    agree_env (Pos.succ fr) env env' ->
    agree_env fr (Env.tail env) (Env.tail env').
Proof.
  intros fr env env' H.
  unfold Env.tail.
  apply agree_env_jump.
  rewrite <- Pos.add_1_r in H.
  apply H.
Qed.


Lemma max_var_acc : forall p i j,
    (max_var (i + j) p = max_var i p + j)%positive.
Proof.
  intros p; induction p as [|? ? IHp|? IHp1 ? ? IHp2]; simpl.
  - reflexivity.
  - intros.
    rewrite ! IHp.
    rewrite Pos.add_assoc.
    reflexivity.
  - intros.
    rewrite !Pplus_one_succ_l.
    rewrite ! IHp1.
    rewrite ! IHp2.
    rewrite ! Pos.add_assoc.
    rewrite <- Pos.add_max_distr_r.
    reflexivity.
Qed.



Lemma agree_env_eval_nformula :
  forall env env' e
         (AGREE : agree_env (max_var xH (fst e))  env env'),
    eval_nformula env e  <->  eval_nformula env' e.
Proof.
  intros env env' e; destruct e as [p o].
  simpl; intros AGREE.
  assert ((RingMicromega.eval_pol Z.add Z.mul (fun x : Z => x) env p)
          =
          (RingMicromega.eval_pol Z.add Z.mul (fun x : Z => x) env' p)) as H.
  {
    revert env env' AGREE.
    generalize xH.
    induction p as [?|p ? IHp|? IHp1 ? ? IHp2]; simpl.
    - reflexivity.
    - intros p1 **.
      apply (IHp p1).
      apply agree_env_jump.
      eapply agree_env_subset; eauto.
      rewrite (Pos.add_comm p).
      rewrite max_var_acc.
      apply Pos.le_refl.
      - intros p ? ? AGREE.
        f_equal;[f_equal|].
        + apply (IHp1 p).
          eapply agree_env_subset; eauto.
          apply Pos.le_max_l.

        + f_equal.
          unfold Env.hd.
          unfold Env.nth.
          apply AGREE.
          apply Pos.le_1_l.


        + apply (IHp2 p).
          apply agree_env_tail.
          eapply agree_env_subset; eauto.
          rewrite !Pplus_one_succ_r.
          rewrite max_var_acc.
          apply Pos.le_max_r.
  }

  rewrite H. tauto.
Qed.

Lemma agree_env_eval_nformulae :
  forall env env' l
         (AGREE : agree_env (max_var_nformulae l) env env'),
         make_conj (eval_nformula env) l <->
         make_conj (eval_nformula env') l.
Proof.
  intros env env' l; induction l as [|a l IHl].
  - simpl. tauto.
  - intros.
    rewrite ! make_conj_cons.
    assert (eval_nformula env a <-> eval_nformula env' a) as H.
    {
      apply agree_env_eval_nformula.
      eapply agree_env_subset ; eauto.
      unfold max_var_nformulae.
      simpl.
      rewrite Pos.max_1_l.
      apply max_var_nformulae_mono_aux.
      apply Pos.le_refl.
    }
    rewrite H.
    apply  and_iff_compat_l.
    apply IHl.
    eapply agree_env_subset ; eauto.
    unfold max_var_nformulae.
    simpl.
    apply max_var_nformulae_mono_aux'.
    apply Pos.le_1_l.
Qed.


Lemma eq_true_iff_eq :
  forall b1 b2 : bool, (b1 = true <-> b2 = true) <-> b1 = b2.
Proof.
  intros b1 b2; destruct b1,b2 ; intuition congruence.
Qed.

Lemma eval_nformula_split : forall env p,
    eval_nformula env (p,NonStrict) \/ eval_nformula env (popp p,NonStrict).
Proof.
  unfold popp.
  simpl. intros. rewrite (eval_pol_opp Zsor ZSORaddon).
  rewrite Z.opp_nonneg_nonpos.
  apply Z.le_ge_cases.
Qed.




Lemma ZChecker_sound : forall w l,
    ZChecker l w = true -> forall env, make_impl  (eval_nformula env)  l False.
Proof.
  intros w; induction w as [w H] using (well_founded_ind (well_founded_ltof _ bdepth)).
  destruct w as [ | w pf | w pf | p pf1 pf2 | w1 w2 pf | x pf].
  - (* DoneProof *)
  simpl. discriminate.
  - (* RatProof *)
  simpl.
  intros l. case_eq (eval_Psatz l w) ; [| discriminate].
  intros f Hf.
  case_eq (Zunsat f).
  + intros H0 ? ?.
  apply (checker_nf_sound Zsor ZSORaddon l w).
  unfold check_normalised_formulas.  unfold eval_Psatz in Hf. rewrite Hf.
  unfold Zunsat in H0. assumption.
  + intros H0 H1 env.
    assert (make_impl  (eval_nformula env) (f::l) False) as H2.
    { apply H with (2:= H1).
      unfold ltof.
      simpl.
      auto with arith.
    }
    destruct f.
    rewrite <- make_conj_impl in H2.
    rewrite make_conj_cons in H2.
    rewrite <- make_conj_impl.
    intro.
    apply H2.
    split ; auto.
    apply eval_Psatz_sound with (2:= Hf) ; assumption.
  - (* CutProof *)
    simpl.
    intros l.
    case_eq (eval_Psatz l w) ; [ | discriminate].
    intros f' Hlc.
    case_eq (genCuttingPlane f').
    + intros p H0 H1 env.
      assert (make_impl (eval_nformula env) (nformula_of_cutting_plane p::l) False) as H2.
      { eapply (H pf)  ; auto.
        unfold ltof.
        simpl.
        auto with arith.
      }
      rewrite <- make_conj_impl in H2.
      rewrite make_conj_cons in H2.
      rewrite <- make_conj_impl.
      intro.
      apply H2.
      split ; auto.
      apply (eval_Psatz_sound env) in Hlc.
      * apply cutting_plane_sound with (1:= Hlc) (2:= H0).
      * auto.
    + (* genCuttingPlane = None *)
      intros H0 H1 env.
      rewrite <- make_conj_impl.
      intros H2.
      apply eval_Psatz_sound with (2:= Hlc) in H2.
      apply genCuttingPlaneNone with (2:= H2) ; auto.
  - (* SplitProof *)
    intros l.
    cbn - [genCuttingPlane].
    case_eq (genCuttingPlane (p, NonStrict)) ; [| discriminate].
    case_eq (genCuttingPlane (popp p, NonStrict)) ; [| discriminate].
    intros cp1 GCP1 cp2 GCP2 ZC1 env.
    flatten_bool.
    match goal with [ H' : ZChecker _ pf1 = true |- _ ] => rename H' into H0 end.
    match goal with [ H' : ZChecker _ pf2 = true |- _ ] => rename H' into H1 end.
    destruct (eval_nformula_split env p).
    + apply (fun H' ck => H _ H' _ ck env) in H0.
      * rewrite <- make_conj_impl in *.
        intro ; apply H0.
        rewrite make_conj_cons. split; auto.
        apply (cutting_plane_sound _ (p,NonStrict)) ; auto.
      * apply ltof_bdepth_split_l.
    + apply (fun H' ck => H _ H' _ ck env) in H1.
      * rewrite <- make_conj_impl in *.
        intro ; apply H1.
        rewrite make_conj_cons. split; auto.
        apply (cutting_plane_sound _ (popp p,NonStrict)) ; auto.
      * apply ltof_bdepth_split_r.
  - (* EnumProof *)
    intros l.
    simpl.
    case_eq (eval_Psatz l w1) ; [  | discriminate].
    case_eq (eval_Psatz l w2) ; [  | discriminate].
    intros f1 Hf1 f2 Hf2.
    case_eq (genCuttingPlane f2).
    + intros p; destruct p as [ [p1 z1] op1].
      case_eq (genCuttingPlane f1).
      * intros p; destruct p as [ [p2 z2] op2].
        case_eq (valid_cut_sign op1 && valid_cut_sign op2 && is_pol_Z0 (padd p1 p2)).
        -- intros Hcond.
           flatten_bool.
           match goal with [ H1 : is_pol_Z0 (padd p1 p2) = true |- _ ] => rename H1 into HZ0 end.
           match goal with [ H2 : valid_cut_sign op1 = true |- _ ] => rename H2 into Hop1 end.
           match goal with [ H3 : valid_cut_sign op2 = true |- _ ] => rename H3 into Hop2 end.
           intros HCutL HCutR Hfix env.
           (* get the bounds of the enum *)
           rewrite <- make_conj_impl.
           intro H0.
           assert (-z1 <= eval_pol env p1 <= z2) as H1. {
             split.
             - apply  (eval_Psatz_sound env) in Hf2 ; auto.
               apply cutting_plane_sound with (1:= Hf2) in HCutR.
               unfold nformula_of_cutting_plane in HCutR.
               unfold eval_nformula in HCutR.
               unfold RingMicromega.eval_nformula in HCutR.
               change (RingMicromega.eval_pol Z.add Z.mul (fun x : Z => x)) with eval_pol in HCutR.
               unfold eval_op1 in HCutR.
               destruct op1 ; simpl in Hop1 ; try discriminate;
                 rewrite eval_pol_add in HCutR; simpl in HCutR.
               + rewrite Z.add_move_0_l in HCutR; rewrite HCutR, Z.opp_involutive; reflexivity.
               + now apply Z.le_sub_le_add_r in HCutR.
               (**)
             - apply (fun H => is_pol_Z0_eval_pol _ H env) in HZ0.
               rewrite eval_pol_add, Z.add_move_r, Z.sub_0_l in HZ0.
               rewrite HZ0.
               apply  (eval_Psatz_sound env) in Hf1 ; auto.
               apply cutting_plane_sound with (1:= Hf1) in HCutL.
               unfold nformula_of_cutting_plane in HCutL.
               unfold eval_nformula in HCutL.
               unfold RingMicromega.eval_nformula in HCutL.
               change (RingMicromega.eval_pol Z.add Z.mul (fun x : Z => x)) with eval_pol in HCutL.
               unfold eval_op1 in HCutL.
               rewrite eval_pol_add in HCutL. simpl in HCutL.
               destruct op2 ; simpl in Hop2 ; try discriminate.
               + rewrite Z.add_move_r, Z.sub_0_l in HCutL.
                 now rewrite HCutL, Z.opp_involutive.
               + now rewrite <- Z.le_sub_le_add_l in HCutL.
           }
           revert Hfix.
           match goal with
           | |- context[?F pf (-z1) z2 = true] => set (FF := F)
           end.
           intros Hfix.
           assert (HH :forall x, -z1 <= x <= z2 -> exists pr,
                        (In pr pf /\
                           ZChecker ((PsubC Z.sub p1 x,Equal) :: l) pr = true)%Z). {
             clear HZ0 Hop1 Hop2 HCutL HCutR H0 H1.
             revert Hfix.
             generalize (-z1). clear z1. intro z1.
             revert z1 z2.
             induction pf as [|a pf IHpf];simpl ;intros z1 z2 Hfix x **.
             - revert Hfix.
               now case (Z.gtb_spec); [ | easy ]; intros LT; elim (Zorder.Zlt_not_le _ _ LT); transitivity x.
             - flatten_bool.
               match goal with [ H' : _ <= x <= _ |- _ ] => rename H' into H0 end.
               match goal with [ H' : FF pf (z1 + 1) z2 = true |- _ ] => rename H' into H2 end.
               destruct (ZArith_dec.Z_le_lt_eq_dec _ _ (proj1 H0)) as [ LT | -> ].
               2: exists a; auto.
               rewrite <- Z.le_succ_l in LT.
               assert (LE: (Z.succ z1 <= x <= z2)%Z) by intuition.
               elim IHpf with (2:=H2) (3:= LE).
               + intros x0 ?.
                 exists x0 ; split;tauto.
               + intros until 1.
                 apply H ; auto.
                 cbv [ltof] in *.
                 cbn [bdepth] in *.
                 eauto using Nat.lt_le_trans, le_n_S, Nat.le_max_r.
           }
           (*/asser *)
           destruct (HH _ H1) as [pr [Hin Hcheker]].
           assert (make_impl (eval_nformula env) ((PsubC Z.sub p1 (eval_pol env p1),Equal) :: l) False) as H2. {
             eapply (H pr)  ;auto.
             apply in_bdepth ; auto.
           }
           rewrite <- make_conj_impl in H2.
           apply H2.
           rewrite  make_conj_cons.
           split ;auto.
           unfold  eval_nformula.
           unfold RingMicromega.eval_nformula.
           simpl.
           rewrite (RingMicromega.PsubC_ok Zsor ZSORaddon).
           unfold eval_pol. ring.
        -- discriminate.
      * (* No cutting plane *)
        intros H0 H1 H2 env.
        rewrite <- make_conj_impl.
        intros H3.
        apply eval_Psatz_sound with (2:= Hf1) in H3.
        apply genCuttingPlaneNone with (2:= H3) ; auto.
    + (* No Cutting plane (bis) *)
      intros H0 H1 env.
      rewrite <- make_conj_impl.
      intros H2.
      apply eval_Psatz_sound with (2:= Hf2) in H2.
      apply genCuttingPlaneNone with (2:= H2) ; auto.
  - intros l.
    unfold ZChecker.
    fold ZChecker.
    set (fr := (max_var_nformulae l)%positive).
    set (z1 := (Pos.succ fr)) in *.
    set (t1 := (Pos.succ z1)) in *.
    destruct (x <=? fr)%positive eqn:LE ; [|congruence].
    intros H0 env.
    set (env':= fun v => if Pos.eqb v z1
                      then if Z.leb (env x) 0 then 0 else env x
                      else if Pos.eqb v t1
                           then if Z.leb (env x) 0 then -(env x) else 0
                           else env v).
    apply (fun H' ck => H _ H' _ ck env') in H0.
    + rewrite <- make_conj_impl in *.
      intro H1.
      rewrite !make_conj_cons in H0.
      apply H0 ; repeat split.
      *
        apply eval_nformula_mk_eq_pos.
        unfold env'.
        rewrite! Pos.eqb_refl.
        replace (x=?z1)%positive with false.
        1:replace (x=?t1)%positive with false.
        1:replace (t1=?z1)%positive with false.
        1:destruct (env x <=? 0); ring.
        { unfold t1.
          symmetry; apply not_true_iff_false; rewrite Pos.eqb_eq; symmetry; apply Pos.succ_discr.
        }
        {
          unfold t1, z1.
          symmetry; apply not_true_iff_false; rewrite Pos.eqb_eq; intros ->.
          apply Pos.leb_le, Pos.lt_succ_r in LE; rewrite <-?Pos.succ_lt_mono in *.
          pose proof Pos.lt_not_add_l fr 1; rewrite Pos.add_1_r in *; contradiction.
        }
        {
          unfold z1.
          symmetry; apply not_true_iff_false; rewrite Pos.eqb_eq; intros ->.
          apply Pos.leb_le, Pos.lt_succ_r in LE; rewrite <-?Pos.succ_lt_mono in *.
          case (Pos.lt_irrefl _ LE).
        }
      *
        apply eval_nformula_bound_var.
        unfold env'.
        rewrite! Pos.eqb_refl.
        destruct (env x <=? 0) eqn:EQ.
        -- compute. congruence.
        -- rewrite Z.leb_gt in EQ.
           apply Z.ge_le_iff, Z.lt_le_incl; trivial.
      *
        apply eval_nformula_bound_var.
        unfold env'.
        rewrite! Pos.eqb_refl.
        replace (t1 =? z1)%positive with false.
        -- destruct (env x <=? 0) eqn:EQ.
           ++ rewrite Z.leb_le in EQ.
              apply Z.ge_le_iff. rewrite Z.opp_le_mono, Z.opp_involutive; trivial.
           ++ compute; congruence.
        -- unfold t1.
           clear.
           symmetry; apply not_true_iff_false; rewrite Pos.eqb_eq; symmetry; apply Pos.succ_discr.
      *
        rewrite (agree_env_eval_nformulae _ env') in H1;auto.
        unfold agree_env; intros x0 H2.
        unfold env'.
        replace (x0 =? z1)%positive with false.
        1:replace (x0 =? t1)%positive with false.
        1:reflexivity.
        {
          unfold t1, z1.
          symmetry; apply not_true_iff_false; rewrite Pos.eqb_eq; intros ->.
          apply Pos.lt_succ_r in H2; rewrite <-?Pos.succ_lt_mono in *.
          pose proof Pos.lt_not_add_l (max_var_nformulae l) 1; rewrite Pos.add_1_r in *; contradiction.
        }
        {
          unfold z1, fr in *.
          symmetry; apply not_true_iff_false; rewrite Pos.eqb_eq; intros ->.
          apply Pos.lt_succ_r in H2; rewrite <-?Pos.succ_lt_mono in *.
          case (Pos.lt_irrefl _ H2).
        }
    + unfold ltof.
      simpl.
      apply Nat.lt_succ_diag_r.
Qed.

Definition ZTautoChecker  (f : BFormula (Formula Z) Tauto.isProp) (w: list ZArithProof): bool :=
  @tauto_checker (Formula Z) (NFormula Z) unit Zunsat Zdeduce normalise negate  ZArithProof (fun cl => ZChecker (List.map fst cl)) f w.

Lemma ZTautoChecker_sound : forall f w, ZTautoChecker f w = true -> forall env, eval_bf  (Zeval_formula env)  f.
Proof.
  intros f w.
  unfold ZTautoChecker.
  apply (tauto_checker_sound _ _ _ _ eval_nformula).
  - apply Zeval_nformula_dec.
  - intros t ? env.
  unfold eval_nformula. unfold RingMicromega.eval_nformula.
  destruct t.
  apply (check_inconsistent_sound Zsor ZSORaddon) ; auto.
  - unfold Zdeduce. intros ? ? ? H **. revert H.
     apply (nformula_plus_nformula_correct Zsor ZSORaddon); auto.
  -
    intros ? ? ? ? H.
    rewrite normalise_correct  in H.
    rewrite Zeval_formula_compat; auto.
  -
    intros ? ? ? ? H.
    rewrite negate_correct in H ; auto.
    rewrite Tauto.hold_eNOT.
    rewrite Zeval_formula_compat; auto.
  - intros t w0.
    unfold eval_tt.
    intros H env.
    rewrite (make_impl_map (eval_nformula env)).
    + eapply ZChecker_sound; eauto.
    + tauto.
Qed.
Fixpoint xhyps_of_pt (base:nat) (acc : list nat) (pt:ZArithProof)  : list nat :=
  match pt with
    | DoneProof => acc
    | RatProof c pt => xhyps_of_pt (S base ) (xhyps_of_psatz base acc c) pt
    | CutProof c pt => xhyps_of_pt (S base ) (xhyps_of_psatz base acc c) pt
    | SplitProof p pt1 pt2 => xhyps_of_pt (S base) (xhyps_of_pt (S base) acc pt1) pt2
    | EnumProof c1 c2 l =>
      let acc := xhyps_of_psatz base (xhyps_of_psatz base acc c2) c1 in
        List.fold_left (xhyps_of_pt (S base)) l acc
    | ExProof _ pt  =>  xhyps_of_pt (S (S (S base ))) acc pt
  end.

Definition hyps_of_pt (pt : ZArithProof) : list nat := xhyps_of_pt 0 nil pt.

Open Scope Z_scope.

(** To ease bindings from ml code **)
Definition make_impl := Refl.make_impl.
Definition make_conj := Refl.make_conj.

Require VarMap.

(*Definition varmap_type := VarMap.t Z. *)
Definition env := PolEnv Z.
Definition node := @VarMap.Branch Z.
Definition empty := @VarMap.Empty Z.
Definition leaf := @VarMap.Elt Z.

Definition coneMember := ZWitness.

Definition eval := eval_formula.

#[deprecated(note="Use [prod positive nat]", since="9.0")]
Definition prod_pos_nat := prod positive nat.

#[deprecated(use=Z.to_N, since="9.0")]
Notation n_of_Z := Z.to_N (only parsing).
