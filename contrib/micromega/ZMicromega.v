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

Ltac flatten_bool :=
  repeat match goal with
           [ id : (_ && _)%bool = true |- _ ] =>  destruct (andb_prop _ _ id); clear id
           |  [ id : (_ || _)%bool = true |- _ ] =>  destruct (orb_prop _ _ id); clear id
         end.

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

Lemma Zeq_bool_neq : forall x y, Zeq_bool x y = false -> x <> y.
Proof.
  red ; intros.
  subst.
  unfold Zeq_bool in H.
  rewrite Zcompare_refl  in H.
  discriminate.
Qed.

Lemma ZSORaddon :
  SORaddon 0 1 Zplus Zmult Zminus Zopp  (@eq Z) Zle (* ring elements *)
  0%Z 1%Z Zplus Zmult Zminus Zopp (* coefficients *)
  Zeq_bool Zle_bool
  (fun x => x) (fun x => x) (pow_N 1 Zmult).
Proof.
  constructor.
  constructor ; intros ; try reflexivity.
  apply Zeqb_ok ; auto.
  constructor.
  reflexivity.
  intros x y.
  apply Zeq_bool_neq ; auto.
  apply Zle_bool_imp_le.
Qed.


(*Definition Zeval_expr :=  eval_pexpr 0 Zplus Zmult Zminus Zopp  (fun x => x) (fun x => Z_of_N x) (Zpower).*)

Fixpoint Zeval_expr (env: PolEnv Z) (e: PExpr Z) : Z :=
  match e with
    | PEc c =>  c
    | PEX j =>  env j
    | PEadd pe1 pe2 => (Zeval_expr env pe1) + (Zeval_expr env pe2)
    | PEsub pe1 pe2 => (Zeval_expr env pe1) - (Zeval_expr env pe2)
    | PEmul pe1 pe2 => (Zeval_expr env pe1) * (Zeval_expr env pe2)
    | PEopp pe1 => - (Zeval_expr env pe1)
    | PEpow pe1 n => Zpower (Zeval_expr env pe1)  (Z_of_N n)
  end.

Lemma Zeval_expr_simpl : forall env e,
  Zeval_expr env e = 
  match e with
    | PEc c =>  c
    | PEX j =>  env j
    | PEadd pe1 pe2 => (Zeval_expr env pe1) + (Zeval_expr env pe2)
    | PEsub pe1 pe2 => (Zeval_expr env pe1) - (Zeval_expr env pe2)
    | PEmul pe1 pe2 => (Zeval_expr env pe1) * (Zeval_expr env pe2)
    | PEopp pe1 => - (Zeval_expr env pe1)
    | PEpow pe1 n => Zpower (Zeval_expr env pe1)  (Z_of_N n)
  end.
Proof.
  destruct e ; reflexivity.
Qed.


Definition Zeval_expr' := eval_pexpr  Zplus Zmult Zminus Zopp (fun x => x) (fun x => x) (pow_N 1 Zmult).

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



Lemma Zeval_expr_compat : forall env e, Zeval_expr env e = Zeval_expr' env e.
Proof.
  induction e ; simpl ; subst ; try congruence.
  rewrite IHe.
  apply ZNpower.
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

Definition Zeval_formula (e: PolEnv Z) (ff : Formula Z) :=
  let (lhs,o,rhs) := ff in Zeval_op2 o (Zeval_expr e lhs) (Zeval_expr e rhs).

Definition Zeval_formula' :=
  eval_formula  Zplus Zmult Zminus Zopp (@eq Z) Zle Zlt (fun x => x) (fun x => x) (pow_N 1 Zmult).

Lemma Zeval_formula_compat : forall env f, Zeval_formula env f <-> Zeval_formula' env f.
Proof.
  intros.
  unfold Zeval_formula.
  destruct f.
  repeat rewrite Zeval_expr_compat.
  unfold Zeval_formula'.
  unfold Zeval_expr'.
  split ; destruct Fop ; simpl; auto with zarith.
Qed.



Definition Zeval_nformula :=
  eval_nformula 0 Zplus Zmult Zminus Zopp (@eq Z) Zle Zlt (fun x => x) (fun x => x) (pow_N 1 Zmult).

Definition Zeval_op1 (o : Op1) : Z -> Prop :=
match o with
| Equal => fun x : Z => x = 0
| NonEqual => fun x : Z => x <> 0
| Strict => fun x : Z => 0 < x
| NonStrict => fun x : Z => 0 <= x
end.

Lemma Zeval_nformula_simpl : forall env f, Zeval_nformula env f = (let (p, op) := f in Zeval_op1 op (Zeval_expr env p)).
Proof.
  intros.
  destruct f.
  rewrite Zeval_expr_compat.
  reflexivity.
Qed.
  
Lemma Zeval_nformula_dec : forall env d, (Zeval_nformula env d) \/ ~ (Zeval_nformula env d).
Proof.
  exact (fun env d =>eval_nformula_dec Zsor (fun x => x) (fun x => x) (pow_N 1%Z Zmult) env d).
Qed.

Definition ZWitness := ConeMember Z.

Definition ZWeakChecker := check_normalised_formulas 0 1 Zplus Zmult Zminus Zopp Zeq_bool Zle_bool.

Lemma ZWeakChecker_sound :   forall (l : list (NFormula Z)) (cm : ZWitness),
  ZWeakChecker l cm = true ->
  forall env, make_impl (Zeval_nformula env) l False.
Proof.
  intros l cm H.
  intro.
  unfold Zeval_nformula.
  apply (checker_nf_sound Zsor ZSORaddon l cm).
  unfold ZWeakChecker in H.
  exact H.
Qed.

Definition xnormalise (t:Formula Z) : list (NFormula Z)  :=
  let (lhs,o,rhs) := t in
    match o with
      | OpEq => 
        ((PEsub lhs (PEadd rhs (PEc 1))),NonStrict)::((PEsub rhs (PEadd lhs (PEc 1))),NonStrict)::nil
      | OpNEq => (PEsub lhs rhs,Equal) :: nil
      | OpGt   => (PEsub rhs lhs,NonStrict) :: nil
      | OpLt => (PEsub lhs rhs,NonStrict) :: nil
      | OpGe => (PEsub rhs (PEadd lhs (PEc 1)),NonStrict) :: nil
      | OpLe => (PEsub lhs (PEadd rhs (PEc 1)),NonStrict) :: nil
    end.

Require Import Tauto.

Definition normalise (t:Formula Z) : cnf (NFormula Z) :=
  List.map  (fun x => x::nil) (xnormalise t).


Lemma normalise_correct : forall env t, eval_cnf (Zeval_nformula env) (normalise t) <-> Zeval_formula env t.
Proof.
  unfold normalise, xnormalise ; simpl ; intros env t.
  rewrite Zeval_formula_compat.
  unfold eval_cnf.
  destruct t as [lhs o rhs]; case_eq o ; simpl;
    generalize (   eval_pexpr  Zplus Zmult Zminus Zopp (fun x : Z => x)
      (fun x : BinNat.N => x) (pow_N 1 Zmult) env lhs);
    generalize (eval_pexpr  Zplus Zmult Zminus Zopp (fun x : Z => x)
      (fun x : BinNat.N => x) (pow_N 1 Zmult) env rhs) ; intros z1 z2 ; intros ; subst;
    intuition (auto with zarith).
Qed.
  
Definition xnegate (t:RingMicromega.Formula Z) : list (NFormula Z)  :=
  let (lhs,o,rhs) := t in
    match o with
      | OpEq  => (PEsub lhs rhs,Equal) :: nil
      | OpNEq => ((PEsub lhs (PEadd rhs (PEc 1))),NonStrict)::((PEsub rhs (PEadd lhs (PEc 1))),NonStrict)::nil
      | OpGt  => (PEsub lhs (PEadd rhs (PEc 1)),NonStrict) :: nil
      | OpLt  => (PEsub rhs (PEadd lhs (PEc 1)),NonStrict) :: nil
      | OpGe  => (PEsub lhs rhs,NonStrict) :: nil
      | OpLe  => (PEsub rhs lhs,NonStrict) :: nil
    end.

Definition negate (t:RingMicromega.Formula Z) : cnf (NFormula Z) :=
  List.map  (fun x => x::nil) (xnegate t).

Lemma negate_correct : forall env t, eval_cnf (Zeval_nformula env) (negate t) <-> ~ Zeval_formula env t.
Proof.
  unfold negate, xnegate ; simpl ; intros env t.
  rewrite Zeval_formula_compat.
  unfold eval_cnf.
  destruct t as [lhs o rhs]; case_eq o ; simpl ;
    generalize (   eval_pexpr  Zplus Zmult Zminus Zopp (fun x : Z => x)
      (fun x : BinNat.N => x) (pow_N 1 Zmult) env lhs);
    generalize (eval_pexpr  Zplus Zmult Zminus Zopp (fun x : Z => x)
      (fun x : BinNat.N => x) (pow_N 1 Zmult) env rhs) ; intros z1 z2 ; intros ; 
    intuition (auto with zarith).
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


(* In this case, a certificate is made of a pair of inequations, in 1 variable,
   that do not have an integer solution.
   => modify the fourier elimination
   *)
Require Import QArith.


Inductive ProofTerm : Type :=
| RatProof : ZWitness -> ProofTerm
| CutProof : PExprC Z -> Q -> ZWitness -> ProofTerm -> ProofTerm
| EnumProof : Q ->  PExprC Z ->  Q -> ZWitness -> ZWitness -> list ProofTerm -> ProofTerm.

(* n/d <= x  -> d*x - n >= 0 *)

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
 

Definition cutChecker (l:list (NFormula Z)) (e: PExpr Z) (lb:Q) (pf : ZWitness) : option (NFormula Z) :=
    let (lb,lc) :=  (makeLb e lb,makeLbCut e lb) in
      if ZWeakChecker (neg_nformula lb::l) pf then Some lc else None.


Fixpoint ZChecker (l:list (NFormula Z)) (pf : ProofTerm)  {struct pf} : bool :=
  match pf with
    | RatProof pf => ZWeakChecker l pf
    | CutProof e q pf rst => 
      match cutChecker l e q pf with
        | None => false
        | Some c => ZChecker  (c::l) rst
      end
    | EnumProof lb e ub  pf1 pf2 rst => 
      match cutChecker l e lb  pf1 , cutChecker l (PEopp e) (Qopp ub) pf2 with
        | None ,  _  | _ , None => false
        | Some _  , Some _ => let (lb',ub') := (qceiling lb, Zopp (qceiling (- ub))) in
          (fix label (pfs:list ProofTerm) :=
            fun lb ub => 
              match pfs with
                | nil => if Z_gt_dec lb ub then true else false
                | pf::rsr => andb (ZChecker  ((PEsub e (PEc lb), Equal) :: l) pf) (label rsr (Zplus lb 1%Z) ub) 
              end)
               rst lb' ub'
      end
  end.


Lemma ZChecker_simpl : forall (pf : ProofTerm) (l:list (NFormula Z)),
  ZChecker  l pf = 
  match pf with
    | RatProof pf => ZWeakChecker l pf
    | CutProof e q pf rst => 
      match cutChecker l e q pf with
        | None => false
        | Some c => ZChecker  (c::l) rst
      end
    | EnumProof lb e ub  pf1 pf2 rst => 
      match cutChecker l e lb  pf1 , cutChecker l (PEopp e) (Qopp ub) pf2 with
        | None ,  _  | _ , None => false
        | Some _  , Some _ => let (lb',ub') := (qceiling lb, Zopp (qceiling (- ub))) in
          (fix label (pfs:list ProofTerm) :=
            fun lb ub => 
              match pfs with
                | nil => if Z_gt_dec lb ub then true else false
                | pf::rsr => andb (ZChecker  ((PEsub e (PEc lb), Equal) :: l) pf) (label rsr (Zplus lb 1%Z) ub) 
              end)
               rst lb' ub'
      end
  end.
Proof.
  destruct pf ; reflexivity.
Qed.

(*
Fixpoint depth (n:nat) : ProofTerm -> option nat :=
  match n with
    | O => fun pf => None
    | S n => 
      fun pf => 
        match pf with
          | RatProof _ => Some O
          | CutProof _ _ _ p =>  option_map S  (depth n p)
          | EnumProof  _ _ _ _ _ l => 
            let f := fun pf x => 
              match x , depth n pf with
                | None ,  _ | _ , None => None
                | Some n1 , Some n2 => Some (Max.max n1 n2)
              end in
            List.fold_right f  (Some O) l
        end
  end.
*)
Fixpoint bdepth (pf : ProofTerm) : nat :=
  match pf with
    | RatProof _ =>  O
    | CutProof _ _ _ p =>   S  (bdepth p)
    | EnumProof _ _ _ _ _ l => S (List.fold_right (fun pf x => Max.max (bdepth pf) x)   O l)
  end.

Require Import Wf_nat.

Lemma in_bdepth : forall l a b p c c0  y, In y l ->  ltof ProofTerm bdepth y (EnumProof a b p c c0 l).
Proof.
  induction l.
  simpl.
  tauto.
  simpl.
  intros.
  destruct H.
  subst.
  unfold ltof.
  simpl.
  generalize (         (fold_right
            (fun (pf : ProofTerm) (x : nat) => Max.max (bdepth pf) x) 0%nat l)).
  intros.
  generalize (bdepth y) ; intros.
  generalize (Max.max_l n0 n) (Max.max_r n0 n).
  omega.
  generalize (IHl a0 b p c c0 y  H).
  unfold ltof.
  simpl.
  generalize (      (fold_right (fun (pf : ProofTerm) (x : nat) => Max.max (bdepth pf) x) 0%nat
         l)).
  intros.
  generalize (Max.max_l (bdepth a) n) (Max.max_r (bdepth a) n).
  omega.
Qed.

Lemma lb_lbcut : forall env e q,  Zeval_nformula env (makeLb e q) -> Zeval_nformula env (makeLbCut e q).
Proof.
  unfold makeLb, makeLbCut.
  destruct q.
  rewrite Zeval_nformula_simpl.
  rewrite Zeval_nformula_simpl.
  unfold Zeval_op1.
  rewrite Zeval_expr_simpl.
  rewrite Zeval_expr_simpl.
  rewrite Zeval_expr_simpl.
  intro.
  rewrite Zeval_expr_simpl.
  revert H.
  generalize (Zeval_expr env e).
  rewrite Zeval_expr_simpl.
  rewrite Zeval_expr_simpl.
  unfold qceiling.
  intros.
  assert ( z >= ceiling Qnum (' Qden))%Z.
  apply narrow_interval_lower_bound.
  compute.
  reflexivity.
  destruct z ; auto with zarith.
  auto with zarith.
Qed.

Lemma cutChecker_sound : forall e lb pf l res, cutChecker l e lb pf = Some res -> 
  forall env, make_impl  (Zeval_nformula env) l (Zeval_nformula env res).
Proof.
  unfold cutChecker.
  intros.
  revert H.
  case_eq (ZWeakChecker (neg_nformula (makeLb e lb) :: l) pf); intros ; [idtac | discriminate].
  generalize (ZWeakChecker_sound _ _  H env).
  intros.
  inversion H0 ; subst ; clear H0.
  apply -> make_conj_impl.
  simpl in H1.
  rewrite <- make_conj_impl in H1.
  intros.
  apply -> neg_nformula_sound ; auto.
  red ; intros.
  apply H1 ; auto.
  clear H H1 H0.
  generalize (lb_lbcut env e lb).
  intros.
  destruct (Zeval_nformula_dec  env ((neg_nformula (makeLb e lb)))).
  auto.
  rewrite -> neg_nformula_sound in H0.
  assert (HH := H H0).
  rewrite <- neg_nformula_sound in HH.
  tauto.
  reflexivity.
  unfold makeLb.
  destruct lb.
  reflexivity.
Qed.


Lemma cutChecker_sound_bound : forall e lb pf l res, cutChecker l e lb pf = Some res -> 
  forall env,  make_conj  (Zeval_nformula env) l  -> (Zeval_expr env e >= qceiling lb)%Z.
Proof.
  intros.
  generalize (cutChecker_sound _ _ _ _ _ H env).
  intros.
  rewrite  <- (make_conj_impl) in H1. 
  generalize (H1 H0).
  unfold cutChecker in H.
  destruct (ZWeakChecker (neg_nformula (makeLb e lb) :: l) pf).
  unfold makeLbCut in H.
  inversion H ; subst.
  clear H.
  simpl.
  rewrite Zeval_expr_compat.
  unfold Zeval_expr'.
  auto with zarith.
  discriminate.
Qed.


Lemma ZChecker_sound : forall w l, ZChecker l w = true -> forall env, make_impl  (Zeval_nformula env)  l False.
Proof.
  induction w    using (well_founded_ind (well_founded_ltof _ bdepth)).
  destruct w.
  (* RatProof *)
  simpl.
  intros.
  eapply ZWeakChecker_sound.
  apply H0.
  (* CutProof *)
  simpl.
  intro.
  case_eq (cutChecker l p q z) ; intros.
  generalize (cutChecker_sound _ _ _ _ _ H0 env).
  intro.
  assert (make_impl  (Zeval_nformula env) (n::l) False).
  eapply (H w) ; auto.
  unfold ltof.
  simpl.
  auto with arith.
  simpl in H3.
  rewrite <- make_conj_impl in H2.
  rewrite <- make_conj_impl in H3.
  rewrite <- make_conj_impl.
  tauto.
  discriminate.
  (* EnumProof *)
  intro.
  rewrite ZChecker_simpl.
  case_eq (cutChecker l0 p q z).
  rename q into llb.
  case_eq (cutChecker l0 (PEopp p) (- q0) z0).
  intros.
  rename q0 into uub.
  (* get the bounds of the enum *)
  rewrite <- make_conj_impl.
  intro.
  assert (qceiling llb <= Zeval_expr env p <= - qceiling ( - uub))%Z.
  generalize (cutChecker_sound_bound _ _ _ _ _ H0 env H3).
  generalize (cutChecker_sound_bound _ _ _ _ _ H1 env H3).
  intros.
  rewrite Zeval_expr_simpl in H5.
  auto with zarith.
  clear H0 H1.
  revert H2 H3 H4.
  generalize (qceiling llb) (- qceiling (- uub))%Z.
  set (FF := (fix label (pfs : list ProofTerm) (lb ub : Z) {struct pfs} : bool :=
    match pfs with
      | nil => if Z_gt_dec lb ub then true else false
      | pf :: rsr =>
        (ZChecker ((PEsub p (PEc lb), Equal) :: l0) pf &&
          label rsr (lb + 1)%Z ub)%bool
    end)).
  intros z1 z2.
  intros.
  assert (forall x, z1 <= x <= z2 -> exists pr, 
    (In pr l /\
      ZChecker  ((PEsub p (PEc x),Equal) :: l0) pr = true))%Z.
  clear H.
  revert H2.
  clear H4.
  revert z1 z2.
  induction l;simpl ;intros.
  destruct (Z_gt_dec z1 z2).
  intros.
  apply False_ind ; omega.
  discriminate.
  intros.
  simpl in H2.
  flatten_bool.
  assert (HH:(x = z1 \/ z1 +1 <=x)%Z) by omega.
  destruct HH.
  subst.
  exists a ; auto.
  assert (z1 + 1 <= x <= z2)%Z by omega.
  destruct (IHl _ _ H1 _ H4).
  destruct H5.
  exists x0 ; split;auto.
  (*/asser *)
  destruct (H0 _ H4) as [pr [Hin Hcheker]].
  assert (make_impl (Zeval_nformula env) ((PEsub p (PEc (Zeval_expr env p)),Equal) :: l0) False).
  apply (H pr);auto.
  apply in_bdepth ; auto.
  rewrite <- make_conj_impl in H1.
  apply H1.
  rewrite  make_conj_cons.
  split ;auto.
  rewrite Zeval_nformula_simpl;
    unfold Zeval_op1;
      rewrite Zeval_expr_simpl.
  generalize (Zeval_expr env p).
  intros.
  rewrite Zeval_expr_simpl.
  auto with zarith.
  intros ; discriminate.
  intros ; discriminate.
Qed.

Definition ZTautoChecker  (f : BFormula (Formula Z)) (w: list ProofTerm): bool :=
  @tauto_checker (Formula Z) (NFormula Z) normalise negate  ProofTerm ZChecker f w.

Lemma ZTautoChecker_sound : forall f w, ZTautoChecker f w = true -> forall env, eval_f  (Zeval_formula env)  f.
Proof.
  intros f w.
  unfold ZTautoChecker.
  apply (tauto_checker_sound  Zeval_formula Zeval_nformula).
  apply Zeval_nformula_dec.
  intros env t.
  rewrite normalise_correct ; auto.
  intros env t.
  rewrite negate_correct ; auto.
  intros t w0.
  apply ZChecker_sound.
Qed.


Open Scope Z_scope.


Fixpoint map_cone (f: nat -> nat) (e:ZWitness) : ZWitness :=
  match e with
    | S_In n         => S_In _ (f n)
    | S_Ideal e cm   => S_Ideal e (map_cone f cm)
    | S_Square _     => e
    | S_Monoid l     => S_Monoid _ (List.map f l)
    | S_Mult cm1 cm2 => S_Mult (map_cone f cm1) (map_cone f cm2)
    | S_Add cm1 cm2  => S_Add (map_cone f cm1) (map_cone f cm2)
    |  _             => e
  end.

Fixpoint indexes (e:ZWitness) : list nat :=
  match e with
    | S_In n         => n::nil
    | S_Ideal e cm   => indexes cm
    | S_Square e     => nil
    | S_Monoid l     => l
    | S_Mult cm1 cm2 => (indexes cm1)++ (indexes cm2)
    | S_Add cm1 cm2  => (indexes cm1)++ (indexes cm2)
    |  _             => nil
  end.
  
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

Definition eval := Zeval_formula.

Definition prod_pos_nat := prod positive nat.

Require Import Int.


Definition n_of_Z (z:Z) : BinNat.N :=
  match z with
    | Z0 => N0
    | Zpos p => Npos p
    | Zneg p => N0
  end.



