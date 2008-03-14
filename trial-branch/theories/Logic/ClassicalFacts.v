(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Some facts and definitions about classical logic

Table of contents:

1. Propositional degeneracy = excluded-middle + propositional extensionality

2. Classical logic and proof-irrelevance

2.1. CC |- prop. ext. + A inhabited -> (A = A->A) -> A has fixpoint

2.2. CC |- prop. ext. + dep elim on bool -> proof-irrelevance

2.3. CIC |- prop. ext. -> proof-irrelevance

2.4. CC |- excluded-middle + dep elim on bool -> proof-irrelevance

2.5. CIC |- excluded-middle -> proof-irrelevance

3. Weak classical axioms

3.1. Weak excluded middle

3.2. G�del-Dummett axiom and right distributivity of implication over
     disjunction

3 3. Independence of general premises and drinker's paradox

*)

(************************************************************************)
(** * Prop degeneracy = excluded-middle + prop extensionality      *)
(**
 i.e.        [(forall A, A=True \/ A=False)
                         <->
       (forall A, A\/~A) /\ (forall A B, (A<->B) -> A=B)]
*)

(** [prop_degeneracy] (also referred to as propositional completeness)
    asserts (up to consistency) that there are only two distinct formulas *)
Definition prop_degeneracy := forall A:Prop, A = True \/ A = False.

(** [prop_extensionality] asserts that equivalent formulas are equal *)
Definition prop_extensionality := forall A B:Prop, (A <-> B) -> A = B.

(** [excluded_middle] asserts that we can reason by case on the truth
    or falsity of any formula *)
Definition excluded_middle := forall A:Prop, A \/ ~ A.

(** We show [prop_degeneracy <-> (prop_extensionality /\ excluded_middle)] *)

Lemma prop_degen_ext : prop_degeneracy -> prop_extensionality.
Proof.
  intros H A B [Hab Hba].
  destruct (H A); destruct (H B).
    rewrite H1; exact H0.
    absurd B.
      rewrite H1; exact (fun H => H).
      apply Hab; rewrite H0; exact I.
    absurd A.
      rewrite H0; exact (fun H => H).
      apply Hba; rewrite H1; exact I.
    rewrite H1; exact H0.
Qed.

Lemma prop_degen_em : prop_degeneracy -> excluded_middle.
Proof.
  intros H A.
  destruct (H A).
    left; rewrite H0; exact I.
    right; rewrite H0; exact (fun x => x).
Qed.

Lemma prop_ext_em_degen :
  prop_extensionality -> excluded_middle -> prop_degeneracy.
Proof.
  intros Ext EM A.
  destruct (EM A).
    left; apply (Ext A True); split;
     [ exact (fun _ => I) | exact (fun _ => H) ].
    right; apply (Ext A False); split; [ exact H | apply False_ind ].
Qed.

(** A weakest form of propositional extensionality: extensionality for
    provable propositions only *)

Definition provable_prop_extensionality := forall A:Prop, A -> A = True.

Lemma provable_prop_ext :
  prop_extensionality -> provable_prop_extensionality.
Proof.
  intros Ext A Ha; apply Ext; split; trivial.
Qed.

(************************************************************************)
(** * Classical logic and proof-irrelevance *)

(************************************************************************)
(** ** CC |- prop ext + A inhabited -> (A = A->A) -> A has fixpoint *)

(** We successively show that:

   [prop_extensionality]
     implies equality of [A] and [A->A] for inhabited [A], which 
     implies the existence of a (trivial) retract from [A->A] to [A]
        (just take the identity), which
     implies the existence of a fixpoint operator in [A]
        (e.g. take the Y combinator of lambda-calculus)

*)

Definition inhabited (A:Prop) := A.

Lemma prop_ext_A_eq_A_imp_A :
  prop_extensionality -> forall A:Prop, inhabited A -> (A -> A) = A.
Proof.
  intros Ext A a.
  apply (Ext (A -> A) A); split; [ exact (fun _ => a) | exact (fun _ _ => a) ].
Qed.

Record retract (A B:Prop) : Prop := 
  {f1 : A -> B; f2 : B -> A; f1_o_f2 : forall x:B, f1 (f2 x) = x}.

Lemma prop_ext_retract_A_A_imp_A :
  prop_extensionality -> forall A:Prop, inhabited A -> retract A (A -> A).
Proof.
  intros Ext A a.
  rewrite (prop_ext_A_eq_A_imp_A Ext A a).
  exists (fun x:A => x) (fun x:A => x).
  reflexivity.
Qed.

Record has_fixpoint (A:Prop) : Prop := 
  {F : (A -> A) -> A; Fix : forall f:A -> A, F f = f (F f)}.

Lemma ext_prop_fixpoint :
  prop_extensionality -> forall A:Prop, inhabited A -> has_fixpoint A.
Proof.
  intros Ext A a.
  case (prop_ext_retract_A_A_imp_A Ext A a); intros g1 g2 g1_o_g2.
  exists (fun f => (fun x:A => f (g1 x x)) (g2 (fun x => f (g1 x x)))).
  intro f.
  pattern (g1 (g2 (fun x:A => f (g1 x x)))) at 1 in |- *.
  rewrite (g1_o_g2 (fun x:A => f (g1 x x))).
  reflexivity.
Qed.

(** Remark: [prop_extensionality] can be replaced in lemma [ext_prop_fixpoint]
    by the weakest property [provable_prop_extensionality].
*)

(************************************************************************)
(** ** CC |- prop_ext /\ dep elim on bool -> proof-irrelevance  *)

(** [proof_irrelevance] asserts equality of all proofs of a given formula *)
Definition proof_irrelevance := forall (A:Prop) (a1 a2:A), a1 = a2.

(** Assume that we have booleans with the property that there is at most 2
    booleans (which is equivalent to dependent case analysis). Consider
    the fixpoint of the negation function: it is either true or false by
    dependent case analysis, but also the opposite by fixpoint. Hence
    proof-irrelevance.

    We then map equality of boolean proofs to proof irrelevance in all
    propositions.
*)

Section Proof_irrelevance_gen.

  Variable bool : Prop.
  Variable true : bool.
  Variable false : bool.
  Hypothesis bool_elim : forall C:Prop, C -> C -> bool -> C.
  Hypothesis
    bool_elim_redl : forall (C:Prop) (c1 c2:C), c1 = bool_elim C c1 c2 true.
  Hypothesis
    bool_elim_redr : forall (C:Prop) (c1 c2:C), c2 = bool_elim C c1 c2 false.
  Let bool_dep_induction :=
  forall P:bool -> Prop, P true -> P false -> forall b:bool, P b.

  Lemma aux : prop_extensionality -> bool_dep_induction -> true = false.
  Proof.
    intros Ext Ind.
    case (ext_prop_fixpoint Ext bool true); intros G Gfix.
    set (neg := fun b:bool => bool_elim bool false true b).
    generalize (refl_equal (G neg)).
    pattern (G neg) at 1 in |- *.
    apply Ind with (b := G neg); intro Heq.
    rewrite (bool_elim_redl bool false true).
    change (true = neg true) in |- *; rewrite Heq; apply Gfix.
    rewrite (bool_elim_redr bool false true).
    change (neg false = false) in |- *; rewrite Heq; symmetry  in |- *;
      apply Gfix.
  Qed.

  Lemma ext_prop_dep_proof_irrel_gen :
    prop_extensionality -> bool_dep_induction -> proof_irrelevance.
  Proof.
    intros Ext Ind A a1 a2.
    set (f := fun b:bool => bool_elim A a1 a2 b).
    rewrite (bool_elim_redl A a1 a2).
    change (f true = a2) in |- *.
    rewrite (bool_elim_redr A a1 a2).
    change (f true = f false) in |- *.
    rewrite (aux Ext Ind).
    reflexivity.
  Qed.

End Proof_irrelevance_gen.

(** In the pure Calculus of Constructions, we can define the boolean
    proposition bool = (C:Prop)C->C->C but we cannot prove that it has at
    most 2 elements.
*)

Section Proof_irrelevance_Prop_Ext_CC.
  
  Definition BoolP := forall C:Prop, C -> C -> C.
  Definition TrueP : BoolP := fun C c1 c2 => c1.
  Definition FalseP : BoolP := fun C c1 c2 => c2.
  Definition BoolP_elim C c1 c2 (b:BoolP) := b C c1 c2.
  Definition BoolP_elim_redl (C:Prop) (c1 c2:C) :
    c1 = BoolP_elim C c1 c2 TrueP := refl_equal c1.
  Definition BoolP_elim_redr (C:Prop) (c1 c2:C) :
    c2 = BoolP_elim C c1 c2 FalseP := refl_equal c2.
  
  Definition BoolP_dep_induction :=
    forall P:BoolP -> Prop, P TrueP -> P FalseP -> forall b:BoolP, P b.
  
  Lemma ext_prop_dep_proof_irrel_cc :
    prop_extensionality -> BoolP_dep_induction -> proof_irrelevance.
  Proof.
    exact (ext_prop_dep_proof_irrel_gen BoolP TrueP FalseP BoolP_elim BoolP_elim_redl
      BoolP_elim_redr).
  Qed.

End Proof_irrelevance_Prop_Ext_CC.

(** Remark: [prop_extensionality] can be replaced in lemma
    [ext_prop_dep_proof_irrel_gen] by the weakest property
    [provable_prop_extensionality].  
*)

(************************************************************************)
(** ** CIC |- prop. ext. -> proof-irrelevance                   *)

(** In the Calculus of Inductive Constructions, inductively defined booleans
    enjoy dependent case analysis, hence directly proof-irrelevance from
    propositional extensionality.
*)

Section Proof_irrelevance_CIC.
  
  Inductive boolP : Prop :=
    | trueP : boolP
    | falseP : boolP.
  Definition boolP_elim_redl (C:Prop) (c1 c2:C) :
    c1 = boolP_ind C c1 c2 trueP := refl_equal c1.
  Definition boolP_elim_redr (C:Prop) (c1 c2:C) :
    c2 = boolP_ind C c1 c2 falseP := refl_equal c2.
  Scheme boolP_indd := Induction for boolP Sort Prop.
  
  Lemma ext_prop_dep_proof_irrel_cic : prop_extensionality -> proof_irrelevance.
  Proof.
    exact (fun pe =>
      ext_prop_dep_proof_irrel_gen boolP trueP falseP boolP_ind boolP_elim_redl
      boolP_elim_redr pe boolP_indd).
  Qed.

End Proof_irrelevance_CIC.

(** Can we state proof irrelevance from propositional degeneracy
  (i.e. propositional extensionality + excluded middle) without
  dependent case analysis ?

  Berardi [[Berardi90]] built a model of CC interpreting inhabited
  types by the set of all untyped lambda-terms. This model satisfies
  propositional degeneracy without satisfying proof-irrelevance (nor
  dependent case analysis). This implies that the previous results
  cannot be refined.

  [[Berardi90]] Stefano Berardi, "Type dependence and constructive
  mathematics", Ph. D. thesis, Dipartimento Matematica, Universit� di
  Torino, 1990.
*)

(************************************************************************)
(** ** CC |- excluded-middle + dep elim on bool -> proof-irrelevance *)

(** This is a proof in the pure Calculus of Construction that
    classical logic in [Prop] + dependent elimination of disjunction entails
    proof-irrelevance.

    Reference:

    [[Coquand90]] T. Coquand, "Metamathematical Investigations of a
    Calculus of Constructions", Proceedings of Logic in Computer Science
    (LICS'90), 1990.

    Proof skeleton: classical logic + dependent elimination of
    disjunction + discrimination of proofs implies the existence of a
    retract from [Prop] into [bool], hence inconsistency by encoding any
    paradox of system U- (e.g. Hurkens' paradox).
*)

Require Import Hurkens.

Section Proof_irrelevance_EM_CC.
  
  Variable or : Prop -> Prop -> Prop.
  Variable or_introl : forall A B:Prop, A -> or A B.
  Variable or_intror : forall A B:Prop, B -> or A B.
  Hypothesis or_elim : forall A B C:Prop, (A -> C) -> (B -> C) -> or A B -> C.
  Hypothesis
    or_elim_redl :
    forall (A B C:Prop) (f:A -> C) (g:B -> C) (a:A),
      f a = or_elim A B C f g (or_introl A B a).
  Hypothesis
    or_elim_redr :
    forall (A B C:Prop) (f:A -> C) (g:B -> C) (b:B),
      g b = or_elim A B C f g (or_intror A B b).
  Hypothesis
    or_dep_elim :
    forall (A B:Prop) (P:or A B -> Prop),
      (forall a:A, P (or_introl A B a)) ->
      (forall b:B, P (or_intror A B b)) -> forall b:or A B, P b.
  
  Hypothesis em : forall A:Prop, or A (~ A).
  Variable B : Prop.
  Variables b1 b2 : B.
  
  (** [p2b] and [b2p] form a retract if [~b1=b2] *)

  Definition p2b A := or_elim A (~ A) B (fun _ => b1) (fun _ => b2) (em A).
  Definition b2p b := b1 = b.

  Lemma p2p1 : forall A:Prop, A -> b2p (p2b A).
  Proof.
    unfold p2b in |- *; intro A; apply or_dep_elim with (b := em A);
      unfold b2p in |- *; intros.
    apply (or_elim_redl A (~ A) B (fun _ => b1) (fun _ => b2)).
    destruct (b H).
  Qed.

  Lemma p2p2 : b1 <> b2 -> forall A:Prop, b2p (p2b A) -> A.
  Proof.
    intro not_eq_b1_b2.
    unfold p2b in |- *; intro A; apply or_dep_elim with (b := em A);
      unfold b2p in |- *; intros.
    assumption.
    destruct not_eq_b1_b2.
    rewrite <- (or_elim_redr A (~ A) B (fun _ => b1) (fun _ => b2)) in H.
    assumption.
  Qed.

  (** Using excluded-middle a second time, we get proof-irrelevance *)

  Theorem proof_irrelevance_cc : b1 = b2.
  Proof.
    refine (or_elim _ _ _ _ _ (em (b1 = b2))); intro H.
    trivial.
    apply (paradox B p2b b2p (p2p2 H) p2p1).
  Qed.

End Proof_irrelevance_EM_CC.

(** Remark: Hurkens' paradox still holds with a retract from the
    _negative_ fragment of [Prop] into [bool], hence weak classical
    logic, i.e. [forall A, ~A\/~~A], is enough for deriving
    proof-irrelevance.
*)

(************************************************************************)
(** ** CIC |- excluded-middle -> proof-irrelevance               *)

(**
    Since, dependent elimination is derivable in the Calculus of
    Inductive Constructions (CCI), we get proof-irrelevance from classical
    logic in the CCI.
*)

Section Proof_irrelevance_CCI.

  Hypothesis em : forall A:Prop, A \/ ~ A.
  
  Definition or_elim_redl (A B C:Prop) (f:A -> C) (g:B -> C) 
    (a:A) : f a = or_ind f g (or_introl B a) := refl_equal (f a).
  Definition or_elim_redr (A B C:Prop) (f:A -> C) (g:B -> C) 
    (b:B) : g b = or_ind f g (or_intror A b) := refl_equal (g b).
  Scheme or_indd := Induction for or Sort Prop.
  
  Theorem proof_irrelevance_cci : forall (B:Prop) (b1 b2:B), b1 = b2.
  Proof.
    exact (proof_irrelevance_cc or or_introl or_intror or_ind or_elim_redl
      or_elim_redr or_indd em).
  Qed.

End Proof_irrelevance_CCI.

(** Remark: in the Set-impredicative CCI, Hurkens' paradox still holds with
    [bool] in [Set] and since [~true=false] for [true] and [false]
    in [bool] from [Set], we get the inconsistency of
    [em : forall A:Prop, {A}+{~A}] in the Set-impredicative CCI.
*)

(** * Weak classical axioms *)

(** We show the following increasing in the strength of axioms:
 - weak excluded-middle
 - right distributivity of implication over disjunction and G�del-Dummett axiom
 - independence of general premises and drinker's paradox
 - excluded-middle
*)

(** ** Weak excluded-middle *)

(** The weak classical logic based on [~~A \/ ~A] is referred to with
    name KC in {[ChagrovZakharyaschev97]]

   [[ChagrovZakharyaschev97]] Alexander Chagrov and Michael
   Zakharyaschev, "Modal Logic", Clarendon Press, 1997.
*)

Definition weak_excluded_middle :=
  forall A:Prop, ~~A \/ ~A.

(** The interest in the equivalent variant
    [weak_generalized_excluded_middle] is that it holds even in logic
    without a primitive [False] connective (like G�del-Dummett axiom) *)

Definition weak_generalized_excluded_middle := 
  forall A B:Prop, ((A -> B) -> B) \/ (A -> B).

(** ** G�del-Dummett axiom *)

(** [(A->B) \/ (B->A)] is studied in [[Dummett59]] and is based on [[G�del33]].

    [[Dummett59]] Michael A. E. Dummett. "A Propositional Calculus
    with a Denumerable Matrix", In the Journal of Symbolic Logic, Vol
    24 No. 2(1959), pp 97-103.

    [[G�del33]] Kurt G�del. "Zum intuitionistischen Aussagenkalk�l",
    Ergeb. Math. Koll. 4 (1933), pp. 34-38.
 *)

Definition GodelDummett := forall A B:Prop, (A -> B) \/ (B -> A).

Lemma excluded_middle_Godel_Dummett : excluded_middle -> GodelDummett.
Proof.
  intros EM A B. destruct (EM B) as [HB|HnotB].
  left; intros _; exact HB.
  right; intros HB; destruct (HnotB HB).
Qed.

(** [(A->B) \/ (B->A)] is equivalent to [(C -> A\/B) -> (C->A) \/ (C->B)]
    (proof from [[Dummett59]]) *)

Definition RightDistributivityImplicationOverDisjunction :=
  forall A B C:Prop, (C -> A\/B) -> (C->A) \/ (C->B).

Lemma Godel_Dummett_iff_right_distr_implication_over_disjunction :
  GodelDummett <-> RightDistributivityImplicationOverDisjunction.
Proof.
  split.
    intros GD A B C HCAB.
    destruct (GD B A) as [HBA|HAB]; [left|right]; intro HC; 
      destruct (HCAB HC) as [HA|HB]; [ | apply HBA | apply HAB | ]; assumption.
    intros Distr A B.
    destruct (Distr A B (A\/B)) as [HABA|HABB].
      intro HAB; exact HAB.
      right; intro HB; apply HABA; right; assumption.
      left; intro HA; apply HABB; left; assumption.
Qed.

(** [(A->B) \/ (B->A)] is stronger than the weak excluded middle *)

Lemma Godel_Dummett_weak_excluded_middle : 
  GodelDummett -> weak_excluded_middle.
Proof.
  intros GD A. destruct (GD (~A) A) as [HnotAA|HAnotA].
    left; intro HnotA; apply (HnotA (HnotAA HnotA)).
    right; intro HA; apply (HAnotA HA HA).
Qed.

(** ** Independence of general premises and drinker's paradox *)

(** Independence of general premises is the unconstrained, non
    constructive, version of the Independence of Premises as
    considered in [[Troelstra73]].

    It is a generalization to predicate logic of the right
    distributivity of implication over disjunction (hence of
    G�del-Dummett axiom) whose own constructive form (obtained by a
    restricting the third formula to be negative) is called
    Kreisel-Putnam principle [[KreiselPutnam57]].

    [[KreiselPutnam57]], Georg Kreisel and Hilary Putnam. "Eine
    Unableitsbarkeitsbeweismethode f�r den intuitionistischen
    Aussagenkalk�l". Archiv f�r Mathematische Logik und
    Graundlagenforschung, 3:74- 78, 1957.

    [[Troelstra73]], Anne Troelstra, editor. Metamathematical
    Investigation of Intuitionistic Arithmetic and Analysis, volume
    344 of Lecture Notes in Mathematics, Springer-Verlag, 1973.
*)

Notation Local "'inhabited' A" := A (at level 10, only parsing).

Definition IndependenceOfGeneralPremises :=
  forall (A:Type) (P:A -> Prop) (Q:Prop),
    inhabited A -> (Q -> exists x, P x) -> exists x, Q -> P x.

Lemma
  independence_general_premises_right_distr_implication_over_disjunction :
  IndependenceOfGeneralPremises -> RightDistributivityImplicationOverDisjunction.
Proof.
  intros IP A B C HCAB.
  destruct (IP bool (fun b => if b then A else B) C true) as ([|],H).
    intro HC; destruct (HCAB HC); [exists true|exists false]; assumption.
    left; assumption.
    right; assumption.
Qed.

Lemma independence_general_premises_Godel_Dummett :
  IndependenceOfGeneralPremises -> GodelDummett.
Proof.
  destruct Godel_Dummett_iff_right_distr_implication_over_disjunction.
  auto using independence_general_premises_right_distr_implication_over_disjunction.
Qed.

(** Independence of general premises is equivalent to the drinker's paradox *)

Definition DrinkerParadox :=
  forall (A:Type) (P:A -> Prop), 
    inhabited A -> exists x, (exists x, P x) -> P x.

Lemma independence_general_premises_drinker : 
  IndependenceOfGeneralPremises <-> DrinkerParadox.
Proof.
  split.
    intros IP A P InhA; apply (IP A P (exists x, P x) InhA); intro Hx; exact Hx.
    intros Drinker A P Q InhA H; destruct (Drinker A P InhA) as (x,Hx).
      exists x; intro HQ; apply (Hx (H HQ)).
Qed.

(** Independence of general premises is weaker than (generalized) 
    excluded middle

Remark: generalized excluded middle is preferred here to avoid relying on
the "ex falso quodlibet" property (i.e. [False -> forall A, A])
*)

Definition generalized_excluded_middle := 
  forall A B:Prop, A \/ (A -> B).

Lemma excluded_middle_independence_general_premises :
  generalized_excluded_middle -> DrinkerParadox.
Proof.
  intros GEM A P x0.
  destruct (GEM (exists x, P x) (P x0)) as [(x,Hx)|Hnot].
    exists x; intro; exact Hx.
    exists x0; exact Hnot.
Qed.
 
