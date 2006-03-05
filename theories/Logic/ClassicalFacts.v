(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** ** Some facts and definitions about classical logic *)

(** [prop_degeneracy] (also referred as propositional completeness) *)
(*  asserts (up to consistency) that there are only two distinct formulas *)
Definition prop_degeneracy := forall A:Prop, A = True \/ A = False.

(** [prop_extensionality] asserts equivalent formulas are equal *)
Definition prop_extensionality := forall A B:Prop, (A <-> B) -> A = B.

(** [excluded_middle] asserts we can reason by case on the truth *)
(*  or falsity of any formula *)
Definition excluded_middle := forall A:Prop, A \/ ~ A.

(** [proof_irrelevance] asserts equality of all proofs of a given formula *)
Definition proof_irrelevance := forall (A:Prop) (a1 a2:A), a1 = a2.

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

(** Assume we have booleans with the property that there is at most 2
    booleans (which is equivalent to dependent case analysis). Consider
    the fixpoint of the negation function: it is either true or false by
    dependent case analysis, but also the opposite by fixpoint. Hence
    proof-irrelevance.

    We then map bool proof-irrelevance to all propositions.
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

Section Proof_irrelevance_CC.

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
Proof
  ext_prop_dep_proof_irrel_gen BoolP TrueP FalseP BoolP_elim BoolP_elim_redl
    BoolP_elim_redr.

End Proof_irrelevance_CC.

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
Proof
  fun pe =>
    ext_prop_dep_proof_irrel_gen boolP trueP falseP boolP_ind boolP_elim_redl
      boolP_elim_redr pe boolP_indd.

End Proof_irrelevance_CIC.

(** Can we state proof irrelevance from propositional degeneracy
  (i.e. propositional extensionality + excluded middle) without
  dependent case analysis ?

  Berardi [Berardi] built a model of CC interpreting inhabited
  types by the set of all untyped lambda-terms. This model satisfies
  propositional degeneracy without satisfying proof-irrelevance (nor
  dependent case analysis). This implies that the previous results
  cannot be refined.

  [Berardi] Stefano Berardi, "Type dependence and constructive mathematics",
  Ph. D. thesis, Dipartimento Matematica, Università di Torino, 1990.
*)

(** *** Standard facts about weak classical axioms *)

(** **** Weak excluded-middle *)

(** The weak classical logic based on [~~A \/ ~A] is refered to with
    name KC in {[ChagrovZakharyaschev97]]

   [[ChagrovZakharyaschev97]] Alexander Chagrov and Michael
   Zakharyaschev, "Modal Logic", Clarendon Press, 1997.
*)

Definition weak_excluded_middle :=
  forall A:Prop, ~~A \/ ~A.

(** The interest in the equivalent variant
    [weak_generalized_excluded_middle] is that it holds even in logic
    without a primitive [False] connective (like Gödel-Dummett axiom) *)

Definition weak_generalized_excluded_middle := 
  forall A B:Prop, ((A -> B) -> B) \/ (A -> B).

(** **** Gödel-Dummett axiom *)

(** [(A->B) \/ (B->A)] is studied in [[Dummett59]] and is based on [[Gödel33]].

    [[Dummett59]] Michael A. E. Dummett. "A Propositional Calculus
    with a Denumerable Matrix", In the Journal of Symbolic Logic, Vol
    24 No. 2(1959), pp 97-103.

    [[Gödel33]] Kurt Gödel. "Zum intuitionistischen Aussagenkalkül",
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

(** **** Independence of general premises and drinker's paradox *)

(** Independence of general premises is the unconstrained, non
    constructive, version of the Independence of Premises as
    considered in [[Troelstra73]].

    It is a generalization to predicate logic of the right
    distributivity of implication over disjunction (hence of
    Gödel-Dummett axiom) whose own constructive form (obtained by a
    restricting the third formula to be negative) is called
    Kreisel-Putnam principle [[KreiselPutnam57]].

    [[KreiselPutnam57]], Georg Kreisel and Hilary Putnam. "Eine
    Unableitsbarkeitsbeweismethode für den intuitionistischen
    Aussagenkalkül". Archiv für Mathematische Logik und
    Graundlagenforschung, 3:74- 78, 1957.

    [[Troelstra73]], Anne Troelstra, editor. Metamathematical
    Investigation of Intuitionistic Arithmetic and Analysis, volume
    344 of Lecture Notes in Mathematics, Springer-Verlag, 1973.
*)


Notation "'inhabited' A" := A (at level 10, only parsing).

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
