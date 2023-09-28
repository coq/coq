(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Some facts and definitions about propositional and predicate extensionality

Table of contents

1. Definitions

2. Relations between the following extensionality principles

   - Proposition extensionality
   - Predicate extensionality
   - Propositional functional extensionality
   - Provable-proposition extensionality
   - Refutable-proposition extensionality
   - Extensional proposition representatives
   - Extensional predicate representatives
   - Extensional propositional function representatives

2.1 Predicate extensionality <-> Proposition extensionality + Propositional functional extensionality

2.2 Propositional extensionality -> Provable propositional extensionality

2.3 Propositional extensionality -> Refutable propositional extensionality

3. Propositional extensionality and proof-irrelevance

3.1. CC |- prop. ext. + A inhabited -> (A = A->A) -> A has fixpoint

3.2. CC |- prop. ext. + dep elim on bool -> proof-irrelevance

3.3. CIC |- prop. ext. -> proof-irrelevance

*)

Set Implicit Arguments.

(************************************************************************)
(** * Relations between different forms of propositional extensionality *)

(**********************************************************************)
(** * Definitions *)

(** Propositional extensionality *)

Local Notation PropositionalExtensionality :=
  (forall A B : Prop, (A <-> B) -> A = B).

(** Provable-proposition extensionality *)

Local Notation ProvablePropositionExtensionality :=
  (forall A:Prop, A -> A = True).

(** Refutable-proposition extensionality *)

Local Notation RefutablePropositionExtensionality :=
  (forall A:Prop, ~A -> A = False).

(** Predicate extensionality *)

Local Notation PredicateExtensionality :=
  (forall (A:Type) (P Q : A -> Prop), (forall x, P x <-> Q x) -> P = Q).

(** Propositional functional extensionality *)

Local Notation PropositionalFunctionalExtensionality :=
  (forall (A:Type) (P Q : A -> Prop), (forall x, P x = Q x) -> P = Q).

(**********************************************************************)
(** * Propositional and predicate extensionality                      *)

(**********************************************************************)
(** ** Predicate extensionality <-> Propositional extensionality + Propositional functional extensionality *)

Lemma PredExt_imp_PropExt : PredicateExtensionality -> PropositionalExtensionality.
Proof.
  intros Ext A B Equiv. 
  change A with ((fun _ => A) I).
  now rewrite Ext with (P := fun _ : True =>A) (Q := fun _ => B).
Qed.

Lemma PredExt_imp_PropFunExt : PredicateExtensionality -> PropositionalFunctionalExtensionality.
Proof.
  intros Ext A P Q Eq. apply Ext. intros x. now rewrite (Eq x).
Qed.

Lemma PropExt_and_PropFunExt_imp_PredExt :
  PropositionalExtensionality -> PropositionalFunctionalExtensionality -> PredicateExtensionality.
Proof.
  intros Ext FunExt A P Q Equiv.
  apply FunExt. intros x. now apply Ext.
Qed.

Theorem PropExt_and_PropFunExt_iff_PredExt :
  PropositionalExtensionality /\ PropositionalFunctionalExtensionality <-> PredicateExtensionality.
Proof.
  firstorder using PredExt_imp_PropExt, PredExt_imp_PropFunExt, PropExt_and_PropFunExt_imp_PredExt.
Qed.

(**********************************************************************)
(** ** Propositional extensionality and provable proposition extensionality *)

Lemma PropExt_imp_ProvPropExt : PropositionalExtensionality -> ProvablePropositionExtensionality.
Proof.
  intros Ext A Ha; apply Ext; split; trivial.
Qed.

(**********************************************************************)
(** ** Propositional extensionality and refutable proposition extensionality *)

Lemma PropExt_imp_RefutPropExt : PropositionalExtensionality -> RefutablePropositionExtensionality.
Proof.
  intros Ext A Ha; apply Ext; split; easy.
Qed.


(************************************************************************)
(** * Propositional extensionality and proof-irrelevance *)

(************************************************************************)
(** ** CC |- prop ext + A inhabited -> (A = A->A) -> A has fixpoint *)

(** We successively show that:

   [PropositionalExtensionality]
     implies equality of [A] and [A->A] for inhabited [A], which
     implies the existence of a (trivial) retract from [A->A] to [A]
        (just take the identity), which
     implies the existence of a fixpoint operator in [A]
        (e.g. take the Y combinator of lambda-calculus)

*)

Unset Implicit Arguments.

Local Notation inhabited A := A (only parsing).

Lemma prop_ext_A_eq_A_imp_A :
  PropositionalExtensionality -> forall A:Prop, inhabited A -> (A -> A) = A.
Proof.
  intros Ext A a.
  apply (Ext (A -> A) A); split; [ exact (fun _ => a) | exact (fun _ _ => a) ].
Qed.

Require Import LawvereFixpoint.

Lemma prop_ext_retract_A_A_imp_A :
  PropositionalExtensionality -> forall A:Prop, inhabited A -> Retract A (A -> A).
Proof.
  intros Ext A a.
  rewrite (prop_ext_A_eq_A_imp_A Ext A a).
  exists (fun x:A => x), (fun x:A => x).
  reflexivity.
Qed.

Lemma ext_prop_fixpoint :
  PropositionalExtensionality -> forall A:Prop, inhabited A -> HasFix A.
Proof.
  intros Ext A a.
  case (prop_ext_retract_A_A_imp_A Ext A a); intros g1 (g2, g1_o_g2).
  exists (fun f => (fun x:A => f (g1 x x)) (g2 (fun x => f (g1 x x)))).
  intro f.
  pattern (g1 (g2 (fun x:A => f (g1 x x)))) at 1.
  rewrite (g1_o_g2 (fun x:A => f (g1 x x))).
  reflexivity.
Qed.

(** Remark: [PropositionalExtensionality] can be replaced in lemma [ext_prop_fixpoint]
    by the weakest property [provable_PropositionalExtensionality].
*)

(************************************************************************)
(** ** CC |- prop_ext /\ dep elim on bool -> proof-irrelevance  *)

(** [proof_irrelevance] asserts equality of all proofs of a given formula *)
Definition ProofIrrelevance := forall (P:Prop) (p1 p2:P), p1 = p2.

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

  Lemma aux : PropositionalExtensionality -> bool_dep_induction -> true = false.
  Proof.
    intros Ext Ind.
    case (ext_prop_fixpoint Ext bool true); intros G Gfix.
    set (neg := fun b:bool => bool_elim bool false true b).
    generalize (eq_refl (G neg)).
    pattern (G neg) at 1.
    apply Ind with (b := G neg); intro Heq.
    - rewrite (bool_elim_redl bool false true).
      change (true = neg true); rewrite Heq; apply Gfix.
    - rewrite (bool_elim_redr bool false true).
      change (neg false = false); rewrite Heq; symmetry ;
        apply Gfix.
  Qed.

  Lemma ext_prop_dep_proof_irrel_gen :
    PropositionalExtensionality -> bool_dep_induction -> ProofIrrelevance.
  Proof.
    intros Ext Ind A a1 a2.
    set (f := fun b:bool => bool_elim A a1 a2 b).
    rewrite (bool_elim_redl A a1 a2).
    change (f true = a2).
    rewrite (bool_elim_redr A a1 a2).
    change (f true = f false).
    rewrite (aux Ext Ind).
    reflexivity.
  Qed.

End Proof_irrelevance_gen.

(** In the pure Calculus of Constructions, we can define the boolean
    proposition [bool = forall C:Prop, C->C->C] but we cannot prove that it has at
    most 2 elements.
*)

Section Proof_irrelevance_Prop_Ext_CC.

  Definition BoolP := forall C:Prop, C -> C -> C.
  Definition TrueP : BoolP := fun C c1 c2 => c1.
  Definition FalseP : BoolP := fun C c1 c2 => c2.
  Definition BoolP_elim C c1 c2 (b:BoolP) := b C c1 c2.
  Definition BoolP_elim_redl (C:Prop) (c1 c2:C) :
    c1 = BoolP_elim C c1 c2 TrueP := eq_refl c1.
  Definition BoolP_elim_redr (C:Prop) (c1 c2:C) :
    c2 = BoolP_elim C c1 c2 FalseP := eq_refl c2.

  Definition BoolP_dep_induction :=
    forall P:BoolP -> Prop, P TrueP -> P FalseP -> forall b:BoolP, P b.

  Lemma ext_prop_dep_proof_irrel_cc :
    PropositionalExtensionality -> BoolP_dep_induction -> ProofIrrelevance.
  Proof.
    exact (ext_prop_dep_proof_irrel_gen BoolP TrueP FalseP BoolP_elim BoolP_elim_redl
      BoolP_elim_redr).
  Qed.

End Proof_irrelevance_Prop_Ext_CC.

(** Remark: [PropositionalExtensionality] can be replaced in lemma
    [ext_prop_dep_proof_irrel_gen] by the weakest property
    [provable_PropositionalExtensionality].
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
    c1 = boolP_ind C c1 c2 trueP := eq_refl c1.
  Definition boolP_elim_redr (C:Prop) (c1 c2:C) :
    c2 = boolP_ind C c1 c2 falseP := eq_refl c2.
  Scheme boolP_indd := Induction for boolP Sort Prop.

  Lemma ext_prop_dep_proof_irrel_cic : PropositionalExtensionality -> ProofIrrelevance.
  Proof.
    exact (fun pe =>
      ext_prop_dep_proof_irrel_gen boolP trueP falseP boolP_ind boolP_elim_redl
      boolP_elim_redr pe boolP_indd).
  Qed.

End Proof_irrelevance_CIC.
