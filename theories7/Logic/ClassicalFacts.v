(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Some facts and definitions about classical logic *)

(** [prop_degeneracy] (also referred as propositional completeness) *)
(*  asserts (up to consistency) that there are only two distinct formulas *)
Definition prop_degeneracy := (A:Prop) A==True \/ A==False.

(** [prop_extensionality] asserts equivalent formulas are equal *)
Definition prop_extensionality := (A,B:Prop) (A<->B) -> A==B.

(** [excluded_middle] asserts we can reason by case on the truth *)
(*  or falsity of any formula *)
Definition excluded_middle := (A:Prop) A \/ ~A.

(** [proof_irrelevance] asserts equality of all proofs of a given formula *)
Definition proof_irrelevance := (A:Prop)(a1,a2:A) a1==a2.

(** We show [prop_degeneracy <-> (prop_extensionality /\ excluded_middle)] *)

Lemma prop_degen_ext : prop_degeneracy -> prop_extensionality.
Proof.
Intros H A B (Hab,Hba).
NewDestruct (H A); NewDestruct (H B).
  Rewrite H1; Exact H0.
  Absurd B.
    Rewrite H1; Exact [H]H.
    Apply Hab; Rewrite H0; Exact I.
  Absurd A.
    Rewrite H0; Exact [H]H.
    Apply Hba; Rewrite H1; Exact I.
  Rewrite H1; Exact H0.
Qed.

Lemma prop_degen_em : prop_degeneracy -> excluded_middle.
Proof.
Intros H A.
NewDestruct (H A).
  Left; Rewrite H0; Exact I.
  Right; Rewrite H0; Exact [x]x.
Qed.

Lemma prop_ext_em_degen :
   prop_extensionality -> excluded_middle -> prop_degeneracy.
Proof.
Intros Ext EM A.
NewDestruct (EM A).
  Left; Apply (Ext A True); Split; [Exact [_]I | Exact [_]H].
  Right; Apply (Ext A False); Split; [Exact H | Apply False_ind].
Qed.

(** We successively show that:

   [prop_extensionality]
     implies equality of [A] and [A->A] for inhabited [A], which 
     implies the existence of a (trivial) retract from [A->A] to [A]
        (just take the identity), which
     implies the existence of a fixpoint operator in [A]
        (e.g. take the Y combinator of lambda-calculus)
*)

Definition inhabited [A:Prop] := A.

Lemma prop_ext_A_eq_A_imp_A :
  prop_extensionality->(A:Prop)(inhabited A)->(A->A)==A.
Proof.
Intros Ext A a.
Apply (Ext A->A A); Split; [ Exact [_]a | Exact [_;_]a ].
Qed.

Record retract [A,B:Prop] : Prop := {
  f1: A->B;
  f2: B->A;
  f1_o_f2: (x:B)(f1 (f2 x))==x
}.

Lemma prop_ext_retract_A_A_imp_A :
  prop_extensionality->(A:Prop)(inhabited A)->(retract A A->A).
Proof.
Intros Ext A a.
Rewrite -> (prop_ext_A_eq_A_imp_A Ext A a).
Exists [x:A]x [x:A]x.
Reflexivity.
Qed.

Record has_fixpoint [A:Prop] : Prop := {
  F : (A->A)->A;
  fix : (f:A->A)(F f)==(f (F f))
}.

Lemma ext_prop_fixpoint :
  prop_extensionality->(A:Prop)(inhabited A)->(has_fixpoint A).
Proof.
Intros Ext A a.
Case (prop_ext_retract_A_A_imp_A Ext A a); Intros g1 g2 g1_o_g2.
Exists [f]([x:A](f (g1 x x)) (g2 [x](f (g1 x x)))).
Intro f.
Pattern 1 (g1 (g2 [x:A](f (g1 x x)))).
Rewrite (g1_o_g2 [x:A](f (g1 x x))).
Reflexivity.
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
Hypothesis bool_elim : (C:Prop)C->C->bool->C.
Hypothesis bool_elim_redl : (C:Prop)(c1,c2:C)c1==(bool_elim C c1 c2 true).
Hypothesis bool_elim_redr : (C:Prop)(c1,c2:C)c2==(bool_elim C c1 c2 false).
Local bool_dep_induction := (P:bool->Prop)(P true)->(P false)->(b:bool)(P b).

Lemma aux : prop_extensionality -> bool_dep_induction -> true==false.
Proof.
Intros Ext Ind.
Case (ext_prop_fixpoint Ext bool true); Intros G Gfix.
Pose neg := [b:bool](bool_elim bool false true b).
Generalize (refl_eqT ? (G neg)).
Pattern 1 (G neg).
Apply Ind with b:=(G neg); Intro Heq.
Rewrite (bool_elim_redl bool false true).
Change true==(neg true); Rewrite -> Heq; Apply Gfix.
Rewrite (bool_elim_redr bool false true).
Change (neg false)==false; Rewrite -> Heq; Symmetry; Apply Gfix.
Qed.

Lemma ext_prop_dep_proof_irrel_gen :
  prop_extensionality -> bool_dep_induction -> proof_irrelevance.
Proof.
Intros Ext Ind A a1 a2.
Pose f := [b:bool](bool_elim A a1 a2 b).
Rewrite (bool_elim_redl A a1 a2).
Change (f true)==a2.
Rewrite (bool_elim_redr A a1 a2).
Change (f true)==(f false).
Rewrite (aux Ext Ind).
Reflexivity.
Qed.

End Proof_irrelevance_gen.

(** In the pure Calculus of Constructions, we can define the boolean
    proposition bool = (C:Prop)C->C->C but we cannot prove that it has at
    most 2 elements.
*)

Section Proof_irrelevance_CC.

Definition BoolP  := (C:Prop)C->C->C.
Definition TrueP  := [C][c1,c2]c1 : BoolP.
Definition FalseP := [C][c1,c2]c2 : BoolP.
Definition BoolP_elim := [C][c1,c2][b:BoolP](b C c1 c2).
Definition BoolP_elim_redl : (C:Prop)(c1,c2:C)c1==(BoolP_elim C c1 c2 TrueP)
  := [C;c1,c2](refl_eqT C c1).
Definition BoolP_elim_redr : (C:Prop)(c1,c2:C)c2==(BoolP_elim C c1 c2 FalseP)
  := [C;c1,c2](refl_eqT C c2).

Definition BoolP_dep_induction := 
 (P:BoolP->Prop)(P TrueP)->(P FalseP)->(b:BoolP)(P b).

Lemma ext_prop_dep_proof_irrel_cc :
  prop_extensionality -> BoolP_dep_induction -> proof_irrelevance.
Proof (ext_prop_dep_proof_irrel_gen BoolP TrueP FalseP BoolP_elim
         BoolP_elim_redl BoolP_elim_redr).

End Proof_irrelevance_CC.

(** In the Calculus of Inductive Constructions, inductively defined booleans
    enjoy dependent case analysis, hence directly proof-irrelevance from
    propositional extensionality.
*)

Section Proof_irrelevance_CIC.

Inductive boolP : Prop := trueP : boolP | falseP : boolP.
Definition boolP_elim_redl : (C:Prop)(c1,c2:C)c1==(boolP_ind C c1 c2 trueP)
  := [C;c1,c2](refl_eqT C c1).
Definition boolP_elim_redr : (C:Prop)(c1,c2:C)c2==(boolP_ind C c1 c2 falseP)
  := [C;c1,c2](refl_eqT C c2).
Scheme boolP_indd := Induction for boolP Sort Prop.

Lemma ext_prop_dep_proof_irrel_cic : prop_extensionality -> proof_irrelevance.
Proof [pe](ext_prop_dep_proof_irrel_gen boolP trueP falseP boolP_ind
         boolP_elim_redl boolP_elim_redr pe boolP_indd).

End Proof_irrelevance_CIC.

(** Can we state proof irrelevance from propositional degeneracy
  (i.e. propositional extensionality + excluded middle) without
  dependent case analysis ?

  Conjecture: it seems possible to build a model of CC interpreting
  all non-empty types by the set of all lambda-terms. Such a model would
  satisfy propositional degeneracy without satisfying proof-irrelevance
  (nor dependent case analysis). This would imply that the previous
  results cannot be refined.
*)
