(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(* R. Diaconescu [Diaconescu] showed that the Axiom of Choice in Set Theory
   entails Excluded-Middle; S. Lacas and B. Werner [LacasWerner]
   adapted the proof to show that the axiom of choice in equivalence
   classes entails Excluded-Middle in Type Theory.

   This is an adaptatation of the proof by Hugo Herbelin to show that
   the relational form of the Axiom of Choice + Extensionality for
   predicates entails Excluded-Middle

   [Diaconescu] R. Diaconescu, Axiom of Choice and Complementation, in
   Proceedings of AMS, vol 51, pp 176-178, 1975.

   [LacasWerner] S. Lacas, B Werner, Which Choices imply the excluded middle?,
   preprint, 1999.

*)

Section PredExt_GuardRelChoice_imp_EM.

(* The axiom of extensionality for predicates *)

Definition PredicateExtensionality :=
   (P,Q:bool->Prop)((b:bool)(P b)<->(Q b))->P==Q.

(* From predicate extensionality we get propositional extensionality
   hence proof-irrelevance *)

Require ClassicalFacts.

Variable pred_extensionality : PredicateExtensionality.
  
Lemma prop_ext : (A,B:Prop) (A<->B) -> A==B.
Proof.
  Intros A B H.
  Change ([_]A true)==([_]B true).
  Rewrite pred_extensionality with P:=[_:bool]A Q:=[_:bool]B.
    Reflexivity.
    Intros _; Exact H.
Qed.

Lemma proof_irrel : (A:Prop)(a1,a2:A) a1==a2.
Proof.
  Apply (ext_prop_dep_proof_irrel_cic prop_ext).
Qed.

(* From proof-irrelevance and relational choice, we get guarded
   relational choice *)

Require ChoiceFacts.

Variable rel_choice : RelationalChoice.

Lemma guarded_rel_choice :
  (A:Type)(B:Type)(P:A->Prop)(R:A->B->Prop)
  ((x:A)(P x)->(EX y:B|(R x y)))->
    (EXT R':A->B->Prop | 
      ((x:A)(P x)->(EX y:B|(R x y)/\(R' x y)/\ ((y':B)(R' x y') -> y=y')))).
Proof.
  Exact
    (rel_choice_and_proof_irrel_imp_guarded_rel_choice rel_choice proof_irrel).
Qed.

(* The form of choice we need: there is a functional relation which chooses
   an element in any non empty subset of bool *)

Require Bool.

Lemma AC :
  (EXT R:(bool->Prop)->bool->Prop |
     (P:bool->Prop)(EX b : bool | (P b))->
        (EX b : bool | (P b) /\ (R P b) /\ ((b':bool)(R P b')->b=b'))).
Proof.
  Apply guarded_rel_choice with
    P:= [Q:bool->Prop](EX y | (Q y)) R:=[Q:bool->Prop;y:bool](Q y).
  Exact [_;H]H.
Qed.

(* The proof of the excluded middle *)
(* Remark: P could have been in Set or Type *)

Theorem pred_ext_and_rel_choice_imp_EM : (P:Prop)P\/~P.
Proof.
Intro P.

(* first we exhibit the choice functional relation R *)
NewDestruct AC as [R H].

Pose class_of_true := [b]b=true\/P.
Pose class_of_false := [b]b=false\/P.

(* the actual "decision": is (R class_of_true) = true or false? *)
NewDestruct (H class_of_true) as [b0 [H0 [H0' H0'']]].
Exists true; Left; Reflexivity.
NewDestruct H0.

(* the actual "decision": is (R class_of_false) = true or false? *)
NewDestruct (H class_of_false) as [b1 [H1 [H1' H1'']]].
Exists false; Left; Reflexivity.
NewDestruct H1.

(* case where P is false: (R class_of_true)=true /\ (R class_of_false)=false *)
Right.
Intro HP.
Assert Hequiv:(b:bool)(class_of_true b)<->(class_of_false b).
Intro b; Split.
Unfold class_of_false; Right; Assumption.
Unfold class_of_true; Right; Assumption.
Assert Heq:class_of_true==class_of_false.
Apply pred_extensionality with 1:=Hequiv.
Apply diff_true_false.
Rewrite <- H0.
Rewrite <- H1.
Rewrite <- H0''. Reflexivity.
Rewrite Heq.
Assumption.

(* cases where P is true *)
Left; Assumption.
Left; Assumption.

Qed.

End PredExt_GuardRelChoice_imp_EM.
