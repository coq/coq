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
  forall P Q:bool -> Prop, (forall b:bool, P b <-> Q b) -> P = Q.

(* From predicate extensionality we get propositional extensionality
   hence proof-irrelevance *)

Require Import ClassicalFacts.

Variable pred_extensionality : PredicateExtensionality.
  
Lemma prop_ext : forall A B:Prop, (A <-> B) -> A = B.
Proof.
  intros A B H.
  change ((fun _ => A) true = (fun _ => B) true) in |- *.
  rewrite
   pred_extensionality with (P := fun _:bool => A) (Q := fun _:bool => B).
    reflexivity.
    intros _; exact H.
Qed.

Lemma proof_irrel : forall (A:Prop) (a1 a2:A), a1 = a2.
Proof.
  apply (ext_prop_dep_proof_irrel_cic prop_ext).
Qed.

(* From proof-irrelevance and relational choice, we get guarded
   relational choice *)

Require Import ChoiceFacts.

Variable rel_choice : RelationalChoice.

Lemma guarded_rel_choice :
 forall (A B:Type) (P:A -> Prop) (R:A -> B -> Prop),
   (forall x:A, P x ->  exists y : B, R x y) ->
    exists R' : A -> B -> Prop,
     (forall x:A,
        P x ->
         exists y : B, R x y /\ R' x y /\ (forall y':B, R' x y' -> y = y')).
Proof.
  exact
   (rel_choice_and_proof_irrel_imp_guarded_rel_choice rel_choice proof_irrel).
Qed.

(* The form of choice we need: there is a functional relation which chooses
   an element in any non empty subset of bool *)

Require Import Bool.

Lemma AC :
  exists R : (bool -> Prop) -> bool -> Prop,
   (forall P:bool -> Prop,
      (exists b : bool, P b) ->
       exists b : bool, P b /\ R P b /\ (forall b':bool, R P b' -> b = b')).
Proof.
  apply guarded_rel_choice with
   (P := fun Q:bool -> Prop =>  exists y : _, Q y)
   (R := fun (Q:bool -> Prop) (y:bool) => Q y).
  exact (fun _ H => H).
Qed.

(* The proof of the excluded middle *)
(* Remark: P could have been in Set or Type *)

Theorem pred_ext_and_rel_choice_imp_EM : forall P:Prop, P \/ ~ P.
Proof.
intro P.

(* first we exhibit the choice functional relation R *)
destruct AC as [R H].

set (class_of_true := fun b => b = true \/ P).
set (class_of_false := fun b => b = false \/ P).

(* the actual "decision": is (R class_of_true) = true or false? *)
destruct (H class_of_true) as [b0 [H0 [H0' H0'']]].
exists true; left; reflexivity.
destruct H0.

(* the actual "decision": is (R class_of_false) = true or false? *)
destruct (H class_of_false) as [b1 [H1 [H1' H1'']]].
exists false; left; reflexivity.
destruct H1.

(* case where P is false: (R class_of_true)=true /\ (R class_of_false)=false *)
right.
intro HP.
assert (Hequiv : forall b:bool, class_of_true b <-> class_of_false b).
intro b; split.
unfold class_of_false in |- *; right; assumption.
unfold class_of_true in |- *; right; assumption.
assert (Heq : class_of_true = class_of_false).
apply pred_extensionality with (1 := Hequiv).
apply diff_true_false.
rewrite <- H0.
rewrite <- H1.
rewrite <- H0''. reflexivity.
rewrite Heq.
assumption.

(* cases where P is true *)
left; assumption.
left; assumption.

Qed.

End PredExt_GuardRelChoice_imp_EM.
