(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** This file formalizes Berardi's paradox which says that in
   the calculus of constructions, excluded middle (EM) and axiom of
   choice (AC) implie proof irrelevenace (PI).
   Here, the axiom of choice is not necessary because of the use
   of inductive types.
<<
@article{Barbanera-Berardi:JFP96,
   author    = {F. Barbanera and S. Berardi},
   title     = {Proof-irrelevance out of Excluded-middle and Choice
                in the Calculus of Constructions},
   journal   = {Journal of Functional Programming},
   year      = {1996},
   volume    = {6},
   number    = {3},
   pages     = {519-525}
}
>> *)

Set Implicit Arguments.

Section Berardis_paradox.

(** Excluded middle *)
Hypothesis EM : (P:Prop) P \/ ~P.

(** Conditional on any proposition. *)
Definition IFProp := [P,B:Prop][e1,e2:P]
  Cases (EM B) of
    (or_introl _) => e1
  | (or_intror _) => e2
  end.

(** Axiom of choice applied to disjunction.
    Provable in Coq because of dependent elimination. *)
Lemma AC_IF : (P,B:Prop)(e1,e2:P)(Q:P->Prop)
  ( B -> (Q e1))->
  (~B -> (Q e2))->
  (Q (IFProp B e1 e2)).
Proof.
Intros P B e1 e2 Q p1 p2.
Unfold IFProp.
Case (EM B); Assumption.
Qed.


(** We assume a type with two elements. They play the role of booleans.
    The main theorem under the current assumptions is that [T=F] *)
Variable Bool: Prop.
Variable T: Bool.
Variable F: Bool.

(** The powerset operator *)
Definition pow [P:Prop] :=P->Bool.


(** A piece of theory about retracts *)
Section Retracts.

Variable A,B: Prop.

Record retract : Prop := {
    i: A->B;
    j: B->A;
    inv: (a:A)(j (i a))==a
  }.

Record retract_cond : Prop := {
    i2: A->B;
    j2: B->A;
    inv2: retract -> (a:A)(j2 (i2 a))==a
  }.


(** The dependent elimination above implies the axiom of choice: *)
Lemma AC: (r:retract_cond) retract -> (a:A)((j2 r) ((i2 r) a))==a.
Proof.
Intros r.
Case r; Simpl.
Trivial.
Qed.

End Retracts.

(** This lemma is basically a commutation of implication and existential
    quantification:  (EX x | A -> P(x))  <=> (A -> EX x | P(x))
    which is provable in classical logic ( => is already provable in
    intuitionnistic logic). *)

Lemma L1 : (A,B:Prop)(retract_cond (pow A) (pow B)).
Proof.
Intros A B.
Elim (EM (retract (pow A) (pow B))).
Intros (f0, g0, e).
Exists f0 g0.
Trivial.

Intros hf.
Exists ([x:(pow A); y:B]F) ([x:(pow B); y:A]F).
Intros; Elim hf; Auto.
Qed.


(** The paradoxical set *)
Definition U := (P:Prop)(pow P).

(** Bijection between [U] and [(pow U)] *)
Definition f : U -> (pow U) :=
  [u](u U).

Definition g : (pow U) -> U :=
  [h,X]
    let lX = (j2 (L1 X U)) in
    let rU = (i2 (L1 U U)) in
    (lX (rU h)).

(** We deduce that the powerset of [U] is a retract of [U].
    This lemma is stated in Berardi's article, but is not used
    afterwards. *)
Lemma retract_pow_U_U : (retract (pow U) U).
Proof.
Exists g f.
Intro a.
Unfold f g; Simpl.
Apply AC.
Exists ([x:(pow U)]x) ([x:(pow U)]x).
Trivial.
Qed.

(** Encoding of Russel's paradox *)

(** The boolean negation. *)
Definition Not_b := [b:Bool](IFProp b==T F T).

(** the set of elements not belonging to itself *)
Definition R : U := (g ([u:U](Not_b (u U u)))).


Lemma not_has_fixpoint : (R R)==(Not_b (R R)).
Proof.
Unfold 1 R.
Unfold g.
Rewrite AC with r:=(L1 U U) a:=[u:U](Not_b (u U u)).
Trivial.
Exists ([x:(pow U)]x) ([x:(pow U)]x); Trivial.
Qed.


Theorem classical_proof_irrelevence : T==F.
Proof.
Generalize not_has_fixpoint.
Unfold Not_b.
Apply AC_IF.
Intros is_true is_false.
Elim is_true; Elim is_false; Trivial.

Intros not_true is_true.
Elim not_true; Trivial.
Qed.

End Berardis_paradox.
