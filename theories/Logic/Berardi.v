(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file formalizes Berardi's paradox which says that in
   the calculus of constructions, excluded middle (EM) and axiom of
   choice (AC) imply proof irrelevance (PI).
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
Hypothesis EM : forall P:Prop, P \/ ~ P.

(** Conditional on any proposition. *)
Definition IFProp (P B:Prop) (e1 e2:P) :=
  match EM B with
  | or_introl _ => e1
  | or_intror _ => e2
  end.

(** Axiom of choice applied to disjunction.
    Provable in Coq because of dependent elimination. *)
Lemma AC_IF :
 forall (P B:Prop) (e1 e2:P) (Q:P -> Prop),
   (B -> Q e1) -> (~ B -> Q e2) -> Q (IFProp B e1 e2).
Proof.
intros P B e1 e2 Q p1 p2.
unfold IFProp.
case (EM B); assumption.
Qed.


(** We assume a type with two elements. They play the role of booleans.
    The main theorem under the current assumptions is that [T=F] *)
Variable Bool : Prop.
Variable T : Bool.
Variable F : Bool.

(** The powerset operator *)
Definition pow (P:Prop) := P -> Bool.


(** A piece of theory about retracts *)
Section Retracts.

Variables A B : Prop.

Record retract : Prop :=
  {i : A -> B; j : B -> A; inv : forall a:A, j (i a) = a}.
Record retract_cond : Prop :=
  {i2 : A -> B; j2 : B -> A; inv2 : retract -> forall a:A, j2 (i2 a) = a}.

(** The dependent elimination above implies the axiom of choice: *)

Lemma AC : forall r:retract_cond, retract -> forall a:A, r.(j2) (r.(i2) a) = a.
Proof. intros r. exact r.(inv2). Qed.

End Retracts.

(** This lemma is basically a commutation of implication and existential
    quantification:  (EX x | A -> P(x))  <=> (A -> EX x | P(x))
    which is provable in classical logic ( => is already provable in
    intuitionistic logic). *)

Lemma L1 : forall A B:Prop, retract_cond (pow A) (pow B).
Proof.
intros A B.
destruct (EM (retract (pow A) (pow B))) as [(f0,g0,e) | hf].
  exists f0 g0; trivial.
  exists (fun (x:pow A) (y:B) => F) (fun (x:pow B) (y:A) => F); intros;
    destruct hf; auto.
Qed.


(** The paradoxical set *)
Definition U := forall P:Prop, pow P.

(** Bijection between [U] and [(pow U)] *)
Definition f (u:U) : pow U := u U.

Definition g (h:pow U) : U :=
  fun X => let lX := j2 (L1 X U) in let rU := i2 (L1 U U) in lX (rU h).

(** We deduce that the powerset of [U] is a retract of [U].
    This lemma is stated in Berardi's article, but is not used
    afterwards. *)
Lemma retract_pow_U_U : retract (pow U) U.
Proof.
exists g f.
intro a.
unfold f, g; simpl.
apply AC. 
exists (fun x:pow U => x) (fun x:pow U => x).
trivial.
Qed.

(** Encoding of Russel's paradox *)

(** The boolean negation. *)
Definition Not_b (b:Bool) := IFProp (b = T) F T.

(** the set of elements not belonging to itself *)
Definition R : U := g (fun u:U => Not_b (u U u)).


Lemma not_has_fixpoint : R R = Not_b (R R).
Proof.
unfold R at 1.
unfold g.
rewrite AC.
trivial.
exists (fun x:pow U => x) (fun x:pow U => x).
trivial.
Qed.


Theorem classical_proof_irrelevance : T = F.
Proof.
generalize not_has_fixpoint.
unfold Not_b.
apply AC_IF.
intros is_true is_false.
elim is_true; elim is_false; trivial.

intros not_true is_true.
elim not_true; trivial.
Qed.


Notation classical_proof_irrelevence := classical_proof_irrelevance (compat "8.8").

End Berardis_paradox.
