(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i 	$Id$	 i*)

(** Properties of decidable propositions *)

Definition decidable (P:Prop) := P \/ ~ P.

Theorem dec_not_not : forall P:Prop, decidable P -> (~ P -> False) -> P.
unfold decidable in |- *; tauto. 
Qed.

Theorem dec_True : decidable True.
unfold decidable in |- *; auto.
Qed.

Theorem dec_False : decidable False.
unfold decidable, not in |- *; auto.
Qed.

Theorem dec_or :
 forall A B:Prop, decidable A -> decidable B -> decidable (A \/ B).
unfold decidable in |- *; tauto. 
Qed.

Theorem dec_and :
 forall A B:Prop, decidable A -> decidable B -> decidable (A /\ B).
unfold decidable in |- *; tauto. 
Qed.

Theorem dec_not : forall A:Prop, decidable A -> decidable (~ A).
unfold decidable in |- *; tauto. 
Qed.

Theorem dec_imp :
 forall A B:Prop, decidable A -> decidable B -> decidable (A -> B).
unfold decidable in |- *; tauto. 
Qed.

Theorem not_not : forall P:Prop, decidable P -> ~ ~ P -> P.
unfold decidable in |- *; tauto. Qed.

Theorem not_or : forall A B:Prop, ~ (A \/ B) -> ~ A /\ ~ B.
tauto. Qed.

Theorem not_and : forall A B:Prop, decidable A -> ~ (A /\ B) -> ~ A \/ ~ B.
unfold decidable in |- *; tauto. Qed.

Theorem not_imp : forall A B:Prop, decidable A -> ~ (A -> B) -> A /\ ~ B.
unfold decidable in |- *; tauto.
Qed.

Theorem imp_simp : forall A B:Prop, decidable A -> (A -> B) -> ~ A \/ B.
unfold decidable in |- *; tauto.
Qed.
