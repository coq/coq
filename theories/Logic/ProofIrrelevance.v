(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This is a proof in the pure Calculus of Construction that
    classical logic in Prop + dependent elimination of disjunction entails
    proof-irrelevance.

    Since, dependent elimination is derivable in the Calculus of
    Inductive Constructions (CCI), we get proof-irrelevance from classical
    logic in the CCI.

    Reference:

    - [Coquand] T. Coquand, "Metamathematical Investigations of a
      Calculus of Constructions", Proceedings of Logic in Computer Science
      (LICS'90), 1990.

    Proof skeleton: classical logic + dependent elimination of
    disjunction + discrimination of proofs implies the existence of a
    retract from [Prop] into [bool], hence inconsistency by encoding any
    paradox of system U- (e.g. Hurkens' paradox).
*)

Require Import Hurkens.

Section Proof_irrelevance_CC.

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

End Proof_irrelevance_CC.


(** The Calculus of Inductive Constructions (CCI) enjoys dependent
    elimination, hence classical logic in CCI entails proof-irrelevance.
*)

Section Proof_irrelevance_CCI.

Hypothesis em : forall A:Prop, A \/ ~ A.

Definition or_elim_redl (A B C:Prop) (f:A -> C) (g:B -> C) 
  (a:A) : f a = or_ind f g (or_introl B a) := refl_equal (f a).
Definition or_elim_redr (A B C:Prop) (f:A -> C) (g:B -> C) 
  (b:B) : g b = or_ind f g (or_intror A b) := refl_equal (g b).
Scheme or_indd := Induction for or Sort Prop.

Theorem proof_irrelevance_cci : forall (B:Prop) (b1 b2:B), b1 = b2.
Proof
  proof_irrelevance_cc or or_introl or_intror or_ind or_elim_redl
    or_elim_redr or_indd em.

End Proof_irrelevance_CCI.

(** Remark: in CCI, [bool] can be taken in [Set] as well in the
    paradox and since [~true=false] for [true] and [false] in
    [bool], we get the inconsistency of [em : forall A:Prop, {A}+{~A}] in CCI
*)
