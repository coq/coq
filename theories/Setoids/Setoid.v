(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export Coq.Classes.SetoidTactics.

Export Morphisms.ProperNotations.

(** For backward compatibility *)

Definition Setoid_Theory := @Equivalence.
Definition Build_Setoid_Theory := @Build_Equivalence.

Definition Seq_refl A Aeq (s : Setoid_Theory A Aeq) : forall x:A, Aeq x x.
Proof.
  unfold Setoid_Theory in s. intros ; reflexivity.
Defined.

Definition Seq_sym A Aeq (s : Setoid_Theory A Aeq) : forall x y:A, Aeq x y -> Aeq y x.
Proof.
  unfold Setoid_Theory in s. intros ; symmetry ; assumption.
Defined.

Definition Seq_trans A Aeq (s : Setoid_Theory A Aeq) : forall x y z:A, Aeq x y -> Aeq y z -> Aeq x z.
Proof.
  unfold Setoid_Theory in s. intros ; transitivity y ; assumption.
Defined.

(** Some tactics for manipulating Setoid Theory not officially
    declared as Setoid. *)

Ltac trans_st x :=
  idtac "trans_st on Setoid_Theory is OBSOLETE";
  idtac "use transitivity on Equivalence instead";
  match goal with
    | H : Setoid_Theory _ ?eqA |- ?eqA _ _ =>
      apply (Seq_trans _ _ H) with x; auto
  end.

Ltac sym_st :=
  idtac "sym_st on Setoid_Theory is OBSOLETE";
  idtac "use symmetry on Equivalence instead";
  match goal with
    | H : Setoid_Theory _ ?eqA |- ?eqA _ _ =>
      apply (Seq_sym _ _ H); auto
  end.

Ltac refl_st :=
  idtac "refl_st on Setoid_Theory is OBSOLETE";
  idtac "use reflexivity on Equivalence instead";
  match goal with
    | H : Setoid_Theory _ ?eqA |- ?eqA _ _ =>
      apply (Seq_refl _ _ H); auto
  end.

Definition gen_st : forall A : Set, Setoid_Theory _ (@eq A).
Proof.
  constructor; congruence.
Qed.

