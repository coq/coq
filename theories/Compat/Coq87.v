(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Compatibility file for making Coq act similar to Coq v8.7 *)

(* In 8.7, omega wasn't taking advantage of local abbreviations,
   see bug 148 and PR#768. For adjusting this flag, we're forced to
   first dynlink the omega plugin, but we should avoid doing a full
   "Require Omega", since it has some undesired effects (at least on hints)
   and breaks at least fiat-crypto. *)
Declare ML Module "omega_plugin".
Unset Omega UseLocalDefs.


Set Typeclasses Axioms Are Instances.

(** In Coq 8.7, [Bool.eqb] was manually defined, and had different
    judgmental behavior from the current definition of [Bool.bool_beq]
    which is given by [Scheme Equality].  We restore the old one by
    overriding it. *)
Require Coq.Bool.Bool.
Local Set Warnings Append "-masking-absolute-name".
Module Export Coq.
  Module Export Bool.
    Module Bool.
      Export Coq.Bool.Bool.
      Definition eqb (b1 b2:bool) : bool :=
        match b1, b2 with
        | true, true => true
        | true, false => false
        | false, true => false
        | false, false => true
        end.
      Lemma eqb_subst :
        forall (P:bool -> Prop) (b1 b2:bool), eqb b1 b2 = true -> P b1 -> P b2.
      Proof.
        destr_bool.
      Qed.

      Lemma eqb_reflx : forall b:bool, eqb b b = true.
      Proof.
        destr_bool.
      Qed.

      Lemma eqb_prop : forall a b:bool, eqb a b = true -> a = b.
      Proof.
        destr_bool.
      Qed.

      Lemma eqb_true_iff : forall a b:bool, eqb a b = true <-> a = b.
      Proof.
        destr_bool; intuition.
      Qed.

      Lemma eqb_false_iff : forall a b:bool, eqb a b = false <-> a <> b.
      Proof.
        destr_bool; intuition.
      Qed.

      Open Scope bool_scope.

      Lemma eqb_negb1 : forall b:bool, eqb (negb b) b = false.
      Proof.
        destr_bool.
      Qed.

      Lemma eqb_negb2 : forall b:bool, eqb b (negb b) = false.
      Proof.
        destr_bool.
      Qed.

      Lemma eqb_refl : forall x:bool, Is_true (eqb x x).
      Proof.
        destr_bool.
      Qed.

      Lemma eqb_eq : forall x y:bool, Is_true (eqb x y) -> x = y.
      Proof.
        destr_bool; tauto.
      Qed.
    End Bool.
  End Bool.
End Coq.
