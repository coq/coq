(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(*i i*)

Require Import NBase.

Module Homomorphism (NAxiomsMod1 NAxiomsMod2 : NAxiomsSig).

Module NBasePropMod2 := NBasePropFunct NAxiomsMod2.

Notation Local N1 := NAxiomsMod1.N.
Notation Local N2 := NAxiomsMod2.N.
Notation Local Eq1 := NAxiomsMod1.Neq.
Notation Local Eq2 := NAxiomsMod2.Neq.
Notation Local O1 := NAxiomsMod1.N0.
Notation Local O2 := NAxiomsMod2.N0.
Notation Local S1 := NAxiomsMod1.S.
Notation Local S2 := NAxiomsMod2.S.
Notation Local "n == m" := (Eq2 n m) (at level 70, no associativity).

Definition homomorphism (f : N1 -> N2) : Prop :=
  f O1 == O2 /\ forall n : N1, f (S1 n) == S2 (f n).

Definition natural_isomorphism : N1 -> N2 :=
  NAxiomsMod1.recursion O2 (fun (n : N1) (p : N2) => S2 p).

Add Morphism natural_isomorphism with signature Eq1 ==> Eq2 as natural_isomorphism_wd.
Proof.
unfold natural_isomorphism.
intros n m Eqxy.
apply NAxiomsMod1.recursion_wd with (Aeq := Eq2).
reflexivity.
unfold fun2_eq. intros _ _ _ y' y'' H. now apply NBasePropMod2.succ_wd.
assumption.
Qed.

Theorem natural_isomorphism_0 : natural_isomorphism O1 == O2.
Proof.
unfold natural_isomorphism; now rewrite NAxiomsMod1.recursion_0.
Qed.

Theorem natural_isomorphism_succ :
  forall n : N1, natural_isomorphism (S1 n) == S2 (natural_isomorphism n).
Proof.
unfold natural_isomorphism.
intro n. now rewrite (@NAxiomsMod1.recursion_succ N2 NAxiomsMod2.Neq);
[| unfold fun2_wd; intros; apply NBasePropMod2.succ_wd |].
Qed.

Theorem hom_nat_iso : homomorphism natural_isomorphism.
Proof.
unfold homomorphism, natural_isomorphism; split;
[exact natural_isomorphism_0 | exact natural_isomorphism_succ].
Qed.

End Homomorphism.

Module Inverse (NAxiomsMod1 NAxiomsMod2 : NAxiomsSig).

Module Import NBasePropMod1 := NBasePropFunct NAxiomsMod1.
(* This makes the tactic induct available. Since it is taken from
(NBasePropFunct NAxiomsMod1), it refers to induction on N1. *)

Module Hom12 := Homomorphism NAxiomsMod1 NAxiomsMod2.
Module Hom21 := Homomorphism NAxiomsMod2 NAxiomsMod1.

Notation Local N1 := NAxiomsMod1.N.
Notation Local N2 := NAxiomsMod2.N.
Notation Local h12 := Hom12.natural_isomorphism.
Notation Local h21 := Hom21.natural_isomorphism.

Notation Local "n == m" := (NAxiomsMod1.Neq n m) (at level 70, no associativity).

Lemma inverse_nat_iso : forall n : N1, h21 (h12 n) == n.
Proof.
induct n.
now rewrite Hom12.natural_isomorphism_0, Hom21.natural_isomorphism_0.
intros n IH.
now rewrite Hom12.natural_isomorphism_succ, Hom21.natural_isomorphism_succ, IH.
Qed.

End Inverse.

Module Isomorphism (NAxiomsMod1 NAxiomsMod2 : NAxiomsSig).

Module Hom12 := Homomorphism NAxiomsMod1 NAxiomsMod2.
Module Hom21 := Homomorphism NAxiomsMod2 NAxiomsMod1.

Module Inverse12 := Inverse NAxiomsMod1 NAxiomsMod2.
Module Inverse21 := Inverse NAxiomsMod2 NAxiomsMod1.

Notation Local N1 := NAxiomsMod1.N.
Notation Local N2 := NAxiomsMod2.N.
Notation Local Eq1 := NAxiomsMod1.Neq.
Notation Local Eq2 := NAxiomsMod2.Neq.
Notation Local h12 := Hom12.natural_isomorphism.
Notation Local h21 := Hom21.natural_isomorphism.

Definition isomorphism (f1 : N1 -> N2) (f2 : N2 -> N1) : Prop :=
  Hom12.homomorphism f1 /\ Hom21.homomorphism f2 /\
  forall n : N1, Eq1 (f2 (f1 n)) n /\
  forall n : N2, Eq2 (f1 (f2 n)) n.

Theorem iso_nat_iso : isomorphism h12 h21.
Proof.
unfold isomorphism.
split. apply Hom12.hom_nat_iso.
split. apply Hom21.hom_nat_iso.
split. apply Inverse12.inverse_nat_iso.
apply Inverse21.inverse_nat_iso.
Qed.

End Isomorphism.

