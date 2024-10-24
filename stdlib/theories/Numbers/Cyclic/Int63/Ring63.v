(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Uint63 numbers defines Z/(2^63)Z, and can hence be equipped
      with a ring structure and a ring tactic *)

Require Import Cyclic63 CyclicAxioms.

Local Open Scope uint63_scope.

(** Detection of constants *)

Ltac isUint63cst t :=
  match eval lazy delta [add] in (t + 1)%uint63 with
  | add _ _ => constr:(false)
  | _ => constr:(true)
  end.

Ltac Uint63cst t :=
  match eval lazy delta [add] in (t + 1)%uint63 with
  | add _ _ => constr:(NotConstant)
  | _ => constr:(t)
  end.

(** The generic ring structure inferred from the Cyclic structure *)

Module Uint63ring := CyclicRing Uint63Cyclic.

(** Unlike in the generic [CyclicRing], we can use Leibniz here. *)

Lemma Uint63_canonic : forall x y, to_Z x = to_Z y -> x = y.
Proof to_Z_inj.

Lemma ring_theory_switch_eq :
 forall A (R R':A->A->Prop) zero one add mul sub opp,
  (forall x y : A, R x y -> R' x y) ->
  ring_theory zero one add mul sub opp R ->
  ring_theory zero one add mul sub opp R'.
Proof.
intros A R R' zero one add mul sub opp Impl Ring.
constructor; intros; apply Impl; apply Ring.
Qed.

Lemma Uint63Ring : ring_theory 0 1 add mul sub opp Logic.eq.
Proof.
exact (ring_theory_switch_eq _ _ _ _ _ _ _ _ _ Uint63_canonic Uint63ring.CyclicRing).
Qed.

Lemma eq31_correct : forall x y, eqb x y = true -> x=y.
Proof. now apply eqb_spec. Qed.

Add Ring Uint63Ring : Uint63Ring
 (decidable eq31_correct,
  constants [Uint63cst]).

Section TestRing.
Let test : forall x y, 1 + x*y + x*x + 1 = 1*1 + 1 + y*x + 1*x*x.
intros. ring.
Defined.
End TestRing.
