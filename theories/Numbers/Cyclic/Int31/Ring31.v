(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Int31 numbers defines Z/(2^31)Z, and can hence be equipped
      with a ring structure and a ring tactic *)

Require Import Int31 Cyclic31 CyclicAxioms.

Local Open Scope int31_scope.

(** Detection of constants *)

Ltac isInt31cst t :=
  match eval lazy delta [add31] in (t + 1)%int31 with
  | add31 _ _ => constr:false
  | _ => constr:true
  end.

Ltac Int31cst t :=
  match eval lazy delta [add31] in (t + 1)%int31 with
  | add31 _ _ => constr:NotConstant
  | _ => constr:t
  end.

(** The generic ring structure inferred from the Cyclic structure *)

Module Int31ring := CyclicRing Int31Cyclic.

(** Unlike in the generic [CyclicRing], we can use Leibniz here. *)

Lemma Int31_canonic : forall x y, to_Z x = to_Z y -> x = y.
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

Lemma Int31Ring : ring_theory 0 1 add31 mul31 sub31 opp31 Logic.eq.
Proof.
exact (ring_theory_switch_eq _ _ _ _ _ _ _ _ _ Int31_canonic Int31ring.CyclicRing).
Qed.

Lemma eq31_correct : forall x y, eq31 x y = true -> x=y.
Proof. now apply spec_eq. Qed.

Add Ring Int31Ring : Int31Ring
 (decidable eq31_correct,
  constants [Int31cst]).

Section TestRing.
Let test : forall x y, 1 + x*y + x*x + 1 = 1*1 + 1 + y*x + 1*x*x.
intros. ring.
Qed.
End TestRing.

