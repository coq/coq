(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* Instantiation of the Ring tactic for the binary integers of ZArith *)

Require Export ArithRing.
Require Export ZArith_base.
Require Eqdep_dec.

Definition Zeq := [x,y:Z]
  Cases `x ?= y ` of
    EGAL => true
  | _ => false
  end.

Lemma Zeq_prop : (x,y:Z)(Is_true (Zeq x y)) -> x==y.
  Intros x y H; Unfold Zeq in H.
  Apply Zcompare_EGAL_eq.
  NewDestruct (Zcompare x y); [Reflexivity | Contradiction | Contradiction ].
Save.

Definition ZTheory : (Ring_Theory Zplus Zmult `1` `0` Zopp Zeq).
  Split; Intros; Apply eq2eqT; EAuto with zarith.
  Apply eqT2eq; Apply Zeq_prop; Assumption.
Save.

(* NatConstants and NatTheory are defined in Ring_theory.v *)
Add Ring Z Zplus Zmult `1` `0` Zopp Zeq ZTheory [POS NEG ZERO xO xI xH].
