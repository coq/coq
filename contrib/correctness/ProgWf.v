(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

Require ZArith.
Require Export Wf_nat.

(* Well-founded relations on Z. *)

(* We define the following family of relations on ZxZ : 
 * 
 *      x (Zwf c) y   iff   c <= x < y
 *)

Definition Zwf := [c:Z][x,y:Z] `c <= x` /\ `c <= y` /\ `x < y`.


(* and we prove that (Zwf c) is well founded *)

Section wf_proof.

Variable c : Z.

(* The proof of well-foundness is classic : we do the proof by induction
 * on a measure in nat, which is here |x-c| *)

Local f := [z:Z](absolu (Zminus z c)).

Lemma Zwf_well_founded : (well_founded Z (Zwf c)).
Proof.
Apply well_founded_lt_compat with f:=f.
Unfold Zwf f.
Intros.
Apply absolu_lt.
Unfold Zminus. Split.
Apply Zle_left; Intuition.
Rewrite (Zplus_sym x `-c`). Rewrite (Zplus_sym y `-c`).
Apply Zlt_reg_l; Intuition.
Save.

End wf_proof.

Hints Resolve Zwf_well_founded : datatypes v62.


(* We also define the other family of relations :
 *
 *      x (Zwf_up c) y   iff   y < x <= c
 *)

Definition Zwf_up := [c:Z][x,y:Z] `y < x <= c`.

(* and we prove that (Zwf_up c) is well founded *)

Section wf_proof_up.

Variable c : Z.

(* The proof of well-foundness is classic : we do the proof by induction
 * on a measure in nat, which is here |c-x| *)

Local f := [z:Z](absolu (Zminus c z)).

Lemma Zwf_up_well_founded : (well_founded Z (Zwf_up c)).
Proof.
Apply well_founded_lt_compat with f:=f.
Unfold Zwf_up f.
Intros.
Apply absolu_lt.
Unfold Zminus. Split.
Apply Zle_left; Intuition.
Apply Zlt_reg_l; Unfold Zlt; Rewrite <- Zcompare_Zopp; Intuition.
Save.

End wf_proof_up.

Hints Resolve Zwf_up_well_founded : datatypes v62.
