(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

Require BinInt.
Require Zeven.
Require Zorder.
Require Zcompare.
Require ZArith_dec.
Require Zsyntax.
Require Sumbool.

(** The decidability of equality and order relations over
    type [Z] give some boolean functions with the adequate specification. *)

Definition Z_lt_ge_bool := [x,y:Z](bool_of_sumbool (Z_lt_ge_dec x y)).
Definition Z_ge_lt_bool := [x,y:Z](bool_of_sumbool (Z_ge_lt_dec x y)).

Definition Z_le_gt_bool := [x,y:Z](bool_of_sumbool (Z_le_gt_dec x y)).
Definition Z_gt_le_bool := [x,y:Z](bool_of_sumbool (Z_gt_le_dec x y)).

Definition Z_eq_bool := [x,y:Z](bool_of_sumbool (Z_eq_dec x y)).
Definition Z_noteq_bool := [x,y:Z](bool_of_sumbool (Z_noteq_dec x y)).

Definition Zeven_odd_bool := [x:Z](bool_of_sumbool (Zeven_odd_dec x)).

(**********************************************************************)
(** Boolean comparisons of binary integers *)

Definition Zle_bool := 
  [x,y:Z]Cases `x ?= y` of SUPERIEUR => false | _ => true end.
Definition Zge_bool := 
  [x,y:Z]Cases `x ?= y` of INFERIEUR => false | _ => true end.
Definition Zlt_bool := 
  [x,y:Z]Cases `x ?= y` of INFERIEUR => true | _ => false end.
Definition Zgt_bool := 
  [x,y:Z]Cases ` x ?= y` of SUPERIEUR => true | _ => false end.
Definition Zeq_bool := 
  [x,y:Z]Cases `x ?= y` of EGAL => true | _ => false end.
Definition Zneq_bool := 
  [x,y:Z]Cases `x ?= y` of EGAL => false | _ => true end.

Lemma Zle_cases : (x,y:Z)if (Zle_bool x y) then `x<=y` else `x>y`.
Proof.
Intros x y; Unfold Zle_bool Zle Zgt.
Case (Zcompare x y); Auto; Discriminate.
Qed.

Lemma Zlt_cases : (x,y:Z)if (Zlt_bool x y) then `x<y` else `x>=y`.
Proof.
Intros x y; Unfold Zlt_bool Zlt Zge.
Case (Zcompare x y); Auto; Discriminate.
Qed.

Lemma Zge_cases : (x,y:Z)if (Zge_bool x y) then `x>=y` else `x<y`.
Proof.
Intros x y; Unfold Zge_bool Zge Zlt.
Case (Zcompare x y); Auto; Discriminate.
Qed.

Lemma Zgt_cases : (x,y:Z)if (Zgt_bool x y) then `x>y` else `x<=y`.
Proof.
Intros x y; Unfold Zgt_bool Zgt Zle.
Case (Zcompare x y); Auto; Discriminate.
Qed.

(** Lemmas on [Zle_bool] used in contrib/graphs *)

Lemma Zle_bool_imp_le : (x,y:Z) (Zle_bool x y)=true -> (Zle x y).
Proof.
  Unfold Zle_bool Zle. Intros x y. Unfold not. 
  Case (Zcompare x y); Intros; Discriminate.
Qed.

Lemma Zle_imp_le_bool : (x,y:Z) (Zle x y) -> (Zle_bool x y)=true.
Proof.
  Unfold Zle Zle_bool. Intros x y. Case (Zcompare x y); Trivial. Intro. Elim (H (refl_equal ? ?)).
Qed.

Lemma Zle_bool_refl : (x:Z) (Zle_bool x x)=true.
Proof.
  Intro. Apply Zle_imp_le_bool. Apply Zle_refl. Reflexivity.
Qed.

Lemma Zle_bool_antisym : (x,y:Z) (Zle_bool x y)=true -> (Zle_bool y x)=true -> x=y.
Proof.
  Intros. Apply Zle_antisym. Apply Zle_bool_imp_le. Assumption.
  Apply Zle_bool_imp_le. Assumption.
Qed.

Lemma Zle_bool_trans : (x,y,z:Z) (Zle_bool x y)=true -> (Zle_bool y z)=true -> (Zle_bool x z)=true.
Proof.
  Intros x y z; Intros. Apply Zle_imp_le_bool. Apply Zle_trans with m:=y. Apply Zle_bool_imp_le. Assumption.
  Apply Zle_bool_imp_le. Assumption.
Qed.

Definition Zle_bool_total : (x,y:Z) {(Zle_bool x y)=true}+{(Zle_bool y x)=true}.
Proof.
  Intros x y; Intros. Unfold Zle_bool. Cut (Zcompare x y)=SUPERIEUR<->(Zcompare y x)=INFERIEUR.
  Case (Zcompare x y). Left . Reflexivity.
  Left . Reflexivity.
  Right . Rewrite (proj1 ? ? H (refl_equal ? ?)). Reflexivity.
  Apply Zcompare_ANTISYM.
Defined.

Lemma Zle_bool_plus_mono : (x,y,z,t:Z) (Zle_bool x y)=true -> (Zle_bool z t)=true ->
                                (Zle_bool (Zplus x z) (Zplus y t))=true.
Proof.
  Intros. Apply Zle_imp_le_bool. Apply Zle_plus_plus. Apply Zle_bool_imp_le. Assumption.
  Apply Zle_bool_imp_le. Assumption.
Qed.

Lemma Zone_pos : (Zle_bool `1` `0`)=false.
Proof.
  Reflexivity.
Qed.

Lemma Zone_min_pos : (x:Z) (Zle_bool x `0`)=false -> (Zle_bool `1` x)=true.
Proof.
  Intros x; Intros. Apply Zle_imp_le_bool. Change (Zle (Zs ZERO) x). Apply Zgt_le_S. Generalize H.
  Unfold Zle_bool Zgt. Case (Zcompare x ZERO). Intro H0. Discriminate H0.
  Intro H0. Discriminate H0.
  Reflexivity.
Qed.


 Lemma Zle_is_le_bool : (x,y:Z) (Zle x y) <-> (Zle_bool x y)=true.
  Proof.
    Intros. Split. Intro. Apply Zle_imp_le_bool. Assumption.
    Intro. Apply Zle_bool_imp_le. Assumption.
  Qed.

  Lemma Zge_is_le_bool : (x,y:Z) (Zge x y) <-> (Zle_bool y x)=true.
  Proof.
    Intros. Split. Intro. Apply Zle_imp_le_bool. Apply Zge_le. Assumption.
    Intro. Apply Zle_ge. Apply Zle_bool_imp_le. Assumption.
  Qed.

  Lemma Zlt_is_le_bool : (x,y:Z) (Zlt x y) <-> (Zle_bool x `y-1`)=true.
  Proof.
    Intros x y. Split. Intro. Apply Zle_imp_le_bool. Apply Zlt_n_Sm_le. Rewrite (Zs_pred y) in H.
    Assumption.
    Intro. Rewrite (Zs_pred y). Apply Zle_lt_n_Sm. Apply Zle_bool_imp_le. Assumption.
  Qed.

  Lemma Zgt_is_le_bool : (x,y:Z) (Zgt x y) <-> (Zle_bool y `x-1`)=true.
  Proof.
    Intros x y. Apply iff_trans with `y < x`. Split. Exact (Zgt_lt x y).
    Exact (Zlt_gt y x).
    Exact (Zlt_is_le_bool y x).
  Qed.

