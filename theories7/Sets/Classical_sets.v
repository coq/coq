(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(****************************************************************************)
(*                                                                          *)
(*                         Naive Set Theory in Coq                          *)
(*                                                                          *)
(*                     INRIA                        INRIA                   *)
(*              Rocquencourt                        Sophia-Antipolis        *)
(*                                                                          *)
(*                                 Coq V6.1                                 *)
(*									    *)
(*			         Gilles Kahn 				    *)
(*				 Gerard Huet				    *)
(*									    *)
(*									    *)
(*                                                                          *)
(* Acknowledgments: This work was started in July 1993 by F. Prost. Thanks  *)
(* to the Newton Institute for providing an exceptional work environment    *)
(* in Summer 1995. Several developments by E. Ledinot were an inspiration.  *)
(****************************************************************************)

(*i $Id$ i*)

Require Export Ensembles.
Require Export Constructive_sets.
Require Export Classical_Type.

(* Hints Unfold  not . *)

Section Ensembles_classical.
Variable U: Type.

Lemma not_included_empty_Inhabited: 
  (A: (Ensemble  U)) ~ (Included U A (Empty_set U)) -> (Inhabited U A).
Proof.
Intros A NI.
Elim (not_all_ex_not U [x:U]~(In U A x)).
Intros x H; Apply Inhabited_intro with x.
Apply NNPP; Auto with sets.
Red; Intro.
Apply NI; Red.
Intros x H'; Elim (H x); Trivial with sets.
Qed.
Hints Resolve not_included_empty_Inhabited.

Lemma not_empty_Inhabited: 
  (A: (Ensemble  U)) ~ A == (Empty_set U) -> (Inhabited U A).
Proof.
Intros; Apply not_included_empty_Inhabited.
Red; Auto with sets.
Qed.

Lemma Inhabited_Setminus :
(X, Y: (Ensemble U)) (Included U X Y) -> ~ (Included U Y X) ->
       (Inhabited U (Setminus U Y X)).
Proof.
Intros X Y I NI. 
Elim (not_all_ex_not U [x:U](In U Y x)->(In U X x) NI).
Intros x YX.
Apply Inhabited_intro with x.
Apply Setminus_intro.
Apply not_imply_elim with (In U X x); Trivial with sets.
Auto with sets.
Qed.
Hints Resolve Inhabited_Setminus.

Lemma Strict_super_set_contains_new_element:
  (X, Y: (Ensemble U)) (Included U X Y) -> ~ X == Y ->
   (Inhabited U (Setminus U Y X)).
Proof.
Auto 7 with sets.
Qed.
Hints Resolve Strict_super_set_contains_new_element.

Lemma Subtract_intro:
  (A: (Ensemble U)) (x, y: U) (In U A y) -> ~ x == y ->
   (In U (Subtract U A x) y).
Proof.
Unfold 1 Subtract; Auto with sets.
Qed.
Hints Resolve Subtract_intro.

Lemma Subtract_inv:
  (A: (Ensemble U)) (x, y: U) (In U (Subtract U A x) y) ->
   (In U A y) /\ ~ x == y.
Proof.
Intros A x y H'; Elim H'; Auto with sets.
Qed.

Lemma Included_Strict_Included:
  (X, Y: (Ensemble U)) (Included U X Y) -> (Strict_Included U X Y) \/ X == Y.
Proof.
Intros X Y H'; Try Assumption.
Elim (classic X == Y); Auto with sets.
Qed.

Lemma Strict_Included_inv:
  (X, Y: (Ensemble U)) (Strict_Included U X Y) ->
   (Included U X Y) /\ (Inhabited U (Setminus U Y X)).
Proof.
Intros X Y H'; Red in H'.
Split; [Tauto | Idtac].
Elim H'; Intros H'0 H'1; Try Exact H'1; Clear H'.
Apply Strict_super_set_contains_new_element; Auto with sets.
Qed.

Lemma not_SIncl_empty: 
    (X: (Ensemble U)) ~ (Strict_Included U X (Empty_set U)).
Proof.
Intro X; Red; Intro H'; Try Exact H'.
LApply (Strict_Included_inv X (Empty_set U)); Auto with sets.
Intro H'0; Elim H'0; Intros H'1 H'2; Elim H'2; Clear H'0.
Intros x H'0; Elim H'0.
Intro H'3; Elim H'3.
Qed.

Lemma Complement_Complement :
  (A: (Ensemble U)) (Complement U (Complement U A)) == A.
Proof.
Unfold Complement; Intros; Apply Extensionality_Ensembles; Auto with sets.
Red; Split; Auto with sets.
Red; Intros; Apply NNPP; Auto with sets.
Qed.

End Ensembles_classical.

Hints Resolve Strict_super_set_contains_new_element Subtract_intro 
	not_SIncl_empty : sets v62.
