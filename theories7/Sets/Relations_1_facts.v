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

Require Export Relations_1.

Definition Complement : (U: Type) (Relation U) -> (Relation U) :=
   [U: Type] [R: (Relation U)] [x,y: U] ~ (R x y).

Theorem Rsym_imp_notRsym: (U: Type) (R: (Relation U)) (Symmetric U R) ->
            (Symmetric U (Complement U R)).
Proof.
Unfold Symmetric Complement.
Intros U R H' x y H'0; Red; Intro H'1; Apply H'0; Auto with sets.
Qed.

Theorem Equiv_from_preorder :
  (U: Type) (R: (Relation U)) (Preorder U R) ->
            (Equivalence U [x,y: U] (R x y) /\ (R y x)).
Proof.
Intros U R H'; Elim H'; Intros H'0 H'1.
Apply Definition_of_equivalence.
Red in H'0; Auto 10 with sets.
2:Red; Intros x y h; Elim h; Intros H'3 H'4; Auto 10 with sets.
Red in H'1; Red; Auto 10 with sets.
Intros x y z h; Elim h; Intros H'3 H'4; Clear h.
Intro h; Elim h; Intros H'5 H'6; Clear h.
Split; Apply H'1 with y; Auto 10 with sets.
Qed.
Hints Resolve Equiv_from_preorder.

Theorem Equiv_from_order :
  (U: Type) (R: (Relation U)) (Order U R) ->
            (Equivalence U [x,y: U] (R x y) /\ (R y x)).
Proof.
Intros U R H'; Elim H'; Auto 10 with sets.
Qed.
Hints Resolve Equiv_from_order.

Theorem contains_is_preorder :
  (U: Type) (Preorder (Relation U) (contains U)).
Proof.
Auto 10 with sets.
Qed.
Hints Resolve contains_is_preorder.

Theorem same_relation_is_equivalence :
  (U: Type) (Equivalence (Relation U) (same_relation U)).
Proof.
Unfold 1 same_relation; Auto 10 with sets.
Qed.
Hints Resolve same_relation_is_equivalence.

Theorem cong_reflexive_same_relation:
  (U:Type) (R, R':(Relation U)) (same_relation U R R') -> (Reflexive U R) ->
  (Reflexive U R').
Proof.
Unfold same_relation; Intuition.
Qed.

Theorem cong_symmetric_same_relation:
  (U:Type) (R, R':(Relation U)) (same_relation U R R') -> (Symmetric U R) ->
  (Symmetric U R').
Proof.
  Compute;Intros;Elim H;Intros;Clear H;Apply (H3 y x (H0 x y (H2 x y H1))).
(*Intuition.*)
Qed.

Theorem cong_antisymmetric_same_relation:
  (U:Type) (R, R':(Relation U)) (same_relation U R R') ->
           (Antisymmetric U R) -> (Antisymmetric U R').
Proof.
  Compute;Intros;Elim H;Intros;Clear H;Apply (H0 x y (H3 x y H1) (H3 y x H2)).
(*Intuition.*)
Qed.

Theorem cong_transitive_same_relation:
  (U:Type) (R, R':(Relation U)) (same_relation U R R') -> (Transitive U R) ->
  (Transitive U R').
Proof.
Intros U R R' H' H'0; Red.
Elim H'.
Intros H'1 H'2 x y z H'3 H'4; Apply H'2.
Apply H'0 with y; Auto with sets.
Qed.
