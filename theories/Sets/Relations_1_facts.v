(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
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

Require Export Relations_1.

Definition Complement (U:Type) (R:Relation U) : Relation U :=
  fun x y:U => ~ R x y.

Theorem Rsym_imp_notRsym :
 forall (U:Type) (R:Relation U),
   Symmetric U R -> Symmetric U (Complement U R).
Proof.
unfold Symmetric, Complement.
intros U R H' x y H'0; red; intro H'1; apply H'0; auto with sets.
Qed.

Theorem Equiv_from_preorder :
 forall (U:Type) (R:Relation U),
   Preorder U R -> Equivalence U (fun x y:U => R x y /\ R y x).
Proof.
intros U R H'; elim H'; intros H'0 H'1.
apply Definition_of_equivalence.
red in H'0; auto 10 with sets.
2: red; intros x y h; elim h; intros H'3 H'4; auto 10 with sets.
red in H'1; red; auto 10 with sets.
intros x y z h; elim h; intros H'3 H'4; clear h.
intro h; elim h; intros H'5 H'6; clear h.
split; apply H'1 with y; auto 10 with sets.
Qed.
Hint Resolve Equiv_from_preorder.

Theorem Equiv_from_order :
 forall (U:Type) (R:Relation U),
   Order U R -> Equivalence U (fun x y:U => R x y /\ R y x).
Proof.
intros U R H'; elim H'; auto 10 with sets.
Qed.
Hint Resolve Equiv_from_order.

Theorem contains_is_preorder :
 forall U:Type, Preorder (Relation U) (contains U).
Proof.
auto 10 with sets.
Qed.
Hint Resolve contains_is_preorder.

Theorem same_relation_is_equivalence :
 forall U:Type, Equivalence (Relation U) (same_relation U).
Proof.
unfold same_relation at 1; auto 10 with sets.
Qed.
Hint Resolve same_relation_is_equivalence.

Theorem cong_reflexive_same_relation :
 forall (U:Type) (R R':Relation U),
   same_relation U R R' -> Reflexive U R -> Reflexive U R'.
Proof.
unfold same_relation; intuition.
Qed.

Theorem cong_symmetric_same_relation :
 forall (U:Type) (R R':Relation U),
   same_relation U R R' -> Symmetric U R -> Symmetric U R'.
Proof.
  compute; intros; elim H; intros; clear H;
   apply (H3 y x (H0 x y (H2 x y H1))).
(*Intuition.*)
Qed.

Theorem cong_antisymmetric_same_relation :
 forall (U:Type) (R R':Relation U),
   same_relation U R R' -> Antisymmetric U R -> Antisymmetric U R'.
Proof.
  compute; intros; elim H; intros; clear H;
   apply (H0 x y (H3 x y H1) (H3 y x H2)).
(*Intuition.*)
Qed.

Theorem cong_transitive_same_relation :
 forall (U:Type) (R R':Relation U),
   same_relation U R R' -> Transitive U R -> Transitive U R'.
Proof.
intros U R R' H' H'0; red.
elim H'.
intros H'1 H'2 x y z H'3 H'4; apply H'2.
apply H'0 with y; auto with sets.
Qed.
