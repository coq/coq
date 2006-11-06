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

Require Import Relation_Definitions.
Require Export Relations_1.
Set Implicit Arguments.

Definition Complement (U:Type) (R:relation U) : relation U :=
  fun x y:U => ~ R x y.

Theorem Rsym_imp_notRsym :
 forall (U:Type) (R:relation U), symmetric R -> symmetric (Complement R).
Proof.
unfold symmetric, Complement in |- *.
intros U R H' x y H'0; red in |- *; intro H'1; apply H'0; auto with sets.
Qed.

Theorem Equiv_from_preorder :
 forall (U:Type) (R:relation U),
   preorder R -> equivalence (fun x y:U => R x y /\ R y x).
Proof.
intros U R H'; elim H'; intros H'0 H'1.
apply Definition_of_equivalence.
red in H'0; auto 10 with sets.
2: red in |- *; intros x y h; elim h; intros H'3 H'4; auto 10 with sets.
red in H'1; red in |- *; auto 10 with sets.
intros x y z h; elim h; intros H'3 H'4; clear h.
intro h; elim h; intros H'5 H'6; clear h.
split; apply H'1 with y; auto 10 with sets.
Qed.
Hint Resolve Equiv_from_preorder.

Theorem Equiv_from_order :
 forall (U:Type) (R:relation U),
   order R -> equivalence (fun x y:U => R x y /\ R y x).
Proof.
intros U R H'; elim H'; auto 10 with sets.
Qed.
Hint Resolve Equiv_from_order.

Theorem contains_is_preorder :
 forall U:Type, preorder (contains (U:=U)).
Proof.
auto 10 with sets.
Qed.
Hint Resolve contains_is_preorder.

Theorem inclusion_is_preorder :
 forall U:Type, preorder (inclusion (A:=U) (B:=U)).
Proof.
auto 10 with sets.
Qed.
Hint Resolve inclusion_is_preorder.

Theorem same_relation_is_equivalence :
 forall U:Type, equivalence (A:=relation U) (same_relation U).
Proof.
unfold Relation_Definitions.same_relation; auto.
Qed.
Hint Resolve same_relation_is_equivalence.

Theorem cong_reflexive_same_relation :
 forall (U:Type) (R R':relation U),
   same_relation U R R' -> reflexive R -> reflexive R'.
Proof.
unfold Relation_Definitions.same_relation in |- *; intuition.
Qed.

Theorem cong_symmetric_same_relation :
 forall (U:Type) (R R':relation U),
   same_relation U R R' -> symmetric R -> symmetric R'.
Proof.
  compute; intros; destruct H; auto.
Qed.

Theorem cong_antisymmetric_same_relation :
 forall (U:Type) (R R':relation U),
   same_relation U R R' -> antisymmetric R -> antisymmetric R'.
Proof.
  compute; intros; destruct H; auto.
Qed.

Theorem cong_transitive_same_relation :
 forall (U:Type) (R R':relation U),
   same_relation U R R' -> transitive R -> transitive R'.
Proof.
  compute; intros; destruct H; eauto.
Qed.
