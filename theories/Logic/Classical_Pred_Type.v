(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Classical Predicate Logic on Type *)

Require Import Classical_Prop.

Section Generic.
Variable U : Type.

(** de Morgan laws for quantifiers *)

Lemma not_all_not_ex :
 forall P:U -> Prop, ~ (forall n:U, ~ P n) ->  exists n : U, P n.
Proof.
intros P notall.
apply NNPP.
intro abs.
apply notall.
intros n H.
apply abs; exists n; exact H.
Qed.

Lemma not_all_ex_not :
 forall P:U -> Prop, ~ (forall n:U, P n) ->  exists n : U, ~ P n.
Proof.
intros P notall.
apply not_all_not_ex with (P:=fun x => ~ P x).
intro all; apply notall.
intro n; apply NNPP.
apply all.
Qed.

Lemma not_ex_all_not :
 forall P:U -> Prop, ~ (exists n : U, P n) -> forall n:U, ~ P n.
Proof. (* Intuitionistic *)
unfold not in |- *; intros P notex n abs.
apply notex.
exists n; trivial.
Qed. 

Lemma not_ex_not_all :
 forall P:U -> Prop, ~ (exists n : U, ~ P n) -> forall n:U, P n.
Proof.
intros P H n.
apply NNPP.
red in |- *; intro K; apply H; exists n; trivial.
Qed.

Lemma ex_not_not_all :
 forall P:U -> Prop, (exists n : U, ~ P n) -> ~ (forall n:U, P n).
Proof. (* Intuitionistic *)
unfold not in |- *; intros P exnot allP.
elim exnot; auto.
Qed.

Lemma all_not_not_ex :
 forall P:U -> Prop, (forall n:U, ~ P n) -> ~ (exists n : U, P n).
Proof. (* Intuitionistic *)
unfold not in |- *; intros P allnot exP; elim exP; intros n p.
apply allnot with n; auto.
Qed.

End Generic.
