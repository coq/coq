(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Classical Predicate Logic on Type *)

Require Classical_Prop.

Section Generic.
Variable U: Type.

(** de Morgan laws for quantifiers *)

Lemma not_all_ex_not : (P:U->Prop)(~(n:U)(P n)) -> (EXT n:U | ~(P n)).
Proof.
Unfold not; Intros P notall.
Apply NNPP; Unfold not.
Intro abs.
Cut ((n:U)(P n)); Auto.
Intro n; Apply NNPP.
Unfold not; Intros.
Apply abs; Exists n; Trivial.
Qed.

Lemma not_all_not_ex : (P:U->Prop)(~(n:U)~(P n)) -> (EXT n:U | (P n)).
Proof.
Intros P H.
Elim (not_all_ex_not [n:U]~(P n) H); Intros n Pn; Exists n.
Apply NNPP; Trivial.
Qed.

Lemma not_ex_all_not : (P:U->Prop)(~(EXT n:U | (P n))) -> (n:U)~(P n).
Proof.
Unfold not; Intros P notex n abs.
Apply notex.
Exists n; Trivial.
Qed. 

Lemma not_ex_not_all : (P:U->Prop)(~(EXT n:U | ~(P n))) -> (n:U)(P n).
Proof.
Intros P H n.
Apply NNPP.
Red; Intro K; Apply H; Exists n; Trivial.
Qed.

Lemma ex_not_not_all : (P:U->Prop) (EXT n:U | ~(P n)) -> ~(n:U)(P n).
Proof.
Unfold not; Intros P exnot allP.
Elim exnot; Auto.
Qed.

Lemma all_not_not_ex : (P:U->Prop) ((n:U)~(P n)) -> ~(EXT n:U | (P n)).
Proof.
Unfold not; Intros P allnot exP; Elim exP; Intros n p.
Apply allnot with n; Auto.
Qed.

End Generic.
