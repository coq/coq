(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** This file is obsolete, use Classical_Pred_Type.v via Classical.v
instead *)

(** Classical Predicate Logic on Set*)

Require Import Classical_Pred_Type.

Section Generic.
Variable U : Set.

(** de Morgan laws for quantifiers *)

Lemma not_all_ex_not :
 forall P:U -> Prop, ~ (forall n:U, P n) ->  exists n : U, ~ P n.
Proof (Classical_Pred_Type.not_all_ex_not U).

Lemma not_all_not_ex :
 forall P:U -> Prop, ~ (forall n:U, ~ P n) ->  exists n : U, P n.
Proof (Classical_Pred_Type.not_all_not_ex U).

Lemma not_ex_all_not :
 forall P:U -> Prop, ~ (exists n : U, P n) -> forall n:U, ~ P n.
Proof (Classical_Pred_Type.not_ex_all_not U).

Lemma not_ex_not_all :
 forall P:U -> Prop, ~ (exists n : U, ~ P n) -> forall n:U, P n.
Proof (Classical_Pred_Type.not_ex_not_all U).

Lemma ex_not_not_all :
 forall P:U -> Prop, (exists n : U, ~ P n) -> ~ (forall n:U, P n).
Proof (Classical_Pred_Type.ex_not_not_all U).

Lemma all_not_not_ex :
 forall P:U -> Prop, (forall n:U, ~ P n) -> ~ (exists n : U, P n).
Proof (Classical_Pred_Type.all_not_not_ex U).

End Generic.
