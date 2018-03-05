(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Bool.
Require Export Ring_theory.
Require Export Ring_base.
Require Export InitialRing.
Require Export Ring_tac.

Lemma BoolTheory :
  ring_theory false true xorb andb xorb (fun b:bool => b) (eq(A:=bool)).
split; simpl.
destruct x; reflexivity.
destruct x; destruct y; reflexivity.
destruct x; destruct y; destruct z; reflexivity.
reflexivity.
destruct x; destruct y; reflexivity.
destruct x; destruct y; reflexivity.
destruct x; destruct y; destruct z; reflexivity.
reflexivity.
destruct x; reflexivity.
Qed.

Definition bool_eq (b1 b2:bool) :=
  if b1 then b2 else negb b2.

Lemma bool_eq_ok : forall b1 b2, bool_eq b1 b2 = true -> b1 = b2.
destruct b1; destruct b2; auto.
Qed.

Ltac bool_cst t :=
  let t := eval hnf in t in
  match t with
    true => constr:(true)
  | false => constr:(false)
  | _ => constr:(NotConstant)
  end.

Add Ring bool_ring : BoolTheory (decidable bool_eq_ok, constants [bool_cst]).
