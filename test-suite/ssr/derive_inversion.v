(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import ssreflect ssrbool.

Set Implicit Arguments.

  Inductive wf T : bool -> option T -> Type :=
  | wf_f : wf false None
  | wf_t : forall x, wf true (Some x).

  Derive Inversion wf_inv with (forall T b (o : option T), wf b o) Sort Prop.

  Lemma Problem T b (o : option T) :
    wf b o ->
    match b with
    | true  => exists x, o = Some x
    | false => o = None
    end.
  Proof.
  by case: b; elim/wf_inv=> //; case: o=> // a *; exists a.
  Qed.
