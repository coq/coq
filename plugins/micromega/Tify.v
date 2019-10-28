(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import ZifyClasses.

Ltac tify_unop OP Spec X :=
  let r := fresh "r" in
  pose proof (Spec X);
  set (r := OP X) in *;
  clearbody r.


Ltac tify_binop OP Spec X Y :=
  tify_unop (OP X) (Spec X) Y.


Ltac applySpec S :=
  let t := type of S in
  match t with
  | @BinOpSpec _ _ ?Op _ =>
    let Spec := (eval unfold S, BSpec in (@BSpec _ _ Op _ S)) in
    repeat
      match goal with
      | H : context[Op ?X ?Y] |- _ => tify_binop Op Spec X Y
      | |- context[Op ?X ?Y]       => tify_binop Op Spec X Y
      end
  | @UnOpSpec _ _ ?Op _ =>
    let Spec := (eval unfold S, USpec in (@USpec _ _ Op _ S)) in
    repeat
      match goal with
      | H : context[Op ?X] |- _ => tify_unop Op Spec X
      | |- context[Op ?X ]       => tify_unop Op Spec X
      end
  end.
