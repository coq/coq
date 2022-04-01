(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.

(** * Boolean operators *)

Ltac2 and x y :=
  match x with
  | true => y
  | false => false
  end.

Ltac2 or x y :=
  match x with
  | true => true
  | false => y
  end.

Ltac2 impl x y :=
  match x with
  | true => y
  | false => true
  end.

Ltac2 neg x :=
  match x with
  | true => false
  | false => true
  end.

Ltac2 xor x y :=
  match x with
  | true
    => match y with
       | true => false
       | false => true
       end
  | false
    => match y with
       | true => true
       | false => false
       end
  end.

Ltac2 equal x y :=
  match x with
  | true
    => match y with
       | true => true
       | false => false
       end
  | false
    => match y with
       | true => false
       | false => true
       end
  end.

(** * Boolean operators with lazy evaluation of the second argument *)

Ltac2 Notation x(self) "&&" y(thunk(self)) : 2 :=
  match x with
  | true => y ()
  | false => false
  end.

Ltac2 Notation x(self) "||" y(thunk(self)) : 3 :=
  match x with
  | true => true
  | false => y ()
  end.
