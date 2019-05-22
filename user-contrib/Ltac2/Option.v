(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.

Ltac2 map (f : 'a -> 'b) (x : 'a option) :=
  match x with
  | Some x => Some (f x)
  | None => None
  end.

Ltac2 bind (x : 'a option) (f : 'a -> 'b option) :=
  match x with
  | Some x => f x
  | None => None
  end.

Ltac2 ret (x : 'a) := Some x.

Ltac2 lift (f : 'a -> 'b) (x : 'a option) := map f x.
