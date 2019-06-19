(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Some of the below functions are inspired by ocaml-extlib *)

Require Import Ltac2.Init.
Require Import Ltac2.Control.

Ltac2 may (f : 'a -> unit) (ov : 'a option) :=
  match ov with
  | Some v => f v
  | None => ()
  end.

Ltac2 map (f : 'a -> 'b) (ov : 'a option) :=
  match ov with
  | Some v => Some (f v)
  | None => None
  end.

Ltac2 default (def : 'a) (ov : 'a option) :=
  match ov with
  | Some v => v
  | None => def
  end.

Ltac2 map_default (f : 'a -> 'b) (def : 'b) (ov : 'a option) :=
  match ov with
  | Some v => f v
  | None => def
  end.

Ltac2 get (ov : 'a option) :=
  match ov with
  | Some v => v
  | None => Control.throw No_value
  end.

Ltac2 get_bt (ov : 'a option) :=
  match ov with
  | Some v => v
  | None => Control.zero No_value
  end.

Ltac2 bind (x : 'a option) (f : 'a -> 'b option) :=
  match x with
  | Some x => f x
  | None => None
  end.

Ltac2 ret (x : 'a) := Some x.

Ltac2 lift (f : 'a -> 'b) (x : 'a option) := map f x.
