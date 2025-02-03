(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

Ltac2 iter (f : 'a -> unit) (ov : 'a option) :=
  match ov with
  | Some v => f v
  | None => ()
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

Ltac2 join (x : 'a option option) :=
  match x with
  | Some x => x
  | None => None
  end.

Ltac2 ret (x : 'a) := Some x.

Ltac2 lift (f : 'a -> 'b) (x : 'a option) := map f x.

Ltac2 equal (eq : 'a -> 'b -> bool) (a : 'a option) (b : 'b option) : bool
  := match a with
     | None => match b with
               | None => true
               | _ => false
               end
     | Some a => match b with
                 | Some b => eq a b
                 | _ => false
                 end
     end.

Ltac2 compare (cmp : 'a -> 'b -> int) (a : 'a option) (b : 'b option) :=
  match a, b with
  | Some a, Some b => cmp a b
  | None, None => 0
  | None, Some _ => -1
  | Some _, None => 1
  end.


Ltac2 is_some (a : 'a option) :=
  match a with
  | Some _ => true
  | None => false
  end.

Ltac2 is_none (a : 'a option) :=
  match a with
  | Some _ => false
  | None => true
  end.
