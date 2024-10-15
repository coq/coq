(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.
Require Import Ltac2.Int.

(** Type of a reference cell, similar to OCaml's ['a ref] type. *)
Ltac2 Type 'a ref := 'a Init.ref.

Ltac2 ref (v : 'a) : 'a ref := { contents := v}.
Ltac2 get (r : 'a ref) : 'a := r.(contents).
Ltac2 set (r : 'a ref) (v : 'a) : unit := r.(contents) := v.

Ltac2 incr (r : int ref) : unit := r.(contents) := add (r.(contents)) 1.
Ltac2 decr (r : int ref) : unit := r.(contents) := sub (r.(contents)) 1.

Ltac2 update (r : 'a ref) (f : 'a -> 'a) : unit :=
  r.(contents) := f (r.(contents)).
