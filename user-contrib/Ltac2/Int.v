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

Ltac2 @ external equal : int -> int -> bool := "ltac2" "int_equal".
Ltac2 @ external compare : int -> int -> int := "ltac2" "int_compare".
Ltac2 @ external add : int -> int -> int := "ltac2" "int_add".
Ltac2 @ external sub : int -> int -> int := "ltac2" "int_sub".
Ltac2 @ external mul : int -> int -> int := "ltac2" "int_mul".
(* Note: unlike Coq Z division, Ltac2 matches OCaml division and rounds towards 0, so 1/-2 = 0 *)
Ltac2 @ external div : int -> int -> int := "ltac2" "int_div".
Ltac2 @ external mod : int -> int -> int := "ltac2" "int_mod".
Ltac2 @ external neg : int -> int := "ltac2" "int_neg".
Ltac2 @ external abs : int -> int := "ltac2" "int_abs".

Ltac2 @ external asr : int -> int -> int := "ltac2" "int_asr".
Ltac2 @ external lsl : int -> int -> int := "ltac2" "int_lsl".
Ltac2 @ external lsr : int -> int -> int := "ltac2" "int_lsr".
Ltac2 @ external land : int -> int -> int := "ltac2" "int_land".
Ltac2 @ external lor : int -> int -> int := "ltac2" "int_lor".
Ltac2 @ external lxor : int -> int -> int := "ltac2" "int_lxor".
Ltac2 @ external lnot : int -> int := "ltac2" "int_lnot".

Ltac2 lt (x : int) (y : int) := equal (compare x y) -1.
Ltac2 gt (x : int) (y : int) := equal (compare x y) 1.
Ltac2 le (x : int) (y : int) :=
  (* we might use [lt x (add y 1)], but that has the wrong behavior on MAX_INT *)
  match equal x y with
  | true => true
  | false => lt x y
  end.
Ltac2 ge (x : int) (y : int) :=
  (* we might use [lt (add x 1) y], but that has the wrong behavior on MAX_INT *)
  match equal x y with
  | true => true
  | false => gt x y
  end.
