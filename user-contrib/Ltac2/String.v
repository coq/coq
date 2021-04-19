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
Require Import Ltac2.Int Ltac2.Char.

Ltac2 @external make : int -> char -> string := "ltac2" "string_make".
Ltac2 @external length : string -> int := "ltac2" "string_length".
Ltac2 @external get : string -> int -> char := "ltac2" "string_get".
Ltac2 @external set : string -> int -> char -> unit := "ltac2" "string_set".
Ltac2 @external to_int : string -> int option := "ltac2" "string_to_int".

Ltac2 equal (x : string) (y : string) : bool :=
  let rec aux n :=
    if Int.lt n 0 then true
    else if Char.equal (String.get x n) (String.get y n) then aux (Int.sub n 1)
    else false
  in
  let len := String.length x in
  if Int.equal len (String.length y) then aux (Int.sub len 1)
  else false.
