(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.
Require Import Ltac2.Notations.
Require Ltac2.Char.
Require Ltac2.List.

Require Import String.

Ltac2 @external make : int -> char -> string := "ltac2" "string_make".
Ltac2 @external length : string -> int := "ltac2" "string_length".
Ltac2 @external get : string -> int -> char := "ltac2" "string_get".
Ltac2 @external set : string -> int -> char -> unit := "ltac2" "string_set".

(** Helper: Convert Coq bool to Ltac2 integer *)

Local Ltac2 bit_to_int (val : constr) (pos : int) :=
  match! val with
  | true => pos
  | false => 0
  end.

(** Convert Coq Ascii to Ltac2 integer *)

Ltac2 ascii_to_int (ascii : constr) :=
  match! ascii with
  | Ascii.Ascii ?b0 ?b1 ?b2 ?b3 ?b4 ?b5 ?b6 ?b7 =>
      (Int.add (bit_to_int b7 128)
      (Int.add (bit_to_int b6 64)
      (Int.add (bit_to_int b5 32)
      (Int.add (bit_to_int b4 16)
      (Int.add (bit_to_int b3 8)
      (Int.add (bit_to_int b2 4)
      (Int.add (bit_to_int b1 2)
               (bit_to_int b0 1) )))))))
  end.

(** Convert Coq Ascii to Ltac2 char *)

Ltac2 ascii_to_char (ascii : constr) := Char.of_int (ascii_to_int ascii).

(** Convert Coq String to Ltac2 char list *)

Ltac2 rec of_coq_string_to_char_list (str : constr) :=
  match! str with
  | String ?ch ?tl => ascii_to_char ch :: of_coq_string_to_char_list tl
  | _  => []
  end.

(** Helper: Set Ltac2 string to Ltac2 list of chars *)

Local Ltac2 rec of_coq_string_aux (l : char list) (s : string) (pos : int) :=
  match l with
  | hd :: tl => String.set s pos hd; of_coq_string_aux tl s (Int.add pos 1)
  | [] => ()
  end.

(** Convert Coq String to Ltac2 string *)

Ltac2 of_coq_string (str : constr) :=
  let clist := of_coq_string_to_char_list str in
  let len := List.length clist in
  let s := String.make len (Char.of_int 0) in
    of_coq_string_aux clist s 0;
    s.
