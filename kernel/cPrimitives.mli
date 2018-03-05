(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t =
  | Int31head0
  | Int31tail0
  | Int31add
  | Int31sub
  | Int31mul
  | Int31div
  | Int31mod
(*
  | Int31lsr
  | Int31lsl
 *)
  | Int31land
  | Int31lor
  | Int31lxor
  | Int31addc
  | Int31subc
  | Int31addcarryc
  | Int31subcarryc
  | Int31mulc
  | Int31diveucl
  | Int31div21
  | Int31addmuldiv
  | Int31eq
  | Int31lt
  | Int31le
  | Int31compare

val hash : t -> int

val to_string : t -> string
