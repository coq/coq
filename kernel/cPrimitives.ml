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

let hash = function
  | Int31head0 -> 1
  | Int31tail0 -> 2
  | Int31add -> 3
  | Int31sub -> 4
  | Int31mul -> 5
  | Int31div -> 6
  | Int31mod -> 7
(*
  | Int31lsr -> 8
  | Int31lsl -> 9
 *)
  | Int31land -> 10
  | Int31lor -> 11
  | Int31lxor -> 12
  | Int31addc -> 13
  | Int31subc -> 14
  | Int31addcarryc -> 15
  | Int31subcarryc -> 16
  | Int31mulc -> 17
  | Int31diveucl -> 18
  | Int31div21 -> 19
  | Int31addmuldiv -> 20
  | Int31eq -> 21
  | Int31lt -> 22
  | Int31le -> 23
  | Int31compare -> 24

let to_string = function
  | Int31head0 -> "head0"
  | Int31tail0 -> "tail0"
  | Int31add -> "add"
  | Int31sub -> "sub"
  | Int31mul -> "mul"
  | Int31div -> "div"
  | Int31mod -> "mod"
(*
  | Int31lsr -> "l_sr"
  | Int31lsl -> "l_sl"
 *)
  | Int31land -> "l_and"
  | Int31lor -> "l_or"
  | Int31lxor -> "l_xor"
  | Int31addc -> "addc"
  | Int31subc -> "subc"
  | Int31addcarryc -> "addcarryc"
  | Int31subcarryc -> "subcarryc"
  | Int31mulc -> "mulc"
  | Int31diveucl -> "diveucl"
  | Int31div21 -> "div21"
  | Int31addmuldiv -> "addmuldiv"
  | Int31eq -> "eq"
  | Int31lt -> "lt"
  | Int31le -> "le"
  | Int31compare -> "compare"
