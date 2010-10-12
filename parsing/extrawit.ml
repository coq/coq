(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Genarg

(* This file defines extra argument types *)

(* Tactics as arguments *)

let tactic_main_level = 5

let (wit_tactic0,globwit_tactic0,rawwit_tactic0) = create_arg "tactic0"
let (wit_tactic1,globwit_tactic1,rawwit_tactic1) = create_arg "tactic1"
let (wit_tactic2,globwit_tactic2,rawwit_tactic2) = create_arg "tactic2"
let (wit_tactic3,globwit_tactic3,rawwit_tactic3) = create_arg "tactic3"
let (wit_tactic4,globwit_tactic4,rawwit_tactic4) = create_arg "tactic4"
let (wit_tactic5,globwit_tactic5,rawwit_tactic5) = create_arg "tactic5"

let wit_tactic = function
  | 0 -> wit_tactic0
  | 1 -> wit_tactic1
  | 2 -> wit_tactic2
  | 3 -> wit_tactic3
  | 4 -> wit_tactic4
  | 5 -> wit_tactic5
  | n -> anomaly ("Unavailable tactic level: "^string_of_int n)

let globwit_tactic = function
  | 0 -> globwit_tactic0
  | 1 -> globwit_tactic1
  | 2 -> globwit_tactic2
  | 3 -> globwit_tactic3
  | 4 -> globwit_tactic4
  | 5 -> globwit_tactic5
  | n -> anomaly ("Unavailable tactic level: "^string_of_int n)

let rawwit_tactic = function
  | 0 -> rawwit_tactic0
  | 1 -> rawwit_tactic1
  | 2 -> rawwit_tactic2
  | 3 -> rawwit_tactic3
  | 4 -> rawwit_tactic4
  | 5 -> rawwit_tactic5
  | n -> anomaly ("Unavailable tactic level: "^string_of_int n)

let tactic_genarg_level s =
  if String.length s = 7 && String.sub s 0 6 = "tactic" then
    let c = s.[6] in if '5' >= c && c >= '0' then Some (Char.code c - 48)
    else None
  else None

let is_tactic_genarg = function
| ExtraArgType s -> tactic_genarg_level s <> None
| _ -> false
