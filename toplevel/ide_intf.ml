(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Interface of calls to Coq by CoqIde *)

type 'a menu = 'a * (string * string) list

type goals =
  | Message of string
  | Goals of ((string menu) list * string menu) list

(** We use phantom types and GADT to protect ourselves against wild casts *)

type raw = bool
type verbose = bool

type 'a call =
  | Interp of raw * verbose * string
  | Rewind of int
  | Goals
  | Status
  | InLoadPath of string
  | MkCases of string

let interp (r,b,s) : string call = Interp (r,b,s)
let rewind i : int call = Rewind i
let goals : goals call = Goals
let status : string call = Status
let inloadpath s : bool call = InLoadPath s
let mkcases s : string list list call = MkCases s

(** * Coq answers to CoqIde *)

type location = (int * int) option (* start and end of the error *)

type 'a value =
  | Good of 'a
  | Fail of (location * string)

type handler = {
  interp : raw * verbose * string -> string;
  rewind : int -> int;
  goals : unit -> goals;
  status : unit -> string;
  inloadpath : string -> bool;
  mkcases : string -> string list list;
}

let abstract_eval_call handler explain_exn c =
  try
    let res = match c with
      | Interp (r,b,s) -> Obj.magic (handler.interp (r,b,s))
      | Rewind i -> Obj.magic (handler.rewind i)
      | Goals -> Obj.magic (handler.goals ())
      | Status -> Obj.magic (handler.status ())
      | InLoadPath s -> Obj.magic (handler.inloadpath s)
      | MkCases s -> Obj.magic (handler.mkcases s)
    in Good res
  with e ->
    let (l,str) = explain_exn e in
    Fail (l,str)

(** * Debug printing *)

let pr_call = function
  | Interp (r,b,s) ->
    let raw = if r then "RAW" else "" in
    let verb = if b then "" else "SILENT" in
    "INTERP"^raw^verb^" ["^s^"]"
  | Rewind i -> "REWIND "^(string_of_int i)
  | Goals -> "GOALS"
  | Status -> "STATUS"
  | InLoadPath s -> "INLOADPATH "^s
  | MkCases s -> "MKCASES "^s

let pr_value_gen pr = function
  | Good v -> "GOOD " ^ pr v
  | Fail (_,str) -> "FAIL ["^str^"]"

let pr_value v = pr_value_gen (fun _ -> "") v

let pr_string s = "["^s^"]"
let pr_bool b = if b then "true" else "false"

let pr_full_value call value =
  match call with
    | Interp _ -> pr_value_gen pr_string (Obj.magic value)
    | Rewind i -> pr_value_gen string_of_int (Obj.magic value)
    | Goals -> pr_value value (* TODO *)
    | Status -> pr_value_gen pr_string (Obj.magic value)
    | InLoadPath s -> pr_value_gen pr_bool (Obj.magic value)
    | MkCases s -> pr_value value (* TODO *)
