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

type 'a call =
  | In_loadpath of string
  | Raw_interp of string
  | Interp of bool * string
  | Rewind of int
  | Read_stdout
  | Cur_goals
  | Cur_status
  | Cases of string

let is_in_loadpath s : bool call = In_loadpath s
let raw_interp s : unit call = Raw_interp s
let interp (b,s) : unit call = Interp (b,s)
let rewind i : unit call = Rewind i
let read_stdout : string call = Read_stdout
let current_goals : goals call = Cur_goals
let current_status : string call = Cur_status
let make_cases s : string list list call = Cases s

(** * Coq answers to CoqIde *)

type location = (int * int) option (* start and end of the error *)

type 'a value =
  | Good of 'a
  | Fail of (location * string)

type handler = {
  is_in_loadpath : string -> bool;
  raw_interp : string -> unit;
  interp : bool * string -> unit;
  rewind : int -> unit;
  read_stdout : unit -> string;
  current_goals : unit -> goals;
  current_status : unit -> string;
  make_cases : string -> string list list;
}

let abstract_eval_call handler explain_exn c =
  try
    let res = match c with
      | In_loadpath s -> Obj.magic (handler.is_in_loadpath s)
      | Raw_interp s -> Obj.magic (handler.raw_interp s)
      | Interp (b,s) -> Obj.magic (handler.interp (b,s))
      | Rewind i -> Obj.magic (handler.rewind i)
      | Read_stdout -> Obj.magic (handler.read_stdout ())
      | Cur_goals -> Obj.magic (handler.current_goals ())
      | Cur_status -> Obj.magic (handler.current_status ())
      | Cases s -> Obj.magic (handler.make_cases s)
    in Good res
  with e ->
    let (l,str) = explain_exn e in
    Fail (l,str)
