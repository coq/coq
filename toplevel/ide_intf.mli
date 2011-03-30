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

type 'a call

val raw_interp : string -> unit call
val interp : bool * string -> unit call
val rewind : int -> unit call
val is_in_loadpath : string -> bool call
val make_cases : string -> string list list call
(** The status, for instance "Ready in SomeSection, proving Foo" *)
val current_status : string call
val current_goals : goals call
(** What has been displayed by coqtop recently ? *)
val read_stdout : string call

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

val abstract_eval_call :
  handler -> (exn -> location * string) ->
  'a call -> 'a value
