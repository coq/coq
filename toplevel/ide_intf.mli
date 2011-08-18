(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Interface of CoqIde calls to Coq *)

type 'a menu = 'a * (string * string) list

type goals =
  | Message of string
  | Goals of ((string menu) list * string menu) list

type 'a call

(** Running a command. The boolean is a verbosity flag.
    Output will be fetch later via [read_stdout]. *)
val interp : bool * string -> unit call

(** Running a command with no impact on the undo stack,
    such as a query or a Set/Unset.
    Output will be fetch later via [read_stdout]. *)
val raw_interp : string -> unit call

(** What messages have been displayed by coqtop recently ? *)
val read_stdout : string call

(** Backtracking by a certain number of phrases. *)
val rewind : int -> unit call

(** Is a file present somewhere in Coq's loadpath ? *)
val is_in_loadpath : string -> bool call

(** Create a "match" template for a given inductive type.
    For each branch of the match, we list the constructor name
    followed by enough pattern variables. *)
val make_cases : string -> string list list call

(** The status, for instance "Ready in SomeSection, proving Foo" *)
val current_status : string call

(** Fetching the list of current goals *)
val current_goals : goals call


(** * Coq answers to CoqIde *)

type location = (int * int) option (* start and end of the error *)

type 'a value =
  | Good of 'a
  | Fail of (location * string)

type handler = {
  interp : bool * string -> unit;
  raw_interp : string -> unit;
  read_stdout : unit -> string;
  rewind : int -> unit;
  is_in_loadpath : string -> bool;
  current_goals : unit -> goals;
  current_status : unit -> string;
  make_cases : string -> string list list;
}

val abstract_eval_call :
  handler -> (exn -> location * string) ->
  'a call -> 'a value

(** * Debug printing *)

val pr_call : 'a call -> string
val pr_value : 'a value -> string
