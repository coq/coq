(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* High level api for clients of the service (like coqtop) *)

type priority = Low | High
val string_of_priority : priority -> string
val priority_of_string : string -> priority

(* Default priority *)
val async_proofs_worker_priority : priority ref

(* Connects to a work manager if any. If no worker manager, then
   -async-proofs-j and -async-proofs-tac-j are used *)
val init : priority -> unit

(* blocking *)
val get : int -> int

(* not blocking *)
val tryget : int -> int option
val giveback : int -> unit

(* Low level *)
type request =
  | Hello of priority
  | Get of int
  | TryGet of int
  | GiveBack of int
  | Ping

type response =
  | Tokens of int
  | Noluck
  | Pong of int * int * int (* cur, max, pid *)

val connect : string -> Unix.file_descr option

exception ParseError

(* Intended to be used with input_line and output_string *)
val parse_request  : string -> request
val parse_response : string -> response

val print_request  : request -> string
val print_response : response -> string
