(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* High level api for clients of the service (like coqtop) *)

(* Connects to a work manager if any. If no worker manager, then
   -async-proofs-j and -async-proofs-tac-j are used *)
val init : Flags.priority -> unit

(* blocking *)
val get : int -> int

(* not blocking *)
val tryget : int -> int option
val giveback : int -> unit

(* Low level *)
type request =
  | Hello of Flags.priority
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
