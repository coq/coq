(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Pp

type error =
  | Illegal_character
  | Unterminated_comment
  | Unterminated_string
  | Undefined_token
  | Bad_token of string

exception Error of error

val add_keyword : string -> unit
val is_keyword : string -> bool

val func : char Stream.t -> (string * string) Stream.t * (int -> int * int)
val current_location_function : (int -> int  * int) ref

val check_ident : string -> unit
val check_special_token : string -> unit

val is_normal_token : string -> bool

val add_token : Token.pattern -> unit

val tparse : string * string -> ((string * string) Stream.t -> string) option

val token_text : string * string -> string

type frozen_t
val freeze : unit -> frozen_t
val unfreeze : frozen_t -> unit
val init : unit -> unit

type com_state
val com_state: unit -> com_state
val restore_com_state: com_state -> unit
