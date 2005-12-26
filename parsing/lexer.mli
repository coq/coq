(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Pp
open Util

type error =
  | Illegal_character
  | Unterminated_comment
  | Unterminated_string
  | Undefined_token
  | Bad_token of string

exception Error of error

val add_token : string * string -> unit
val is_keyword : string -> bool

val func : char Stream.t -> (string * string) Stream.t * (int -> loc)
val location_function : int -> loc

(* for coqdoc *)
type location_table
val location_table : unit -> location_table
val restore_location_table : location_table -> unit

val check_ident : string -> unit
val check_keyword : string -> unit

val tparse : string * string -> ((string * string) Stream.t -> string) option

val token_text : string * string -> string

type frozen_t
val freeze : unit -> frozen_t
val unfreeze : frozen_t -> unit
val init : unit -> unit

type com_state
val com_state: unit -> com_state
val restore_com_state: com_state -> unit

val set_xml_output_comment : (string -> unit) -> unit

val terminal : string -> string * string
