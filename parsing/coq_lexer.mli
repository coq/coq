(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

val add_keyword : string -> unit
val remove_keyword : string -> unit
val is_keyword : string -> bool

(* val location_function : int -> Loc.t *)

(** for coqdoc *)
type location_table
val location_table : unit -> location_table
val restore_location_table : location_table -> unit

val check_ident : string -> unit
val is_ident : string -> bool
val check_keyword : string -> unit

type frozen_t
val freeze : unit -> frozen_t
val unfreeze : frozen_t -> unit

type com_state
val com_state: unit -> com_state
val restore_com_state: com_state -> unit

val terminal : string -> Tok.t

(** The lexer of Coq: *)

include Compat.LexerSig
