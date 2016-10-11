(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

val add_keyword : string -> unit
val remove_keyword : string -> unit
val is_keyword : string -> bool

(** [get_current_file fname] returns the filename used in locations emitted by
    the lexer *)
val get_current_file : unit -> string

(** [set_current_file fname] sets the filename used in locations emitted by the
    lexer *)
val set_current_file : fname:string -> unit

val check_ident : string -> unit
val is_ident : string -> bool
val check_keyword : string -> unit

type frozen_t
val freeze : unit -> frozen_t
val unfreeze : frozen_t -> unit

val xml_output_comment : (string -> unit) Hook.t

(* Retrieve the comments lexed at a given location of the stream
   currently being processeed *)
val extract_comments : int -> string list

val terminal : string -> Tok.t

(** The lexer of Coq: *)

include Compat.LexerSig
