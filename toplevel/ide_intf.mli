(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2014     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Applicative part of the interface of CoqIde calls to Coq *)

open Interface

type xml = Xml_parser.xml

type 'a call

type unknown

val interp      : interp_sty      -> interp_rty call
val rewind      : rewind_sty      -> rewind_rty call
val goals       : goals_sty       -> goals_rty call
val hints       : hints_sty       -> hints_rty call
val status      : status_sty      -> status_rty call
val inloadpath  : inloadpath_sty  -> inloadpath_rty call
val mkcases     : mkcases_sty     -> mkcases_rty call
val evars       : evars_sty       -> evars_rty call
val search      : search_sty      -> search_rty call
val get_options : get_options_sty -> get_options_rty call
val set_options : set_options_sty -> set_options_rty call
val quit        : quit_sty        -> quit_rty call

val abstract_eval_call : handler -> 'a call -> 'a value

(** * Protocol version *)

val protocol_version : string

(** * XML data marshalling *)

exception Marshal_error

val of_call : 'a call -> xml
val to_call : xml -> unknown call

val of_message : message -> xml
val to_message : xml -> message
val is_message : xml -> bool

val of_value : ('a -> xml) -> 'a value -> xml

val of_feedback : feedback -> xml
val to_feedback : xml -> feedback
val is_feedback : xml -> bool

val of_answer : 'a call -> 'a value -> xml
val to_answer : xml -> 'a call -> 'a value

(** * Debug printing *)

val pr_call : 'a call -> string
val pr_value : 'a value -> string
val pr_full_value : 'a call -> 'a value -> string
