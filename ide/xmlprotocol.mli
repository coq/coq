(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Applicative part of the interface of CoqIde calls to Coq *)

open Interface
open Xml_datatype

type 'a call

type unknown_call = Unknown : 'a call -> unknown_call

val add         : add_sty         -> add_rty call
val edit_at     : edit_at_sty     -> edit_at_rty call
val query       : query_sty       -> query_rty call
val goals       : goals_sty       -> goals_rty call
val hints       : hints_sty       -> hints_rty call
val status      : status_sty      -> status_rty call
val mkcases     : mkcases_sty     -> mkcases_rty call
val evars       : evars_sty       -> evars_rty call
val search      : search_sty      -> search_rty call
val get_options : get_options_sty -> get_options_rty call
val set_options : set_options_sty -> set_options_rty call
val quit        : quit_sty        -> quit_rty call
val init        : init_sty        -> init_rty call
val stop_worker : stop_worker_sty -> stop_worker_rty call
(* internal use (fake_ide) only, do not use *)
val wait        : wait_sty        -> wait_rty call
(* retrocompatibility *)
val interp      : interp_sty      -> interp_rty call
val print_ast   : print_ast_sty   -> print_ast_rty call
val annotate    : annotate_sty    -> annotate_rty call

val abstract_eval_call : handler -> 'a call -> 'a value

(** * Protocol version *)

val protocol_version : string

(** By default, we still output messages in Richpp so we are
    compatible with 8.6, however, 8.7 aware clients will want to
    set this to Ppcmds *)
type msg_format = Richpp of int | Ppcmds

(** * XML data marshalling *)

val of_call : 'a call -> xml
val to_call : xml -> unknown_call

val of_answer : msg_format -> 'a call -> 'a value -> xml
val to_answer : 'a call -> xml -> 'a value

(* Prints the documentation of this module *)
val document : (xml -> string) -> unit

(** * Debug printing *)

val pr_call : 'a call -> string
val pr_value : 'a value -> string
val pr_full_value : 'a call -> 'a value -> string

(** * Serializaiton of feedback  *)
val of_feedback : msg_format -> Feedback.feedback -> xml
val to_feedback : xml -> Feedback.feedback

val is_feedback : xml -> bool
