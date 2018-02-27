(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Cdglobals
open Index

val initialize : unit -> unit

val add_printing_token : string -> string option * string option -> unit
val remove_printing_token : string -> unit

val set_module : coq_module -> string option -> unit
val get_module : bool -> string

val header : unit -> unit
val trailer : unit -> unit

val push_in_preamble : string -> unit

val start_module : unit -> unit

val start_doc : unit -> unit
val end_doc : unit -> unit

val start_emph : unit -> unit
val stop_emph : unit -> unit

val start_comment : unit -> unit
val end_comment : unit -> unit

val start_coq : unit -> unit
val end_coq : unit -> unit

val start_code : unit -> unit
val end_code : unit -> unit

val start_inline_coq : unit -> unit
val end_inline_coq : unit -> unit

val start_inline_coq_block : unit -> unit
val end_inline_coq_block : unit -> unit

val indentation : int -> unit
val line_break : unit -> unit
val paragraph : unit -> unit
val empty_line_of_code : unit -> unit

val section : int -> (unit -> unit) -> unit

val item : int -> unit
val stop_item : unit -> unit
val reach_item_level : int -> unit

val rule : unit -> unit

val nbsp : unit -> unit
val char : char -> unit
val keyword : string -> loc -> unit
val ident : string -> loc option -> unit
val sublexer : char -> loc -> unit
val sublexer_in_doc : char -> unit

val proofbox : unit -> unit

val latex_char : char -> unit
val latex_string : string -> unit
val html_char : char -> unit
val html_string : string -> unit
val verbatim_char : bool -> char -> unit
val hard_verbatim_char : char -> unit

val start_latex_math : unit -> unit
val stop_latex_math : unit -> unit
val start_verbatim : bool -> unit
val stop_verbatim : bool -> unit
val start_quote : unit -> unit
val stop_quote : unit -> unit

val url : string -> string option -> unit

(* this outputs an inference rule in one go.  You pass it the list of
   assumptions, then the middle line info, then the conclusion (which
   is allowed to span multiple lines).

   In each case, the int is the number of spaces before the start of
   the line's text and the string is the text of the line with the
   leading trailing space trimmed.  For the middle rule, you can
   also optionally provide a name.

   We need the space info so that in modes where we aren't doing
   something smart we can just format the rule verbatim like the user did
*)
val inf_rule :  (int * string) list
             -> (int * string * (string option)) 
             -> (int * string) list
             -> unit

val make_multi_index : unit -> unit
val make_index : unit -> unit
val make_toc : unit -> unit
