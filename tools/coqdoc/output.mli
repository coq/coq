(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Cdglobals
open Index

(* Common primitives: should be moved to out_common? *)
val add_printing_token    : string -> string option * string option -> unit
val remove_printing_token : string -> unit

(* This interface should be improved. *)
type toc_entry =
  | Toc_library of string * string option
  | Toc_section of int * (unit -> unit) * string

val add_toc_entry : toc_entry -> unit
val toc_q : toc_entry Queue.t

val is_keyword : string -> bool
val is_tactic  : string -> bool

(* Backend printer *)
module type S = sig

(** XXX move to start_file  *)
val push_in_preamble : string -> unit

(** [support_files] List of support files to be copied along the output. *)
val support_files    : string list

(** [appendix toc index split_index standalone] Backend-specific
    function that outputs additional files. *)
val appendix : toc:bool -> index:bool -> split_index:bool -> standalone:bool -> unit

(** [start_file fmt toc index split_index standalone] Start a logical
    output file to formatter [fmt]. [toc], [index], and [standalone]
    control whether the backend will generate a TOC, index, and
    header/trailers for the file.
*)
val start_file : Format.formatter -> toc:bool -> index:bool ->
                 split_index:bool -> standalone:bool -> unit

(** [end_file] Ends the file *)
val end_file : unit -> unit

(** [start_module mod] Starts a coq module. *)
val start_module : coq_module -> unit

(** [start_doc] Moves the backend to "document" mode. *)
val start_doc : unit -> unit
val end_doc : unit -> unit

val start_emph : unit -> unit
val stop_emph : unit -> unit

val start_comment : unit -> unit
val end_comment : unit -> unit

val start_coq : unit -> unit
val end_coq : unit -> unit

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

val char    : char -> unit
val keyword : string -> loc -> unit
val ident   : string -> loc option -> unit

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

end

module Latex   : S
module Html    : S
module TeXmacs : S
module Raw     : S
