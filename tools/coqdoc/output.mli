(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Index

type target_language = LaTeX | HTML | TeXmacs

val target_language : target_language ref

val set_out_file : string -> unit
val output_dir : string ref
val close : unit -> unit

val quiet : bool ref
val short : bool ref
val light : bool ref
val header_trailer : bool ref
val index : bool ref
val multi_index : bool ref
val toc : bool ref
val title : string ref
val externals : bool ref
val coqlib : string ref
val raw_comments : bool ref

val charset : string ref
val inputenc : string ref
val set_latin1 : unit -> unit
val set_utf8 : unit -> unit

val add_printing_token : string -> string option * string option -> unit
val remove_printing_token : string -> unit

val set_module : coq_module -> unit

val header : unit -> unit
val trailer : unit -> unit

val push_in_preamble : string -> unit

val dump_file : string -> unit

val start_module : unit -> unit

val start_doc : unit -> unit
val end_doc : unit -> unit

val start_coq : unit -> unit
val end_coq : unit -> unit

val start_code : unit -> unit
val end_code : unit -> unit

val start_inline_coq : unit -> unit
val end_inline_coq : unit -> unit

val indentation : int -> unit
val line_break : unit -> unit
val paragraph : unit -> unit
val empty_line_of_code : unit -> unit

val section : int -> (unit -> unit) -> unit

val item : int -> unit

val rule : unit -> unit

val char : char -> unit
val ident : string -> loc -> unit
val symbol : string -> unit

val latex_char : char -> unit
val latex_string : string -> unit
val html_char : char -> unit
val html_string : string -> unit
val verbatim_char : char -> unit
val hard_verbatim_char : char -> unit

val start_latex_math : unit -> unit
val stop_latex_math : unit -> unit
val start_verbatim : unit -> unit
val stop_verbatim : unit -> unit

val make_index : unit -> unit
val make_toc : unit -> unit
