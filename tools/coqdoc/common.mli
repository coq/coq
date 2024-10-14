(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Misc types **********************************************************************)
type target_language = LaTeX | HTML | TeXmacs | Raw
type output_t = StdOut | MultFiles | File of string
type coq_module = string
type file_t = Vernac_file of string * coq_module | Latex_file of string
type glob_source_t = NoGlob | DotGlob | GlobFile of string
type encoding_t = {
  charset : string;
  inputenc : string;
  latin1 : bool;
  utf8 : bool;
}
type otype = Dvi | Ps | Pdf
(* End misc types ******************************************************************)

(* Globals *************************************************************************)
val page_title : string ref
val out_channel : out_channel ref
(* End globals *********************************************************************)

(** User-setable options from command line [coqdoc] arugments **********************)
type t = {
  targetlang : target_language;
  compile_targets : otype list;
  out_to : output_t;
  output_dir : string;
  gallina : bool;
  short : bool;
  light : bool;
  title : string;
  header_trailer : bool;
  header_file_spec : bool;
  header_file : string;
  footer_file_spec : bool;
  footer_file : string;
  index : bool;
  binder_index : bool;
  multi_index : bool;
  index_name : string;
  toc : bool;
  files : file_t list;
  glob_source : glob_source_t;
  quiet : bool;
  externals : bool;
  coqlib_url : string;
  paths : (string * string) list;
  encoding : encoding_t;
  interpolate : bool;
  raw_comments : bool;
  parse_comments : bool;
  plain_comments : bool;
  toc_depth : int option;
  lib_name : string;
  lib_subtitles : bool;
  inline_notmono : bool;
}

(* All command-line options will be stored here after parse_args is called *)
val prefs : t ref

(* Little helpers ******************************************************************)
val (/) : string -> string -> string
val coqdoc_out : string -> string
val open_out_file : string -> unit
val close_out_file : unit -> unit
(* End little helpers **************************************************************)
