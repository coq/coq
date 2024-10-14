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

(** User-setable options from command line [coqdoc] arugments **********************)
type t = {
  targetlang : target_language;
  compile_targets : otype list;
  out_to : output_t;
  output_dir: string;
  gallina: bool;
  short : bool;
  light : bool;
  title : string;
  header_trailer : bool;
  header_file_spec : bool;
  header_file : string;
  footer_file_spec : bool;
  footer_file : string;
  index: bool;
  binder_index : bool;
  multi_index : bool;
  index_name : string;
  toc: bool;
  files : file_t list;
  glob_source : glob_source_t;
  quiet : bool;
  externals : bool;
  coqlib_url: string;
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

let default : t = {
  targetlang = HTML;
  compile_targets = [];
  out_to = MultFiles;
  output_dir = "";
  gallina = false;
  short = false;
  light = false;
  title = "";
  header_trailer = true;
  header_file_spec = false;
  header_file = "";
  footer_file_spec = false;
  footer_file = "";
  index = true;
  multi_index = false;
  index_name = "index";
  binder_index = false;
  toc = false;
  files = [];
  glob_source = DotGlob;
  quiet = true;
  externals = true;
  coqlib_url = Coq_config.wwwstdlib;
  paths = [];
  encoding = {
    charset = "iso-8859-1";
    inputenc = "";
    latin1 = false;
    utf8 = false;
  };
  interpolate = false;
  raw_comments = false;
  parse_comments = false;
  plain_comments = false;
  toc_depth = None;
  lib_name = "Library";
  lib_subtitles = false;
  inline_notmono = false;
}

let prefs = ref default

(* Globals *************************************************************************)
let page_title = ref ""
let out_channel = ref stdout
(* End globals *********************************************************************)

(* Little helpers ******************************************************************)
let (/) = Filename.concat

let coqdoc_out f =
  if !prefs.output_dir <> "" && Filename.is_relative f then
    if not (Sys.file_exists !prefs.output_dir) then
      (Printf.eprintf "No such directory: %s\n" !prefs.output_dir; exit 1)
    else
      !prefs.output_dir / f
  else
    f

let open_out_file f =
  out_channel :=
    try open_out (coqdoc_out f)
    with Sys_error s -> Printf.eprintf "%s\n" s; exit 1

let close_out_file () = close_out !out_channel
(* End little helpers **************************************************************)
