(* Global CoqDoc types *)

type target_language = LaTeX | HTML | TeXmacs | Raw

type output_t = StdOut | MultFiles | File of string

type glob_source_t = NoGlob | DotGlob | GlobFile of string

type coq_module = string
type file = Vernac_file of string * coq_module

(* Path handling functions *)
val normalize_path     : string -> string
val normalize_filename : string -> string * string

(** [coqdoc_out f] locates output file *)
val coqdoc_out  : string -> string

(** [with_outfile s f] opens a file named [s] and calls [f out] where
    [out] is the file descriptor *)
val with_outfile : string -> (out_channel -> unit) -> unit

(* Global options *)
val out_to      : output_t ref
val output_dir  : string ref
val glob_source : glob_source_t ref

val target_language : target_language ref

(* Index options *)
val index       : bool ref
val index_name  : string ref
val multi_index : bool ref
val toc         : bool ref

(* Header/Footer *)
val header_trailer   : bool ref
val header_file      : string ref
val header_file_spec : bool ref
val footer_file      : string ref
val footer_file_spec : bool ref

val page_title : string ref
val title : string ref

val quiet          : bool ref
val light          : bool ref
val gallina        : bool ref
val short          : bool ref
val externals      : bool ref
val coqlib         : string ref
val coqlib_path    : string ref
val raw_comments   : bool ref
val parse_comments : bool ref
val plain_comments : bool ref
val toc_depth      : int option ref
val lib_name       : string ref
val lib_subtitles  : bool ref
val interpolate    : bool ref
val inline_notmono : bool ref

(* Encoding options *)
val set_latin1 : unit -> unit
val set_utf8   : unit -> unit

val charset    : string ref
val inputenc   : string ref
val latin1     : bool ref
val utf8       : bool ref
