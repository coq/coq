type target_language = LaTeX | HTML | TeXmacs | Raw
val target_language : target_language ref
type output_t = StdOut | MultFiles | File of string
val output_dir : string ref
val out_to : output_t ref
val out_channel : out_channel ref
val ( / ) : string -> string -> string
val coqdoc_out : string -> string
val open_out_file : string -> unit
val close_out_file : unit -> unit
type glob_source_t = NoGlob | DotGlob | GlobFile of string
val glob_source : glob_source_t ref
val normalize_path : string -> string
val normalize_filename : string -> string * string
val guess_coqlib : unit -> string
val header_trailer : bool ref
val header_file : string ref
val header_file_spec : bool ref
val footer_file : string ref
val footer_file_spec : bool ref
val quiet : bool ref
val light : bool ref
val gallina : bool ref
val short : bool ref
val index : bool ref
val multi_index : bool ref
val index_name : string ref
val toc : bool ref
val page_title : string ref
val title : string ref
val externals : bool ref
val coqlib : string ref
val coqlib_path : string ref
val raw_comments : bool ref
val parse_comments : bool ref
val plain_comments : bool ref
val toc_depth : int option ref
val lib_name : string ref
val lib_subtitles : bool ref
val interpolate : bool ref
val inline_notmono : bool ref
val charset : string ref
val inputenc : string ref
val latin1 : bool ref
val utf8 : bool ref
val set_latin1 : unit -> unit
val set_utf8 : unit -> unit
type coq_module = string
type file = Vernac_file of string * coq_module | Latex_file of string
