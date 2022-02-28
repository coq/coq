type target_language = LaTeX | HTML | TeXmacs | Raw
type output_t = StdOut | MultFiles | File of string
type file_t = Vernac_file of string * string | Latex_file of string
type glob_source_t = NoGlob | DotGlob | GlobFile of string
type encoding_t = {
  charset : string;
  inputenc : string;
  latin1 : bool;
  utf8 : bool;
}
module Prefs :
  sig
    type t = {
      targetlang : target_language;
      compile_targets : LatexCompiler.otype list;
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
      parse_comments : bool;
      plain_comments : bool;
      toc_depth : int option;
      lib_name : string;
      lib_subtitles : bool;
      inline_notmono : bool;
    }
  end
val prefs : Prefs.t ref
val args_options : (string * Arg.spec * string) list
