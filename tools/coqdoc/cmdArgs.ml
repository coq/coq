(* Command-line argument parsing *)
type target_language = LaTeX | HTML | TeXmacs | Raw

type output_t =
| StdOut
| MultFiles
| File of string

type file_t =
| Vernac_file of string * string
| Latex_file of string

type glob_source_t = NoGlob | DotGlob | GlobFile of string

type encoding_t = {
  charset : string;
  inputenc : string;
  latin1 : bool;
  utf8 : bool;
}
module Prefs = struct

type t = {
  targetlang : target_language;
  compile_targets : LatexCompiler.otype list;
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
  parse_comments : bool;
  plain_comments : bool;
  toc_depth : int option;
  lib_name : string;
  lib_subtitles : bool;
  inline_notmono : bool;
}

end

open Prefs
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
  parse_comments = false;
  plain_comments = false;
  toc_depth = None;
  lib_name = "Library";
  lib_subtitles = false;
  inline_notmono = false;
}

let prefs = ref default

let normalize_path p =
  (* We use the Unix subsystem to normalize a physical path (relative
     or absolute) and get rid of symbolic links, relative links (like
     ./ or ../ in the middle of the path; it's tricky but it
     works... *)
  (* Rq: Sys.getcwd () returns paths without '/' at the end *)
  let orig = Sys.getcwd () in
  Sys.chdir p;
  let res = Sys.getcwd () in
  Sys.chdir orig;
  res

let normalize_filename f =
  let basename = Filename.basename f in
  let dirname = Filename.dirname f in
  normalize_path dirname, basename

let rec name_of_path p name dirname suffix =
  if p = dirname then String.concat "." (if name = "" then suffix else (name::suffix))
  else
    let subdir = Filename.dirname dirname in
    if subdir = dirname then raise Not_found
    else name_of_path p name subdir (Filename.basename dirname::suffix)


let coq_module filename =
  let bfname = Filename.chop_extension filename in
  let dirname, fname = normalize_filename bfname in
  let _ = match Unicode.ident_refutation fname with
    | Some err -> raise (Arg.Bad (Printf.sprintf "Not a valid filename: %s" fname))
    | None -> () in
  let rec change_prefix = function
    (* Follow coqc: if in scope of -R, substitute logical name *)
    (* otherwise, keep only base name *)
    | [] -> fname
    | (p, name) :: rem ->
        try name_of_path p name dirname [fname]
        with Not_found -> change_prefix rem
  in
  change_prefix !prefs.paths

let what_file f =
  FileUtil.check_if_file_exists f;
  if Filename.check_suffix f ".v" || Filename.check_suffix f ".g" then
    Vernac_file (f, coq_module f)
  else if Filename.check_suffix f ".tex" then
    Latex_file f
  else
     raise (Arg.Bad (Printf.sprintf "Expected a .v, .g, or .tex file: %s" f))

let arg_set f = Arg.Unit (fun () -> prefs := f !prefs)
let arg_string f = Arg.String (fun s -> prefs := f !prefs s)
let arg_file f = Arg.String (fun s -> FileUtil.check_if_file_exists s; prefs := f !prefs s)
let arg_int f = Arg.Int (fun d -> prefs := f !prefs d)
let arg_path f = Arg.Rest_all (fun l ->
  match l with
  | dir :: name :: [] -> prefs := f !prefs (normalize_path dir, name)
  | _ -> raise (Arg.Bad ("Two arguments expected: <dir> and <name>")))
let arg_url_path f = Arg.Rest_all (fun l ->
  match l with
  | url :: path :: [] -> f path url
  | _ -> raise (Arg.Bad ("Two arguments expected: <url> and <path>")))

let args_options = Arg.align [
  "--html", arg_set (fun p -> { p with targetlang = HTML }),
  "produce a HTML document (default)";
  "--latex", arg_set (fun p -> { p with targetlang = LaTeX }),
  "produce a LaTeX document";
  "--texmacs",arg_set (fun p -> { p with targetlang = TeXmacs }),
  "produce a TeXmacs document";
  "--raw", arg_set (fun p -> { p with targetlang = Raw }),
  "produce a text document";
  "--dvi", arg_set (fun p -> { { p with targetlang = LaTeX }
                              with compile_targets = LatexCompiler.Dvi :: !prefs.compile_targets }),
  "output the DVI";
  "--ps", arg_set (fun p -> { { p with targetlang = LaTeX }
                               with compile_targets = LatexCompiler.Ps :: !prefs.compile_targets }),
  "output the PostScript";
  "--pdf", arg_set (fun p -> { { p with targetlang = LaTeX }
                              with compile_targets = LatexCompiler.Pdf :: !prefs.compile_targets }),
  "output the Pdf";
  "--stdout", arg_set (fun p -> { p with out_to = StdOut }),
  "write output to stdout";
  "-o", arg_string (fun p f -> { { p with out_to = File (Filename.basename f) }
                            with output_dir = Filename.dirname f }),
  "<file> write output to file <file>";
  "-d", arg_string (fun p f -> { p with output_dir = f }),
  "<dir> output files into directory <dir>";
  "-g", arg_set (fun p -> { p with gallina = true }),
  "(gallina) skip proofs";
  "-s", arg_set (fun p -> { p with short = true }),
  "(short) no titles for files";
  "-l", arg_set (fun p -> { { p with gallina = true } with light = true }),
  "light mode (only defs and statements)";
  "-t", arg_string (fun p s -> { p with title = s }),
  "<string> give a title to the document";
  "--body-only", arg_set (fun p -> { p with header_trailer = false }),
  "suppress LaTeX/HTML header and trailer";
  "--with-header", arg_file (fun p f -> { p with header_trailer = true;
                                                 header_file_spec = true;
                                                 header_file = f }),
  "<file> prepend <file> as html reader";
  "--with-footer", arg_file (fun p f -> { p with header_trailer = true;
                                                 footer_file_spec = true;
                                                 footer_file = f }),
  "<file> append <file> as html footer";
  "--no-index", arg_set (fun p -> { p with index = false }),
  "do not output the index";
  "--multi-index", arg_set (fun p -> { p with multi_index = true }),
  "index split in multiple files";
  "--index <string>", arg_string (fun p s -> { p with index_name = s }),
  "set index name (default is index)";
  "--toc", arg_set (fun p -> { p with toc = true }),
  "output a table of contents";
  "--vernac-file",
  arg_file (fun p f -> { p with files = Vernac_file (f, coq_module f) :: !prefs.files }),
  "<file> consider <file> as a .v file";
  "--tex-file", arg_file (fun p f -> { p with files =  Latex_file f :: !prefs.files }),
  "<file> consider <file> as a .tex file";
  "-p", Arg.String (fun f -> Output.push_in_preamble f),
  "<string> insert <string> in LaTeX preamble";
  "--files-from", arg_file (fun p f -> { p with
    files = List.append (List.map what_file (FileUtil.files_from_file f)) !prefs.files }),
  "<file>  read file names to process in <file>";
  "--glob-from", arg_file (fun p f -> { p with glob_source = GlobFile f }),
  "<file> read globalization information from <file>";
  "--no-glob", arg_set (fun p -> { p with glob_source = NoGlob }),
  "don't use any globalization information (no links will be inserted at identifiers)";
  "--quiet", arg_set (fun p -> { p with quiet = true }), "quiet mode (default)";
  "--verbose", arg_set (fun p -> { p with quiet = false }), "verbose mode";
  "--no-externals", arg_set (fun p -> { p with externals = false }),
  "no links to Coq standard library";
  "--external", arg_url_path Index.add_external_library,
  "<url> <d> set URL for external library <d>";
  "--coqlib_url", arg_string (fun p u -> { p with coqlib_url = u }),
  "<url> set URL for Coq standard library (default: " ^ Coq_config.wwwstdlib ^ ")";
  "--coqlib", Arg.String (fun d -> Boot.Env.set_coqlib d),
  "<dir> set the path where Coq files are installed";
  "-R", arg_path (fun p l -> { p with paths = l :: !prefs.paths }),
  "<dir> <coqdir> map physical dir to Coq dir";
  "-Q", arg_path (fun p l -> { p with paths = l :: !prefs.paths }),
  "<dir> <coqdir> map physical dir to Coq dir";
  "--latin1", arg_set (fun p -> {p with encoding = { charset = "iso-8859-1";
                                                     inputenc = "latin1";
                                                     latin1 = true;
                                                     utf8 = false } }),
  "set ISO-8859-1 mode";
  "--utf8", arg_set (fun p -> {p with encoding = { charset = "utf-8";
                                                   inputenc = "utf8x";
                                                   latin1 = false;
                                                   utf8 = true } }),
  "set UTF-8 mode";
  "--charset", arg_string (fun p s -> { p with encoding = { !prefs.encoding with charset = s } }),
   "<string> set HTML charset";
  "--inputenc", arg_string (fun p s -> { p with encoding = { !prefs.encoding with inputenc = s } }),
  "<string> set LaTeX input encoding";
  "--interpolate", arg_set (fun p -> {p with interpolate = true }),
  "try to typeset identifiers in comments using definitions in the same module";
  "--parse-comments", arg_set (fun p -> {p with parse_comments = true }),
  "parse regular comments";
  "--plain-comments", arg_set (fun p -> {p with plain_comments = true }),
  "consider comments as non-literate text";
  "--toc-depth", arg_int (fun p d -> { p with toc_depth = Some d }),
  "<int> don't include TOC entries for sections below level <int>";
  "--no-lib-name", arg_set (fun p -> { p with lib_name = "" }),
  "don't display \"Library\" before library names in the toc";
  "--lib-name", arg_string (fun p s -> { p with lib_name = s }),
  "<string> call top level toc entries <string> instead of \"Library\"";
  "--lib-subtitles", arg_set (fun p -> { p with lib_subtitles = true }),
  "first line comments of the form (** * ModuleName : text *) will be interpreted as subtitles";
  "--inline-notmono", arg_set (fun p -> { p with inline_notmono = true }),
  "use a proportional width font for inline code (possibly with a different color)";
];
