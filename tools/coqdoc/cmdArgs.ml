(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Command-line argument parsing *)
open Common

let banner () =
  Printf.eprintf "This is rocq doc version %s\n" Coq_config.version;
  flush stderr

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

let current = Arg.current

let argv = ref [||]

(* TODO: replace these hacks with Arg.Rest_all, when rocq moves to a newer version of OCaml stdlib *)
let arg_path f = Arg.String (fun s ->
  if Array.length !argv < !current + 3 ||
    CString.is_prefix "-" !argv.(!current + 2) then
    raise (Arg.Bad ("Two arguments expected: <dir> and <name>"))
  else
    Arg.current := !current + 1;
    prefs := f !prefs (normalize_path s, !argv.(!current + 1)))
let arg_url_path f = Arg.String (fun s ->
  if Array.length !argv < !current + 3 ||
    CString.is_prefix "-" !argv.(!current + 2) then
    raise (Arg.Bad ("Two arguments expected: <url> and <path>"))
  else
    current := !current + 1;
    f s !argv.(!current + 1))

let args_options = Arg.align [
  "--html", arg_set (fun p -> { p with targetlang = HTML }),
  " Produce a HTML document (default)";
  "--latex", arg_set (fun p -> { p with targetlang = LaTeX }),
  " Produce a LaTeX document";
  "--texmacs",arg_set (fun p -> { p with targetlang = TeXmacs }),
  " Produce a TeXmacs document";
  "--raw", arg_set (fun p -> { p with targetlang = Raw }),
  " Produce a text document";
  "--dvi", arg_set (fun p -> { { p with targetlang = LaTeX }
                              with compile_targets = Dvi :: !prefs.compile_targets }),
  " Output the DVI";
  "--ps", arg_set (fun p -> { { p with targetlang = LaTeX }
                               with compile_targets = Ps :: !prefs.compile_targets }),
  " Output the PostScript";
  "--pdf", arg_set (fun p -> { { p with targetlang = LaTeX }
                              with compile_targets = Pdf :: !prefs.compile_targets }),
  " Output the Pdf";
  "--stdout", arg_set (fun p -> { p with out_to = StdOut }),
  " Write output to stdout";
  "-o", arg_string (fun p f -> { { p with out_to = File (Filename.basename f) }
                            with output_dir = Filename.dirname f }),
  "<file> Write output to file <file>";
  "--output", arg_string (fun p f -> { { p with out_to = File (Filename.basename f) }
                          with output_dir = Filename.dirname f }),
  "<file> Write output to file <file>";
  "-d", arg_string (fun p f -> { p with output_dir = f }),
  "<dir> Output files into directory <dir>";
  "--directory", arg_string (fun p f -> { p with output_dir = f }),
  "<dir> Output files into directory <dir>";
  "-g", arg_set (fun p -> { p with gallina = true }),
  " Skip proofs (gallina)";
  "--gallina", arg_set (fun p -> { p with gallina = true }),
  " Skip proofs";
  "-s", arg_set (fun p -> { p with short = true }),
  " No titles for files (short)";
  "--short", arg_set (fun p -> { p with short = true }),
  " No titles for files";
  "-l", arg_set (fun p -> { { p with gallina = true } with light = true }),
  " Light mode (only defs and statements)";
  "--light", arg_set (fun p -> { { p with gallina = true } with light = true }),
  " Light mode (only defs and statements)";
  "-t", arg_string (fun p s -> { p with title = s }),
  "<string> Give a title to the document";
  "--title", arg_string (fun p s -> { p with title = s }),
  "<string> Give a title to the document";
  "--body-only", arg_set (fun p -> { p with header_trailer = false }),
  " Suppress LaTeX/HTML header and trailer";
  "--no-preamble", arg_set (fun p -> { p with header_trailer = false }),
  " Suppress LaTeX/HTML header and trailer";
  "--with-header", arg_file (fun p f -> { p with header_trailer = true;
                                                 header_file_spec = true;
                                                 header_file = f }),
  "<file> Prepend <file> as html header";
  "--with-footer", arg_file (fun p f -> { p with header_trailer = true;
                                                 footer_file_spec = true;
                                                 footer_file = f }),
  "<file> append <file> as html footer";
  "--no-index", arg_set (fun p -> { p with index = false }),
  " Do not output the index";
  "--binder-index", arg_set (fun p -> { p with binder_index = true }),
  " Include variable binders in index";
  "--multi-index", arg_set (fun p -> { p with multi_index = true }),
  " Index split in multiple files";
  "--index", arg_string (fun p s -> { p with index_name = s }),
  "<string> Set index name to <string> (default is index)";
  "--toc", arg_set (fun p -> { p with toc = true }),
  " Output a table of contents";
  "--table-of-contents", arg_set (fun p -> { p with toc = true }),
  " Output a table of contents";
  "--vernac-file",
  arg_file (fun p f -> { p with files = Vernac_file (f, coq_module f) :: !prefs.files }),
  "<file> consider <file> as a .v file";
  "--tex-file", arg_file (fun p f -> { p with files =  Latex_file f :: !prefs.files }),
  "<file> Consider <file> as a .tex file";
  "-p", Arg.String (fun f -> Output.push_in_preamble f),
  "<string> Insert <string> in LaTeX preamble";
  "--preamble", Arg.String (fun f -> Output.push_in_preamble f),
  "<string> Insert <string> in LaTeX preamble";
  "--files-from", arg_file (fun p f -> { p with
    files = List.append (List.map what_file (FileUtil.files_from_file f)) !prefs.files }),
  "<file> Read file names to process in <file>";
  "--files", arg_file (fun p f -> { p with
    files = List.append (List.map what_file (FileUtil.files_from_file f)) !prefs.files }),
  "<file> Read file names to process in <file>";
  "--glob-from", arg_file (fun p f -> { p with glob_source = GlobFile f }),
  "<file> Read globalization information from <file>";
  "--no-glob", arg_set (fun p -> { p with glob_source = NoGlob }),
  " Don't use any globalization information (no links will be inserted at identifiers)";
  "-q", arg_set (fun p -> { p with quiet = true }), " Quiet mode (default)";
  "--quiet", arg_set (fun p -> { p with quiet = true }), " Quiet mode (default)";
  "--verbose", arg_set (fun p -> { p with quiet = false }), " Verbose mode";
  "--no-externals", arg_set (fun p -> { p with externals = false }),
  " No links to Rocq standard library";
  "--external", arg_url_path (fun url lp -> Index.add_external_library lp url),
  "<url>+<d> set URL for external library <d>";
  "--coqlib_url", arg_string (fun p u -> { p with coqlib_url = u }),
  "<url> Set URL for Rocq standard library (default: " ^ Coq_config.wwwstdlib ^ ")";
  "--coqlib", Arg.String (fun d -> Boot.Env.set_coqlib d),
  "<dir> Set the path where Rocq files are installed";
  "-R", arg_path (fun p l -> { p with paths = l :: !prefs.paths }),
  "<dir>+<coqdir> map physical dir to Rocq dir";
  "-Q", arg_path (fun p l -> { p with paths = l :: !prefs.paths }),
  "<dir>+<coqdir> Map physical dir to Rocq dir";
  "--latin1", arg_set (fun p -> {p with encoding = { charset = "iso-8859-1";
                                                     inputenc = "latin1";
                                                     latin1 = true;
                                                     utf8 = false } }),
  " Set ISO-8859-1 mode";
  "--utf8", arg_set (fun p -> {p with encoding = { charset = "utf-8";
                                                   inputenc = "utf8x";
                                                   latin1 = false;
                                                   utf8 = true } }),
  " Set UTF-8 mode";
  "--charset", arg_string (fun p s -> { p with encoding = { !prefs.encoding with charset = s } }),
   "<string> Set HTML charset";
  "--inputenc", arg_string (fun p s -> { p with encoding = { !prefs.encoding with inputenc = s } }),
  "<string> Set LaTeX input encoding";
  "--interpolate", arg_set (fun p -> {p with interpolate = true }),
  " Try to typeset identifiers in comments using definitions in the same module";
  "--raw-comments", arg_set (fun p -> {p with raw_comments = true }),
  " Raw comments";
  "--parse-comments", arg_set (fun p -> {p with parse_comments = true }),
  " Parse regular comments";
  "--plain-comments", arg_set (fun p -> {p with plain_comments = true }),
  " Consider comments as non-literate text";
  "--toc-depth", arg_int (fun p d -> { p with toc_depth = Some d }),
  "<int> Don't include TOC entries for sections below level <int>";
  "--no-lib-name", arg_set (fun p -> { p with lib_name = "" }),
  " Don't display \"Library\" before library names in the toc";
  "--lib-name", arg_string (fun p s -> { p with lib_name = s }),
  "<string> Call top level toc entries <string> instead of \"Library\"";
  "--lib-subtitles", arg_set (fun p -> { p with lib_subtitles = true }),
  " First line comments of the form (** * ModuleName : text *) will be interpreted as subtitles";
  "--inline-notmono", arg_set (fun p -> { p with inline_notmono = true }),
  " Use a proportional width font for inline code (possibly with a different color)";
  "--version", Arg.Unit (fun () -> banner()), " Display rocq doc version";
]

let add_input_files f = prefs := { !prefs with files = what_file f :: !prefs.files }
let usage_msg = "rocq doc [options] <input file>...\nAvailable options are:"

let single_hyphen_opts =
  ["-html"; "-latex"; "-texmacs"; "-raw"; "-dvi"; "-ps"; "-pdf"; "-stdout"; "-output"; "-directory"; "-gallina"; "-short"; "-light"; "-title"; "-body-only"; "-no-preamble"; "-with-header"; "-with-footer"; "-no-index"; "-multi-index"; "-index"; "-toc"; "-table-of-contents"; "-vernac-file"; "-tex-file"; "-preamble"; "-files-from"; "-files"; "-glob-from"; "-no-glob"; "-quiet"; "-verbose"; "-no-externals"; "-external"; "-coqlib_url"; "-coqlib"; "-latin1"; "-utf8"; "-charset"; "-inputenc"; "-interpolate"; "-raw-comments"; "-parse-comments"; "-plain-comments"; "-toc-depth"; "-no-lib-name"; "-lib-name"; "-lib-subtitles"; "-inline-notmono"; "-version"]

let deprecated_mapper_opts =
  [("-noindex", "--no-index"); ("-nopreamble", "--no-preamble"); ("-noexternals", "--no-externals"); ("-V", "--version")]

let translate_arg s =
  match List.find_opt (fun m -> m = s) single_hyphen_opts with
  | Some _ -> Printf.sprintf "-%s" s
  | None -> (match List.assoc_opt s deprecated_mapper_opts with
      | Some b -> b
      | None -> s)

let parse_args ~prog args =
(* Deprecated options *)
  let new_argv = List.map translate_arg args in
  let new_argv = Array.of_list (prog::new_argv) in
  argv := new_argv;
  current := 0;
  try
    Arg.parse_argv new_argv args_options add_input_files usage_msg
  with
  | Arg.Bad s -> Printf.eprintf "%s" s
  | Arg.Help s -> Printf.printf "%s" s
