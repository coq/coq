(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util

(** * Command-line parsing *)

type ide = Opt | Byte | No

type nativecompiler = NativeYes | NativeNo | NativeOndemand

module Prefs = struct

type t = {
  prefix : string option;
  interactive : bool;
  output_summary : bool;
  vmbyteflags : string option;
  custom : bool option;
  libdir : string option;
  configdir : string option;
  datadir : string option;
  mandir : string option;
  docdir : string option;
  ocamlfindcmd : string option;
  arch : string option;
  natdynlink : bool;
  coqide : ide option;
  macintegration : bool;
  browser : string option;
  withdoc : bool;
  byteonly : bool;
  flambda_flags : string list;
  debug : bool;
  profile : bool;
  bin_annot : bool;
  annot : bool;
  bytecodecompiler : bool;
  nativecompiler : nativecompiler;
  coqwebsite : string;
  force_caml_version : bool;
  force_findlib_version : bool;
  warn_error : bool;
  dune_profile : string;
  install_enabled : bool;
}

end

open Prefs

module Profiles = struct

let default = {
  prefix = None;
  interactive = true;
  output_summary = true;
  vmbyteflags = None;
  custom = None;
  libdir = None;
  configdir = None;
  datadir = None;
  mandir = None;
  docdir = None;
  ocamlfindcmd = None;
  arch = None;
  natdynlink = true;
  coqide = None;
  macintegration = true;
  browser = None;
  withdoc = false;
  byteonly = false;
  flambda_flags = [];
  debug = true;
  profile = false;
  bin_annot = false;
  annot = false;
  bytecodecompiler = true;
  nativecompiler =
    if os_type_win32 || os_type_cygwin then NativeNo else NativeOndemand;
  coqwebsite = "http://coq.inria.fr/";
  force_caml_version = false;
  force_findlib_version = false;
  warn_error = false;
  dune_profile = "release";
  install_enabled = true;
}

let devel state = { state with
  bin_annot = true;
  annot = true;
  warn_error = true;
  dune_profile = "dev";
  interactive = false;
  output_summary = true;
  prefix = Some (Filename.concat (Sys.getcwd ()) "_build_vo/default");
  install_enabled = false;
}

let devel_doc = "-annot -bin-annot -warn-error yes"

let get = function
  | "devel" -> devel
  | s -> raise (Arg.Bad ("profile name expected instead of "^s))

let doc =
  "<profile> Sets a bunch of flags. Supported profiles:
     devel = " ^ devel_doc

end

let get_bool = function
  | "true" | "yes" | "y" | "all" -> true
  | "false" | "no" | "n" -> false
  | s -> raise (Arg.Bad ("boolean argument expected instead of "^s))

let get_ide = function
  | "opt" -> Opt
  | "byte" -> Byte
  | "no" -> No
  | s -> raise (Arg.Bad ("(opt|byte|no) argument expected instead of "^s))

let get_native = function
  | "yes" -> NativeYes
  | "no" -> NativeNo
  | "ondemand" -> NativeOndemand
  | s -> raise (Arg.Bad ("(yes|no|ondemand) argument expected instead of "^s))

let prefs = ref Profiles.default

let arg_bool f = Arg.String (fun s -> prefs := f !prefs (get_bool s))

let arg_string f = Arg.String (fun s -> prefs := f !prefs s)
let arg_string_option f = Arg.String (fun s -> prefs := f !prefs (Some s))
let arg_string_list c f = Arg.String (fun s -> prefs := f !prefs (string_split c s))

let arg_set f = Arg.Unit (fun () -> prefs := f !prefs)

let arg_set_option f = Arg.Unit (fun () -> prefs := f !prefs (Some true))
let arg_clear_option f = Arg.Unit (fun () -> prefs := f !prefs (Some false))

let arg_ide f = Arg.String (fun s -> prefs := f !prefs (Some (get_ide s)))

let arg_native f = Arg.String (fun s -> prefs := f !prefs (get_native s))

let arg_profile = Arg.String (fun s -> prefs := Profiles.get s !prefs)

(* TODO : earlier any option -foo was also available as --foo *)

let check_absolute = function
  | None -> ()
  | Some path ->
    if Filename.is_relative path then
      die "argument to -prefix must be an absolute path"
    else ()

let local_warning () = warn "-local option is deprecated, and equivalent to -profile devel"
let bindir_warning () = warn "-bindir option is deprecated, Coq will now unconditionally use $prefix/bin"
let coqdocdir_warning () = warn "-coqdordir option is deprecated, Coq will now unconditionally use $datadir/texmf/tex/latex/misc/ to install coqdoc sty files"

let args_options = Arg.align [
  "-prefix", arg_string_option (fun p prefix -> check_absolute prefix; { p with prefix }),
    "<dir> Set installation directory to <dir> (absolute path required)";
  "-local", arg_set (fun p -> local_warning (); Profiles.get "devel" p), "Deprecated option, equivalent to -profile devel";
  "-no-ask", arg_set (fun p -> { p with interactive = false; output_summary = false }),
    " Don't ask questions / print variables during configure [questions will be filled with defaults]";
  "-vmbyteflags", arg_string_option (fun p vmbyteflags -> { p with vmbyteflags }),
    "<flags> Comma-separated link flags for the VM of coqtop.byte";
  "-custom", arg_set_option (fun p custom -> { p with custom }),
    " Build bytecode executables with -custom (not recommended)";
  "-no-custom", arg_clear_option (fun p custom -> { p with custom }),
    " Do not build with -custom on Windows and MacOS";
  "-bindir", arg_string_option (fun p _ -> bindir_warning (); p ),
    "<dir> Where to install bin files";
  "-libdir", arg_string_option (fun p libdir -> { p with libdir }),
    "<dir> Where to install lib files";
  "-configdir", arg_string_option (fun p configdir -> { p with configdir }),
    "<dir> Where to install config files";
  "-datadir", arg_string_option (fun p datadir -> { p with datadir }),
    "<dir> Where to install data files";
  "-mandir", arg_string_option (fun p mandir -> { p with mandir }),
    "<dir> Where to install man files";
  "-docdir", arg_string_option (fun p docdir -> { p with docdir }),
    "<dir> Where to install doc files";
  "-coqdocdir", arg_string_option (fun p _ -> coqdocdir_warning (); p),
    "<dir> Where to install Coqdoc style files";
  "-ocamlfind", arg_string_option (fun p ocamlfindcmd -> { p with ocamlfindcmd }),
    "<dir> Specifies the ocamlfind command to use";
  "-flambda-opts", arg_string_list ' ' (fun p flambda_flags -> { p with flambda_flags }),
    "<flags> Specifies additional flags to be passed to the flambda optimizing compiler";
  "-arch", arg_string_option (fun p arch -> { p with arch }),
    "<arch> Specifies the architecture";
  "-natdynlink", arg_bool (fun p natdynlink -> { p with natdynlink }),
    "(yes|no) Use dynamic loading of native code or not";
  "-coqide", arg_ide (fun p coqide -> { p with coqide }),
    "(opt|byte|no) Specifies whether or not to compile CoqIDE";
  "-nomacintegration", arg_set (fun p -> { p with macintegration = false}),
    " Do not try to build CoqIDE MacOS integration";
  "-browser", arg_string_option (fun p browser -> { p with browser }),
    "<command> Use <command> to open URL %s";
  "-with-doc", arg_bool (fun p withdoc -> { p with withdoc }),
    "(yes|no) Compile the documentation or not";
  "-byte-only", arg_set (fun p -> { p with byteonly = true }),
    " Compiles only bytecode version of Coq";
  "-nodebug", arg_set (fun p -> { p with debug = true }),
    " Do not add debugging information in the Coq executables";
  "-profiling", arg_set (fun p -> { p with profile = true }),
    " Add profiling information in the Coq executables";
  "-annotate", Arg.Unit (fun () -> die "-annotate has been removed. Please use -annot or -bin-annot instead."),
    " Removed option. Please use -annot or -bin-annot instead";
  "-annot", arg_set (fun p -> { p with annot = true }),
    " Dumps ml text annotation files while compiling Coq (e.g. for Tuareg)";
  "-bin-annot", arg_set (fun p -> { p with bin_annot = true }),
    " Dumps ml binary annotation files while compiling Coq (e.g. for Merlin)";
  "-bytecode-compiler", arg_bool (fun p bytecodecompiler -> { p with bytecodecompiler }),
    "(yes|no) Enable Coq's bytecode reduction machine (VM)";
  "-native-compiler", arg_native (fun p nativecompiler -> { p with nativecompiler }),
    "(yes|no|ondemand) Compilation to native code for conversion and normalization
     yes: -native-compiler option of coqc will default to 'yes', stdlib will be precompiled
     no: no native compilation available at all
     ondemand (default): -native-compiler option of coqc will default to 'ondemand', stdlib will not be precompiled";
  "-coqwebsite", arg_string (fun p coqwebsite -> { p with coqwebsite }),
    " URL of the coq website";
  "-force-caml-version", arg_set (fun p -> { p with force_caml_version = true}),
    " Force OCaml version";
  "-force-findlib-version", arg_set (fun p -> { p with force_findlib_version = true}),
    " Force findlib version";
  "-warn-error", arg_bool (fun p warn_error -> { p with warn_error }),
    "(yes|no) Make OCaml warnings into errors (default no)";
  "-camldir", Arg.String (fun _ -> ()),
    "<dir> Specifies path to 'ocaml' for running configure script";
  "-profile", arg_profile,
    Profiles.doc
]

let parse_args () =
  Arg.parse
    args_options
    (fun s -> raise (Arg.Bad ("Unknown option: "^s)))
    "Available options for configure are:";
  !prefs
