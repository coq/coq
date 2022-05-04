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
  libdir : string option;
  configdir : string option;
  datadir : string option;
  mandir : string option;
  docdir : string option;
  arch : string option;
  natdynlink : bool;
  coqide : ide option;
  macintegration : bool;
  browser : string option;
  withdoc : bool;
  bin_annot : bool;
  annot : bool;
  bytecodecompiler : bool;
  nativecompiler : nativecompiler;
  coqwebsite : string;
  warn_error : bool;
  debug : bool;
}

end

open Prefs

let default_prefs = {
  prefix = None;
  interactive = true;
  libdir = None;
  configdir = None;
  datadir = None;
  mandir = None;
  docdir = None;
  arch = None;
  natdynlink = true;
  coqide = None;
  macintegration = true;
  browser = None;
  withdoc = false;
  bin_annot = false;
  annot = false;
  bytecodecompiler = true;
  nativecompiler =
    if os_type_win32 || os_type_cygwin then NativeNo else NativeOndemand;
  coqwebsite = "http://coq.inria.fr/";
  warn_error = false;
  debug = false;
}

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

let prefs = ref default_prefs

let arg_bool f = Arg.String (fun s -> prefs := f !prefs (get_bool s))

let arg_string f = Arg.String (fun s -> prefs := f !prefs s)
let arg_string_option f = Arg.String (fun s -> prefs := f !prefs (Some s))

let arg_set f = Arg.Unit (fun () -> prefs := f !prefs)

let arg_ide f = Arg.String (fun s -> prefs := f !prefs (Some (get_ide s)))

let arg_native f = Arg.String (fun s -> prefs := f !prefs (get_native s))

(* TODO : earlier any option -foo was also available as --foo *)

let check_absolute = function
  | None -> ()
  | Some path ->
    if Filename.is_relative path then
      die "argument to -prefix must be an absolute path"
    else ()

let args_options = Arg.align [
  "-prefix", arg_string_option (fun p prefix -> check_absolute prefix; { p with prefix }),
    "<dir> Set installation directory to <dir> (absolute path required)";
  "-no-ask", arg_set (fun p -> { p with interactive = false }),
    " Don't ask questions / print variables during configure [questions will be filled with defaults]";
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
  "-warn-error", arg_bool (fun p warn_error -> { p with warn_error }),
    "(yes|no) Make OCaml warnings into errors (default no)";
  "-debug", arg_set (fun p -> { p with debug = true }), " Enable debug information for package detection"
]

let parse_args () =
  Arg.parse
    args_options
    (fun s -> raise (Arg.Bad ("Unknown option: "^s)))
    "Available options for configure are:";
  !prefs

(* Support don't ask *)
let cprintf prefs x =
  if prefs.interactive
  then cprintf x
  else Printf.ifprintf stdout x
