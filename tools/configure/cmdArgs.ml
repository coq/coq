(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util

(** * Command-line parsing *)

type nativecompiler = NativeYes | NativeNo | NativeOndemand

module Prefs = struct

type t = {
  prefix : string option;
  quiet : bool;
  interactive : bool;
  libdir : string option;
  configdir : string option;
  datadir : string option;
  mandir : string option;
  docdir : string option;
  arch : string option;
  natdynlink : bool;
  browser : string option;
  bytecodecompiler : bool;
  nativecompiler : nativecompiler;
  coqwebsite : string;
  debug : bool;
}

end

open Prefs

let default_prefs = {
  prefix = None;
  quiet = false;
  interactive = true;
  libdir = None;
  configdir = None;
  datadir = None;
  mandir = None;
  docdir = None;
  arch = None;
  natdynlink = true;
  browser = None;
  bytecodecompiler = true;
  nativecompiler = NativeNo;
  coqwebsite = "http://coq.inria.fr/";
  debug = false;
}

let get_bool = function
  | "true" | "yes" | "y" | "all" -> true
  | "false" | "no" | "n" -> false
  | s -> raise (Arg.Bad ("boolean argument expected instead of "^s))

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

let arg_native f = Arg.String (fun s -> prefs := f !prefs (get_native s))

(* TODO : earlier any option -foo was also available as --foo *)

let warn_warn_error () =
  Format.eprintf "****** the -warn-error option is deprecated, \
                  warnings are not set in the config section of the \
                  corresponding build tool [coq_makefile, dune]@\n%!"

let make_absolute = function
  | None -> None
  | Some path ->
    if Filename.is_relative path then
      Some (Sys.getcwd() ^ "/" ^ path)
    else Some path

let args_options = Arg.align [
  "-prefix", arg_string_option (fun p prefix -> { p with prefix = make_absolute prefix }),
    "<dir> Set installation directory to <dir>";
  "-quiet", arg_set (fun p -> { p with quiet = true }),
    " Don't print variables during configure";
  "-no-ask", arg_set (fun p -> { p with interactive = false }),
    " Don't ask questions during configure [questions will be filled with defaults]";
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
  "-browser", arg_string_option (fun p browser -> { p with browser }),
    "<command> Use <command> to open URL %s";
  "-bytecode-compiler", arg_bool (fun p bytecodecompiler -> { p with bytecodecompiler }),
    "(yes|no) Enable Rocq's bytecode reduction machine (VM)";
  "-native-compiler", arg_native (fun p nativecompiler -> { p with nativecompiler }),
    "(yes|no|ondemand) Compilation to native code for conversion and normalization
     yes: -native-compiler option of coqc will default to 'yes', stdlib will be precompiled
     no (default): no native compilation available at all
     ondemand: -native-compiler option of coqc will default to 'ondemand', stdlib will not be precompiled";
  "-warn-error", arg_bool (fun p _warn_error -> warn_warn_error (); p),
    "Deprecated option: warnings are now adjusted in the corresponding build tool.";
  "-coqwebsite", arg_string (fun p coqwebsite -> { p with coqwebsite }),
    " URL of the rocq website";
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
  if not prefs.quiet
  then cprintf x
  else Printf.ifprintf stdout x
