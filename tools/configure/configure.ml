(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(**********************************)
(**  Configuration script for Coq *)
(**********************************)
open Printf
open Conf
open Util
open CmdArgs
open CmdArgs.Prefs

let (/) = Filename.concat

let coq_version = "8.16+alpha"
let vo_magic = 81591
let is_a_released_version = false

(** Default OCaml binaries *)

type camlexec = { mutable find : string }
let camlexec = { find = "ocamlfind" }

let reset_caml_find c o = c.find <- o

let coq_annot_flag prefs = if prefs.annot then "-annot" else ""
let coq_bin_annot_flag prefs = if prefs.bin_annot then "-bin-annot" else ""

(* This variable can be overridden only for debug purposes, use with
   care. *)
let coq_safe_string = "-safe-string"
let coq_strict_sequence = "-strict-sequence"

(* Query for the architecture *)
let arch prefs = arch prefs.arch

(** NB: [arch_is_win32] is broader than [os_type_win32], cf. cygwin *)

let arch_is_win32 arch = arch = "win32"

let resolve_binary_suffix arch = if arch_is_win32 arch then ".exe" else ""

(** * Git Precommit Hook *)
let install_precommit_hook prefs =
  let f = ".git/hooks/pre-commit" in
  if dir_exists ".git/hooks" && not (Sys.file_exists f) then begin
    cprintf prefs "Creating pre-commit hook in %s" f;
    let o = open_out f in
    let pr s = fprintf o s in
    pr "#!/bin/sh\n";
    pr "\n";
    pr "if [ -x dev/tools/pre-commit ]; then\n";
    pr "    exec dev/tools/pre-commit\n";
    pr "fi\n";
    close_out o;
    Unix.chmod f 0o775
  end

(** * Browser command *)

let browser prefs arch =
  match prefs.browser with
  | Some b -> b
  | None when arch_is_win32 arch -> "start %s"
  | None when arch = "Darwin" -> "open %s"
  | _ -> "firefox -remote \"OpenURL(%s,new-tab)\" || firefox %s &"

(** * OCaml programs *)
module CamlConf = struct
  type t =
    { camlbin : string
    ; caml_version : string
    ; camllib : string
    ; findlib_version : string
    }
end

let resolve_caml prefs =
  let () =
    try reset_caml_find camlexec (which camlexec.find)
    with Not_found ->
      die (sprintf "Error: cannot find '%s' in your path!\n" camlexec.find ^
           "Please adjust your path or use the -ocamlfind option of ./configure")
  in
  if not (is_executable camlexec.find)
  then die ("Error: cannot find the executable '"^camlexec.find^"'.")
  else
    let findlib_version, _ = run camlexec.find ["query"; "findlib"; "-format"; "%v"] in
    let caml_version, _ = run camlexec.find ["ocamlc";"-version"] in
    let camllib, _ = run camlexec.find ["printconf";"stdlib"] in
    let camlbin = (* TODO beurk beurk beurk *)
      Filename.dirname (Filename.dirname camllib) / "bin/" in
    { CamlConf.camlbin; caml_version; camllib; findlib_version }

(** Caml version as a list of ints [4;0;1] *)
let caml_version_nums { CamlConf.caml_version } =
  generic_version_nums ~name:"the OCaml compiler" caml_version

let check_caml_version prefs caml_version caml_version_nums =
  if caml_version_nums >= [4;5;0] then
    cprintf prefs "You have OCaml %s. Good!" caml_version
  else
    let () = cprintf prefs "Your version of OCaml is %s." caml_version in
    die "You need OCaml 4.05.0 or later."

let check_findlib_version prefs { CamlConf.findlib_version } =
  let findlib_version_nums = generic_version_nums ~name:"findlib" findlib_version in
  if findlib_version_nums >= [1;8;0] then
    cprintf prefs "You have OCamlfind %s. Good!" findlib_version
  else
    let () = cprintf prefs "Your version of OCamlfind is %s." findlib_version in
    die "You need OCamlfind 1.8.0 or later."

(** Note, these warnings are only used in Coq Makefile *)
(** Explanation of enabled/disabled warnings:
    4: fragile pattern matching: too common in the code and too annoying to avoid in general
    9: missing fields in a record pattern: too common in the code and not worth the bother
    27: innocuous unused variable: innocuous
    41: ambiguous constructor or label: too common
    42: disambiguated counstructor or label: too common
    44: "open" shadowing already defined identifier: too common, especially when some are aliases
    45: "open" shadowing a label or constructor: see 44
    48: implicit elimination of optional arguments: too common
    58: "no cmx file was found in path": See https://github.com/ocaml/num/issues/9
    67: "unused functor parameter" seems totally bogus
    68: "This pattern depends on mutable state" no idea what it means, dune builds don't display it
    70: ".ml file without .mli file" bogus warning when used generally
*)

(* Note, we list all warnings to be complete *)
let coq_warnings = "-w -a+1..3-4+5..8-9+10..26-27+28..40-41-42+43-44-45+46..47-48+49..57-58+59..66-67-68+69-70"
let coq_warn_error prefs =
    if prefs.warn_error
    then "-warn-error +a"
    else ""

(* Flags used to compile Coq and plugins (via coq_makefile) *)
let caml_flags coq_annot_flag coq_bin_annot_flag =
  Printf.sprintf "-thread -rectypes %s %s %s %s %s" coq_warnings coq_annot_flag coq_bin_annot_flag coq_safe_string coq_strict_sequence

(* Flags used to compile Coq but _not_ plugins (via coq_makefile) *)
let coq_caml_flags = coq_warn_error

(** * Native compiler *)

let msg_byteonly =
  "Only the bytecode version of Coq will be available."

let msg_no_ocamlopt () =
  warn "Cannot find the OCaml native-code compiler.\n%s" msg_byteonly

let msg_no_dynlink_cmxa prefs =
  warn "Cannot find native-code dynlink library.\n%s" msg_byteonly;
  cprintf prefs "For building a native-code Coq, you may try to first";
  cprintf prefs "compile and install a dummy dynlink.cmxa (see dev/dynlink.ml)";
  cprintf prefs "and then run ./configure -natdynlink no"

let check_native prefs camlenv =
  let () = if prefs.byteonly then raise Not_found in
  let version, _ = tryrun camlexec.find ["opt";"-version"] in
  if version = "" then let () = msg_no_ocamlopt () in raise Not_found
  else if fst (tryrun camlexec.find ["query";"dynlink"]) = ""
  then let () = msg_no_dynlink_cmxa prefs in raise Not_found
  else
    let () =
      let { CamlConf.caml_version } = camlenv in
      if version <> caml_version then
        warn "Native and bytecode compilers do not have the same version!"
    in cprintf prefs "You have native-code compilation. Good!"

let best_compiler prefs camlenv =
  try check_native prefs camlenv; "opt" with Not_found -> "byte"

(** * Native dynlink *)

let hasnatdynlink prefs best_compiler = prefs.natdynlink && best_compiler = "opt"

(** * OS dependent libraries *)

(** Check for dune *)

let dune_install_warning () =
  warn "You are using Dune < 2.9, the install procedure will not respect the -docdir and -configdir configure directives; please see dev/doc/INSTALL.make.md for more information"

(* returns true if dune >= 2.9 *)
let check_for_dune_29 () =
  let dune_version, _  = tryrun "dune" ["--version"] in
  let dune_version = generic_version_nums ~name:"dune" dune_version in
  match dune_version with
  (* Development version, consider it >= 2.9 *)
  | [] -> true
  | _ ->
    if dune_version < [2;9;0] then
      (dune_install_warning ();
       false)
    else
      true

(** Zarith library *)

let check_for_zarith prefs =
  let zarith,_ = tryrun camlexec.find ["query";"zarith"] in
  let zarith_cmai base = Sys.file_exists (base / "z.cmi") && Sys.file_exists (base / "zarith.cma") in
  let zarith_version, _ = run camlexec.find ["query"; "zarith"; "-format"; "%v"] in
  match zarith with
  | ""  ->
    die "Zarith library not installed, required"
  | _ when not (zarith_cmai zarith) ->
    die "Zarith library installed but no development files found (try installing the -dev package)"
  | _   ->
    let zarith_version_int = generic_version_nums ~name:"Zarith" zarith_version in
    if zarith_version_int >= [1;10;0] then
      cprintf prefs "You have the Zarith library %s installed. Good!" zarith_version
    else
      die ("Zarith version 1.10 is required, you have " ^ zarith_version)

(** * Documentation : do we have latex, hevea, ... *)

let check_sphinx_deps () =
  ignore (run (which "python3") ["doc/tools/coqrst/checkdeps.py"])

let check_doc () =
  let err s =
    die (sprintf "A documentation build was requested, but %s was not found." s);
  in
  if not (program_in_path "python3") then err "python3";
  if not (program_in_path "sphinx-build") then err "sphinx-build";
  check_sphinx_deps ()

(** * Installation directories : bindir, libdir, mandir, docdir, etc *)

(* Source code root *)
let coqsrc = Sys.getcwd ()

let unix arch = os_type_cygwin || not (arch_is_win32 arch)

(** Variable name, description, ref in prefs, default dir, prefix-relative *)

type path_style =
  | Absolute of string (* Should start with a "/" *)
  | Relative of string (* Should not start with a "/" *)

module InstallDir = struct

  type t =
    { var : string
    (** Makefile variable to write *)
    ; msg : string
    (** Description of the directory  *)
    ; uservalue : string option
    (** Value given explictly by the user *)
    ; selfcontainedlayout : path_style
    (** Path style when layout is "local" *)
    ; unixlayout : path_style
    (** Path style for installation *)
    }

  let make var msg uservalue selfcontainedlayout unixlayout =
    { var; msg; uservalue; selfcontainedlayout; unixlayout }

end

let install prefs =
  [ InstallDir.make "COQPREFIX" "Coq" prefs.prefix (Relative "") (Relative "")
  ; InstallDir.make "COQLIBINSTALL" "the Coq library" prefs.libdir (Relative "lib") (Relative "lib/coq")
  ; InstallDir.make "CONFIGDIR" "the Coqide configuration files" prefs.configdir (Relative "config") (Absolute "/etc/xdg/coq")
  ; InstallDir.make "DATADIR" "the Coqide data files" prefs.datadir (Relative "share") (Relative "share/coq")
  ; InstallDir.make "MANDIR" "the Coq man pages" prefs.mandir (Relative "man") (Relative "share/man")
  ; InstallDir.make "DOCDIR" "documentation prefix path for all Coq packages" prefs.docdir (Relative "doc") (Relative "share/doc")
  ]

let strip_trailing_slash_if_any p =
  if p.[String.length p - 1] = '/' then String.sub p 0 (String.length p - 1) else p

let use_suffix prefix = function
  | Relative "" -> prefix
  | Relative suff -> prefix ^ "/" ^ suff
  | Absolute path -> path

let relativize = function
  (* Turn a global layout based on some prefix to a relative layout *)
  | Relative _ as suffix -> suffix
  | Absolute path -> Relative (String.sub path 1 (String.length path - 1))

let find_suffix prefix path = match prefix with
  | None -> Absolute path
  | Some p ->
     let p = strip_trailing_slash_if_any p in
     let lpath = String.length path in
     let lp = String.length p in
     if lpath > lp && String.sub path 0 lp = p then
       Relative (String.sub path (lp+1) (lpath - lp - 1))
     else
       Absolute path

(* This computes the actual effective path for an install directory,
   based on the given prefix; if prefix is absent, it is assumed that
   the profile is "local" *)
let do_one_instdir ~prefix ~arch InstallDir.{var; msg; uservalue; selfcontainedlayout; unixlayout} =
  (var,msg),
  match uservalue, prefix with
  | Some d, p -> d, find_suffix p d
  | None, Some p ->
    let suffix = if (arch_is_win32 arch) then selfcontainedlayout else relativize unixlayout in
    use_suffix p suffix, suffix
  | None, None ->
    let suffix = if (unix arch) then unixlayout else selfcontainedlayout in
    let base = if (unix arch) then "/usr/local" else "C:/coq" in
    let dflt = use_suffix base suffix in
    let () = printf "Where should I install %s [%s]? " msg dflt in
    let line = read_line () in
    if line = "" then (dflt,suffix) else (line,find_suffix None line)

let install_dirs prefs arch =
  let prefix =
    match prefs.prefix with
    | None ->
      begin
        try Some (Sys.getenv "COQ_CONFIGURE_PREFIX")
        with
        | Not_found when prefs.interactive -> None
        | Not_found -> Some Sys.(getcwd () ^ "/../install/default")
      end
    | p -> p
  in
  List.map (do_one_instdir ~prefix ~arch) (install prefs)

let select var install_dirs = List.find (fun ((v,_),_) -> v=var) install_dirs |> snd

module CoqEnv = struct
  (** Coq core paths, for libraries, documentation, configuration, and data *)
  type t =
    { coqlib : string
    ; coqlibsuffix : path_style
    ; docdir : string
    ; docdirsuffix : path_style
    ; configdir : string
    ; configdirsuffix : path_style
    ; datadir : string
    ; datadirsuffix : path_style }
end

let resolve_coqenv install_dirs =
  let coqlib, coqlibsuffix = select "COQLIBINSTALL" install_dirs in
  let docdir, docdirsuffix = select "DOCDIR" install_dirs in
  let configdir, configdirsuffix = select "CONFIGDIR" install_dirs in
  let datadir,datadirsuffix = select "DATADIR" install_dirs in
  { CoqEnv.coqlib; coqlibsuffix; docdir; docdirsuffix
  ; configdir; configdirsuffix; datadir; datadirsuffix }

(** * CC runtime flags *)

(* Note that Coq's VM requires at least C99-compliant floating-point
   arithmetic; this should be ensured by OCaml's own C flags, which
   set a minimum of [--std=gnu99] ; modern compilers by default assume
   C11 or later, so no explicit [--std=] flags are added by OCaml *)
let cflags_dflt = "-Wall -Wno-unused -g -O2"

let cflags_sse2 = "-msse2 -mfpmath=sse"

(* cflags, sse2_math = *)
let compute_cflags () =
  let _, slurp =
    (* Test SSE2_MATH support <https://stackoverflow.com/a/45667927> *)
    tryrun camlexec.find
      ["ocamlc"; "-ccopt"; cflags_dflt ^ " -march=native -dM -E " ^ cflags_sse2;
       "-c"; coqsrc/"dev/header.c"] in  (* any file *)
  if List.exists (fun line -> starts_with line "#define __SSE2_MATH__ 1") slurp
  then (cflags_dflt ^ " " ^ cflags_sse2, true)
  else (cflags_dflt, false)

(** Test at configure time that no harmful double rounding seems to
    be performed with an intermediate 80-bit representation (x87).

    If this test fails but SSE2_MATH is available, the build can go
    further as Coq's primitive floats will use it through a dedicated
    external C implementation (instead of relying on OCaml operations)

    If this test fails and SSE2_MATH is not available, abort.
 *)
let check_fmath sse2_math =
  let add = (+.) in
  let b = ldexp 1. 53 in
  let s = add 1. (ldexp 1. (-52)) in
  if (add b s <= b || add b 1. <> b || ldexp 1. (-1074) <= 0.)
     && not sse2_math then
    die "Detected non IEEE-754 compliant architecture (or wrong \
         rounding mode). Use of Float is thus unsafe."

let esc s = if String.contains s ' ' then "\"" ^ s ^ "\"" else s

(** * Summary of the configuration *)

let pr_native = function
  | NativeYes -> "yes" | NativeNo -> "no" | NativeOndemand -> "ondemand"

let print_summary prefs arch camlenv best_compiler install_dirs coqide lablgtkdir hasnatdynlink idearchdef browser =
  let { CamlConf.caml_version; camlbin; camllib } = camlenv in
  let pr s = printf s in
  pr "\n";
  pr "  Architecture                : %s\n" arch;
  pr "  Sys.os_type                 : %s\n" Sys.os_type;
  pr "  OCaml version               : %s\n" caml_version;
  pr "  OCaml binaries in           : %s\n" (esc camlbin);
  pr "  OCaml library in            : %s\n" (esc camllib);
  if best_compiler = "opt" then
    pr "  Native dynamic link support : %B\n" hasnatdynlink;
  if coqide <> "no" then
    pr "  Lablgtk3 library in         : %s\n" (esc lablgtkdir);
  if idearchdef = "QUARTZ" then
    pr "  Mac OS integration is on\n";
  pr "  CoqIDE                      : %s\n" coqide;
  pr "  Documentation               : %s\n"
    (if prefs.withdoc then "All" else "None");
  pr "  Web browser                 : %s\n" browser;
  pr "  Coq web site                : %s\n" prefs.coqwebsite;
  pr "  Bytecode VM enabled         : %B\n" prefs.bytecodecompiler;
  pr "  Native Compiler enabled     : %s\n\n" (pr_native prefs.nativecompiler);
  if prefs.install_enabled then begin
    pr "  Paths for true installation:\n";
    List.iter
      (fun ((_,msg),(dir,_)) -> pr "  - %s will be copied in %s\n" msg (esc dir))
      install_dirs
  end
  else pr "  Installation not available (local mode)";
  pr "\n";
  pr "If anything is wrong above, please restart './configure'.\n\n";
  pr "*Warning* To compile the system for a new architecture\n";
  pr "          don't forget to do a 'make clean' before './configure'.\n"

(** * Build the dev/ocamldebug-coq file *)
let write_dbg_wrapper camlenv o =
  let { CamlConf.camlbin } = camlenv in
  let pr s = fprintf o s in
  pr "#!/bin/sh\n\n";
  pr "###### ocamldebug-coq : a wrapper around ocamldebug for Coq ######\n\n";
  pr "# DO NOT EDIT THIS FILE: automatically generated by ../configure #\n\n";
  pr "export COQTOP=%S\n" coqsrc;
  pr "OCAMLDEBUG=%S\n" (camlbin^"/ocamldebug");
  pr ". $COQTOP/dev/ocamldebug-coq.run\n"

(** * Build the config/coq_config.ml file *)

let write_configml camlenv coqenv caml_flags caml_version_nums arch arch_is_win32 hasnatdynlink browser idearchdef prefs o =
  let { CoqEnv.coqlib; coqlibsuffix; configdir; configdirsuffix; docdir; docdirsuffix; datadir; datadirsuffix } = coqenv in
  let { CamlConf.caml_version } = camlenv in
  let pr s = fprintf o s in
  let pr_s = pr "let %s = %S\n" in
  let pr_b = pr "let %s = %B\n" in
  let pr_i32 = pr "let %s = %dl\n" in
  let pr_p s o = pr "let %s = %S\n" s
    (match o with Relative s -> s | Absolute s -> s) in
  let pr_li n l = pr "let %s = [%s]\n" n (String.concat ";" (List.map string_of_int l)) in
  pr "(* DO NOT EDIT THIS FILE: automatically generated by ../configure *)\n";
  pr "(* Exact command that generated this file: *)\n";
  pr "(* %s *)\n\n" (String.concat " " (Array.to_list Sys.argv));
  pr_s "coqlib" coqlib;
  pr_s "configdir" configdir;
  pr_s "datadir" datadir;
  pr_s "docdir" docdir;
  pr_p "coqlibsuffix" coqlibsuffix;
  pr_p "configdirsuffix" configdirsuffix;
  pr_p "datadirsuffix" datadirsuffix;
  pr_p "docdirsuffix" docdirsuffix;
  pr_s "ocamlfind" camlexec.find;
  pr_s "caml_flags" caml_flags;
  pr_s "version" coq_version;
  pr_s "caml_version" caml_version;
  pr_li "caml_version_nums" caml_version_nums;
  pr_s "arch" arch;
  pr_b "arch_is_win32" arch_is_win32;
  pr_s "exec_extension" !exe;
  pr "let gtk_platform = `%s\n" idearchdef;
  pr_b "has_natdynlink" hasnatdynlink;
  pr_i32 "vo_version" vo_magic;
  pr_s "browser" browser;
  pr_s "wwwcoq" prefs.coqwebsite;
  pr_s "wwwbugtracker" (prefs.coqwebsite ^ "bugs/");
  pr_s "wwwrefman" (prefs.coqwebsite ^ "distrib/V" ^ coq_version ^ "/refman/");
  pr_s "wwwstdlib" (prefs.coqwebsite ^ "distrib/V" ^ coq_version ^ "/stdlib/");
  pr_s "localwwwrefman"  ("file:/" ^ docdir ^ "/html/refman");
  pr_b "bytecode_compiler" prefs.bytecodecompiler;
  pr "type native_compiler = NativeOff | NativeOn of { ondemand : bool }\n";
  pr "let native_compiler = %s\n"
    (match prefs.nativecompiler with
     | NativeYes -> "NativeOn {ondemand=false}" | NativeNo -> "NativeOff"
     | NativeOndemand -> "NativeOn {ondemand=true}");

  let core_src_dirs = [ "boot"; "config"; "lib"; "clib"; "kernel"; "library";
                        "engine"; "pretyping"; "interp"; "gramlib"; "parsing"; "proofs";
                        "tactics"; "toplevel"; "printing"; "ide"; "stm"; "vernac" ] in
  let core_src_dirs = List.fold_left (fun acc core_src_subdir -> acc ^ "  \"" ^ core_src_subdir ^ "\";\n")
                                    ""
                                    core_src_dirs in

  pr "\nlet core_src_dirs = [\n%s]\n" core_src_dirs;
  pr "\nlet plugins_dirs = [\n";

  let plugins = match open_in "config/plugin_list" with
    | exception Sys_error _ ->
      let plugins =
        try Sys.readdir "plugins"
        with _ -> [||]
      in
      Array.sort compare plugins;
      plugins
    | ch -> Array.of_list (snd (read_lines_and_close ch))
  in
  Array.iter
    (fun f ->
      let f' = "plugins/"^f in
      if Sys.is_directory f' && f.[0] <> '.' then pr "  %S;\n" f')
    plugins;
  pr "]\n";

  pr "\nlet all_src_dirs = core_src_dirs @ plugins_dirs\n"

(** * Build the config/Makefile file *)

let write_makefile prefs install_dirs best_compiler caml_flags coq_caml_flags coqide arch exe dune_29 o =
  let pr s = fprintf o s in
  pr "###### config/Makefile : Configuration file for Coq ##############\n";
  pr "#                                                                #\n";
  pr "# This file is generated by the script \"configure\"               #\n";
  pr "# DO NOT EDIT IT !! DO NOT EDIT IT !! DO NOT EDIT IT !!          #\n";
  pr "# If something is wrong below, then rerun the script \"configure\" #\n";
  pr "# with the good options (see the file INSTALL).                  #\n";
  pr "#                                                                #\n";
  pr "##################################################################\n\n";
  pr "#Variable used to detect whether ./configure has run successfully.\n";
  pr "COQ_CONFIGURED=yes\n\n";
  pr "# Paths for true installation\n";
  List.iter (fun ((v,msg),_) -> pr "# %s: path for %s\n" v msg) install_dirs;
  List.iter (fun ((v,_),(dir,_)) -> pr "%s=%S\n" v dir) install_dirs;
  pr "\n# Coq version\n";
  pr "VERSION=%s\n" coq_version;
  pr "# The best compiler: native (=opt) or bytecode (=byte)\n";
  pr "BEST=%s\n\n" best_compiler;
  (* Only used in the test suite: OCAMLFIND CAMLFLAGS *)
  pr "# Findlib command\n";
  pr "OCAMLFIND=%S\n" camlexec.find;
  pr "# Caml flags\n";
  pr "CAMLFLAGS=%s %s\n" caml_flags coq_caml_flags;
  pr "# Your architecture\n";
  pr "# Can be obtain by UNIX command arch\n";
  pr "ARCH=%s\n" arch;
  pr "# executable files extension, currently:\n";
  pr "#  Unix systems:\n";
  pr "#  Win32 systems : .exe\n";
  pr "EXE=%s\n" exe;
  pr "# the command MKDIR (try to use mkdirhier if you have problems)\n";
  pr "MKDIR=mkdir -p\n\n";
  pr "# CoqIDE (no/byte/opt)\n";
  pr "HASCOQIDE=%s\n" coqide;
  pr "# Defining REVISION\n";
  pr "# Option to control compilation and installation of the documentation\n";
  pr "WITHDOC=%s\n\n" (if prefs.withdoc then "all" else "no");
  pr "# Option to produce precompiled files for native_compute\n";
  pr "NATIVECOMPUTE=%s\n" (if prefs.nativecompiler = NativeYes then "-native-compiler yes" else "");
  pr "COQWARNERROR=%s\n" (if prefs.warn_error then "-w +default" else "");
  pr "CONFIGURE_DARGS=%s\n" prefs.dune_args;
  pr "COQ_INSTALL_ENABLED=%b\n" prefs.install_enabled;
  if dune_29 then pr "DUNE_29_PLUS=yes\n";
  ()

let write_dune_c_flags cflags o =
  let pr s = fprintf o s in
  pr "(%s)\n" cflags

let write_configpy o =
  let pr s = fprintf o s in
  pr "# DO NOT EDIT THIS FILE: automatically generated by ../configure\n";
  pr "version = '%s'\n" coq_version;
  pr "is_a_released_version = %s\n" (if is_a_released_version then "True" else "False")

(* Main configure routine *)
let main () =
  let prefs = CmdArgs.parse_args () in
  Util.debug := prefs.debug;
  let dune_29 = check_for_dune_29 () in
  let coq_annot_flag = coq_annot_flag prefs in
  let coq_bin_annot_flag = coq_bin_annot_flag prefs in
  let arch = arch prefs in
  let arch_is_win32 = arch_is_win32 arch in
  let exe = resolve_binary_suffix arch in
  Util.exe := exe;
  install_precommit_hook prefs;
  let browser = browser prefs arch in
  let camlenv = resolve_caml prefs in
  let caml_version_nums = caml_version_nums camlenv in
  check_caml_version prefs camlenv.CamlConf.caml_version caml_version_nums;
  check_findlib_version prefs camlenv;
  let best_compiler = best_compiler prefs camlenv in
  let caml_flags = caml_flags coq_annot_flag coq_bin_annot_flag in
  let coq_caml_flags = coq_caml_flags prefs in
  let hasnatdynlink = hasnatdynlink prefs best_compiler in
  check_for_zarith prefs;
  let coqide, lablgtkdir = Coqide.coqide camlexec.find prefs best_compiler camlenv.CamlConf.camllib in
  let idearchdef = Coqide.idearchdef camlexec.find prefs coqide arch in
  (if prefs.withdoc then check_doc ());
  let install_dirs = install_dirs prefs arch in
  let coqenv = resolve_coqenv install_dirs in
  let cflags, sse2_math = compute_cflags () in
  check_fmath sse2_math;
  if prefs.interactive then
    print_summary prefs arch camlenv best_compiler install_dirs coqide lablgtkdir hasnatdynlink idearchdef browser;
  write_config_file ~file:"dev/ocamldebug-coq" ~bin:true (write_dbg_wrapper camlenv);
  write_config_file ~file:"config/coq_config.ml"
    (write_configml camlenv coqenv caml_flags caml_version_nums arch arch_is_win32 hasnatdynlink browser idearchdef prefs);
  write_config_file ~file:"config/Makefile"
    (write_makefile prefs install_dirs best_compiler caml_flags coq_caml_flags coqide arch exe dune_29);
  write_config_file ~file:"config/dune.c_flags" (write_dune_c_flags cflags);
  write_config_file ~file:"config/coq_config.py" write_configpy;
  ()

let _ =
  main ()
