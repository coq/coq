(**********************************)

(**  Configuration script for Coq *)

(**********************************)

(** This file should be run via: ocaml configure.ml <opts>
    You could also use our wrapper ./configure <opts> *)

#load "unix.cma"
#load "str.cma"
open Printf

let coq_version = "8.9.0"
let coq_macos_version = "8.9.0" (** "[...] should be a string comprised of
three non-negative, period-separated integers [...]" *)
let vo_magic = 8900
let state_magic = 58900
let distributed_exec =
  ["coqtop.opt"; "coqidetop.opt"; "coqqueryworker.opt"; "coqproofworker.opt"; "coqtacticworker.opt";
   "coqc";"coqchk";"coqdoc";"coqworkmgr";"coq_makefile";"coq-tex";"coqwc";"csdpcert";"coqdep"]

let verbose = ref false (* for debugging this script *)

let red, yellow, reset =
  if Unix.isatty Unix.stdout && Unix.isatty Unix.stderr && Sys.os_type = "Unix"
  then "\027[31m", "\027[33m", "\027[0m"
  else "", "", ""

(** * Utility functions *)
let cfprintf oc = kfprintf (fun oc -> fprintf oc "\n%!") oc
let cprintf s = cfprintf stdout s
let ceprintf s = cfprintf stderr s
let die msg = ceprintf "%s%s%s\nConfiguration script failed!" red msg reset; exit 1

let warn s = kfprintf (fun oc -> cfprintf oc "%s" reset) stdout ("%sWarning: " ^^ s) yellow

let s2i = int_of_string
let i2s = string_of_int
let (/) x y = x ^ "/" ^ y

(** Remove the final '\r' that may exists on Win32 *)

let remove_final_cr s =
  let n = String.length s in
  if n<>0 && s.[n-1] = '\r' then String.sub s 0 (n-1)
  else s

let check_exit_code (_,code) = match code with
  | Unix.WEXITED 0 -> ()
  | Unix.WEXITED 127 -> failwith "no such command"
  | Unix.WEXITED n -> failwith ("exit code " ^ i2s n)
  | Unix.WSIGNALED n -> failwith ("killed by signal " ^ i2s n)
  | Unix.WSTOPPED n -> failwith ("stopped by signal " ^ i2s n)

(** As for Unix.close_process, our Unix.waipid will ignore all EINTR *)

let rec waitpid_non_intr pid =
  try Unix.waitpid [] pid
  with Unix.Unix_error (Unix.EINTR, _, _) -> waitpid_non_intr pid

(** Below, we'd better read all lines on a channel before closing it,
    otherwise a SIGPIPE could be encountered by the sub-process *)

let read_lines_and_close fd =
  let cin = Unix.in_channel_of_descr fd in
  let lines = ref [] in
  begin
    try
      while true do
        lines := remove_final_cr (input_line cin) :: !lines
      done
    with End_of_file -> ()
  end;
  close_in cin;
  let lines = List.rev !lines in
  try List.hd lines, lines with Failure _ -> "", []

(** Run some unix command and read the first line of its output.
    We avoid Unix.open_process and its non-fully-portable /bin/sh,
    especially when it comes to quoting the filenames.
    See open_process_pid in ide/coq.ml for more details.
    Error messages:
     - if err=StdErr, any error message goes in the stderr of our script.
     - if err=StdOut, we merge stderr and stdout (just as 2>&1).
     - if err=DevNull, we drop the error messages (same as 2>/dev/null). *)

type err = StdErr | StdOut | DevNull

let exe = ref ""  (* Will be set later on, when the suffix is known *)

let run ?(fatal=true) ?(err=StdErr) prog args =
  let prog = (* Ensure prog ends with exe *)
    if Str.string_match (Str.regexp ("^.*" ^ !exe ^ "$")) prog 0
    then prog else (prog ^ !exe) in
  let argv = Array.of_list (prog::args) in
  try
    let out_r,out_w = Unix.pipe () in
    let nul_r,nul_w = Unix.pipe () in
    let () = Unix.set_close_on_exec out_r in
    let () = Unix.set_close_on_exec nul_r in
    let fd_err = match err with
      | StdErr -> Unix.stderr
      | StdOut -> out_w
      | DevNull -> nul_w
    in
    let pid = Unix.create_process prog argv Unix.stdin out_w fd_err in
    let () = Unix.close out_w in
    let () = Unix.close nul_w in
    let line, all = read_lines_and_close out_r in
    let _ = read_lines_and_close nul_r in
    let () = check_exit_code (waitpid_non_intr pid) in
    line, all
  with
  | _ when not fatal && not !verbose -> "", []
  | e ->
      let cmd = String.concat " " (prog::args) in
      let exn = match e with Failure s -> s | _ -> Printexc.to_string e in
      let msg = sprintf "Error while running '%s' (%s)" cmd exn in
      if fatal then die msg else (warn "%s" msg; "", [])

let tryrun prog args = run ~fatal:false ~err:DevNull prog args

(** Splitting a string at some character *)

let string_split c s =
  let len = String.length s in
  let rec split n =
    try
      let pos = String.index_from s n c in
      let dir = String.sub s n (pos-n) in
      dir :: split (succ pos)
    with
      | Not_found -> [String.sub s n (len-n)]
  in
  if len = 0 then [] else split 0

(** String prefix test : does [s1] starts with [s2] ? *)

let starts_with s1 s2 =
  let l1 = String.length s1 and l2 = String.length s2 in
  l2 <= l1 && s2 = String.sub s1 0 l2

(** Turn a version string such as "4.01.0+rc2" into the list
    ["4";"01";"1"], stopping at the first non-digit or "." *)

let numeric_prefix_list s =
  let isnum c = (c = '.' || (c >= '0' && c <= '9')) in
  let max = String.length s in
  let i = ref 0 in
  while !i < max && isnum s.[!i] do incr i done;
  string_split '.' (String.sub s 0 !i)

(** Combined existence and directory tests *)

let dir_exists f = Sys.file_exists f && Sys.is_directory f

(** Does a file exist and is executable ? *)

let is_executable f =
  try let () = Unix.access f [Unix.X_OK] in true
  with Unix.Unix_error _ -> false

(** Equivalent of rm -f *)

let safe_remove f =
  try Unix.chmod f 0o644; Sys.remove f with _ -> ()

(** The PATH list for searching programs *)

let os_type_win32 = (Sys.os_type = "Win32")
let os_type_cygwin = (Sys.os_type = "Cygwin")

let global_path =
  try string_split (if os_type_win32 then ';' else ':') (Sys.getenv "PATH")
  with Not_found -> []

(** A "which" command. May raise [Not_found] *)

let which prog =
  let rec search = function
    | [] -> raise Not_found
    | dir :: path ->
      let file = if os_type_win32 then dir/prog^".exe" else dir/prog in
      if is_executable file then file else search path
  in search global_path

let program_in_path prog =
  try let _ = which prog in true with Not_found -> false

(** Choose a command among a list of candidates
    (command name, mandatory arguments, arguments for this test).
    Chooses the first one whose execution outputs a non-empty (first) line.
    Dies with message [msg] if none is found. *)

let select_command msg candidates =
  let rec search = function
    | [] -> die msg
    | (p, x, y) :: tl ->
      if fst (tryrun p (x @ y)) <> ""
      then List.fold_left (Printf.sprintf "%s %s") p x
      else search tl
  in search candidates

(** As per bug #4828, ocamlfind on Windows/Cygwin barfs if you pass it
    a quoted path to camlp5o via -pp.  So we only quote camlp5o on not
    Windows, and warn on Windows if the path contains spaces *)
let contains_suspicious_characters str =
  List.fold_left (fun b ch -> String.contains str ch || b) false [' '; '\t']

let win_aware_quote_executable str =
  if not (os_type_win32 || os_type_cygwin) then
    sprintf "%S" str
  else
    let _ = if contains_suspicious_characters str then
      warn "The string %S contains suspicious characters; ocamlfind might fail" str in
    Str.global_replace (Str.regexp "\\\\") "/" str

(** * Date *)

(** The short one is displayed when starting coqtop,
    The long one is used as compile date *)

let months =
 [| "January";"February";"March";"April";"May";"June";
    "July";"August";"September";"October";"November";"December" |]

let get_date () =
  let now = Unix.localtime (Unix.time ()) in
  let year = 1900+now.Unix.tm_year in
  let month = months.(now.Unix.tm_mon) in
  sprintf "%s %d" month year,
  sprintf "%s %d %d %d:%02d:%02d" (String.sub month 0 3) now.Unix.tm_mday year
    now.Unix.tm_hour now.Unix.tm_min now.Unix.tm_sec

let short_date, full_date = get_date ()

(** * Command-line parsing *)

type ide = Opt | Byte | No

type preferences = {
  prefix : string option;
  local : bool;
  vmbyteflags : string option;
  custom : bool option;
  bindir : string option;
  libdir : string option;
  configdir : string option;
  datadir : string option;
  mandir : string option;
  docdir : string option;
  coqdocdir : string option;
  ocamlfindcmd : string option;
  lablgtkdir : string option;
  camlp5dir : string option;
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
  nativecompiler : bool;
  coqwebsite : string;
  force_caml_version : bool;
  force_findlib_version : bool;
  warn_error : bool;
}

module Profiles = struct

let default = {
  prefix = None;
  local = false;
  vmbyteflags = None;
  custom = None;
  bindir = None;
  libdir = None;
  configdir = None;
  datadir = None;
  mandir = None;
  docdir = None;
  coqdocdir = None;
  ocamlfindcmd = None;
  lablgtkdir = None;
  camlp5dir = None;
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
  nativecompiler = not (os_type_win32 || os_type_cygwin);
  coqwebsite = "http://coq.inria.fr/";
  force_caml_version = false;
  force_findlib_version = false;
  warn_error = false;
}

let devel state = { state with
  local = true;
  bin_annot = true;
  annot = true;
  warn_error = true;
}
let devel_doc = "-local -annot -bin-annot -warn-error yes"

let get = function
  | "devel" -> devel
  | s -> raise (Arg.Bad ("profile name expected instead of "^s))

let doc =
  "<profile> Sets a bunch of flags. Supported profiles:
     devel = " ^ devel_doc

end

let prefs = ref Profiles.default


let get_bool = function
  | "true" | "yes" | "y" | "all" -> true
  | "false" | "no" | "n" -> false
  | s -> raise (Arg.Bad ("boolean argument expected instead of "^s))

let get_ide = function
  | "opt" -> Opt
  | "byte" -> Byte
  | "no" -> No
  | s -> raise (Arg.Bad ("(opt|byte|no) argument expected instead of "^s))

let arg_bool f = Arg.String (fun s -> prefs := f !prefs (get_bool s))

let arg_string f = Arg.String (fun s -> prefs := f !prefs s)
let arg_string_option f = Arg.String (fun s -> prefs := f !prefs (Some s))
let arg_string_list c f = Arg.String (fun s -> prefs := f !prefs (string_split c s))

let arg_set f = Arg.Unit (fun () -> prefs := f !prefs true)
let arg_clear f = Arg.Unit (fun () -> prefs := f !prefs false)

let arg_set_option f = Arg.Unit (fun () -> prefs := f !prefs (Some true))
let arg_clear_option f = Arg.Unit (fun () -> prefs := f !prefs (Some false))

let arg_ide f = Arg.String (fun s -> prefs := f !prefs (Some (get_ide s)))

let arg_profile = Arg.String (fun s -> prefs := Profiles.get s !prefs)

(* TODO : earlier any option -foo was also available as --foo *)

let args_options = Arg.align [
  "-prefix", arg_string_option (fun p prefix -> { p with prefix }),
    "<dir> Set installation directory to <dir>";
  "-local", arg_set (fun p local -> { p with local }),
    " Set installation directory to the current source tree";
  "-vmbyteflags", arg_string_option (fun p vmbyteflags -> { p with vmbyteflags }),
    "<flags> Comma-separated link flags for the VM of coqtop.byte";
  "-custom", arg_set_option (fun p custom -> { p with custom }),
    " Build bytecode executables with -custom (not recommended)";
  "-no-custom", arg_clear_option (fun p custom -> { p with custom }),
    " Do not build with -custom on Windows and MacOS";
  "-bindir", arg_string_option (fun p bindir -> { p with bindir }),
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
  "-coqdocdir", arg_string_option (fun p coqdocdir -> { p with coqdocdir }),
    "<dir> Where to install Coqdoc style files";
  "-ocamlfind", arg_string_option (fun p ocamlfindcmd -> { p with ocamlfindcmd }),
    "<dir> Specifies the ocamlfind command to use";
  "-lablgtkdir", arg_string_option (fun p lablgtkdir -> { p with lablgtkdir }),
    "<dir> Specifies the path to the Lablgtk library";
  "-camlp5dir", arg_string_option (fun p camlp5dir -> { p with camlp5dir }),
    "<dir> Specifies where is the Camlp5 library and tells to use it";
  "-flambda-opts", arg_string_list ' ' (fun p flambda_flags -> { p with flambda_flags }),
    "<flags> Specifies additional flags to be passed to the flambda optimizing compiler";
  "-arch", arg_string_option (fun p arch -> { p with arch }),
    "<arch> Specifies the architecture";
  "-natdynlink", arg_bool (fun p natdynlink -> { p with natdynlink }),
    "(yes|no) Use dynamic loading of native code or not";
  "-coqide", arg_ide (fun p coqide -> { p with coqide }),
    "(opt|byte|no) Specifies whether or not to compile CoqIDE";
  "-nomacintegration", arg_clear (fun p macintegration -> { p with macintegration }),
    " Do not try to build CoqIDE MacOS integration";
  "-browser", arg_string_option (fun p browser -> { p with browser }),
    "<command> Use <command> to open URL %s";
  "-with-doc", arg_bool (fun p withdoc -> { p with withdoc }),
    "(yes|no) Compile the documentation or not";
  "-byte-only", arg_set (fun p byteonly -> { p with byteonly }),
    " Compiles only bytecode version of Coq";
  "-nodebug", arg_clear (fun p debug -> { p with debug }),
    " Do not add debugging information in the Coq executables";
  "-profiling", arg_set (fun p profile -> { p with profile }),
    " Add profiling information in the Coq executables";
  "-annotate", Arg.Unit (fun () -> die "-annotate has been removed. Please use -annot or -bin-annot instead."),
    " Removed option. Please use -annot or -bin-annot instead";
  "-annot", arg_set (fun p annot -> { p with annot }),
    " Dumps ml text annotation files while compiling Coq (e.g. for Tuareg)";
  "-bin-annot", arg_set (fun p bin_annot -> { p with bin_annot }),
    " Dumps ml binary annotation files while compiling Coq (e.g. for Merlin)";
  "-bytecode-compiler", arg_bool (fun p bytecodecompiler -> { p with bytecodecompiler }),
    "(yes|no) Enable Coq's bytecode reduction machine (VM)";
  "-native-compiler", arg_bool (fun p nativecompiler -> { p with nativecompiler }),
    "(yes|no) Compilation to native code for conversion and normalization";
  "-coqwebsite", arg_string (fun p coqwebsite -> { p with coqwebsite }),
    " URL of the coq website";
  "-force-caml-version", arg_set (fun p force_caml_version -> { p with force_caml_version }),
    " Force OCaml version";
  "-force-findlib-version", arg_set (fun p force_findlib_version -> { p with force_findlib_version }),
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
  if !prefs.local && !prefs.prefix <> None then
    die "Options -prefix and -local are incompatible."

let _ = parse_args ()

(** Default OCaml binaries *)

type camlexec =
 { mutable find : string;
   mutable top : string;
   mutable lex : string;
   mutable yacc : string;
  }

let camlexec =
  { find = "ocamlfind";
    top = "ocaml";
    lex = "ocamllex";
    yacc = "ocamlyacc";
  }

let reset_caml_lex c o = c.lex <- o
let reset_caml_yacc c o = c.yacc <- o
let reset_caml_top c o = c.top <- o
let reset_caml_find c o = c.find <- o

let coq_debug_flag = if !prefs.debug then "-g" else ""
let coq_profile_flag = if !prefs.profile then "-p" else ""
let coq_annot_flag = if !prefs.annot then "-annot" else ""
let coq_bin_annot_flag = if !prefs.bin_annot then "-bin-annot" else ""

(* This variable can be overriden only for debug purposes, use with
   care. *)
let coq_safe_string = "-safe-string"
let coq_strict_sequence = "-strict-sequence"

let cflags = "-Wall -Wno-unused -g -O2"

(** * Architecture *)

let arch_progs =
  [("/bin/uname",["-s"]);
   ("/usr/bin/uname",["-s"]);
   ("/bin/arch", []);
   ("/usr/bin/arch", []);
   ("/usr/ucb/arch", []) ]

let query_arch () =
  cprintf "I can not automatically find the name of your architecture.";
  cprintf "Give me a name, please [win32 for Win95, Win98 or WinNT]: %!";
  read_line ()

let rec try_archs = function
  | (prog,args)::rest when is_executable prog ->
    let arch, _ = tryrun prog args in
    if arch <> "" then arch else try_archs rest
  | _ :: rest -> try_archs rest
  | [] -> query_arch ()

let arch = match !prefs.arch with
  | Some a -> a
  | None ->
    let arch,_ = tryrun "uname" ["-s"] in
    if starts_with arch "CYGWIN" then "win32"
    else if starts_with arch "MINGW32" then "win32"
    else if arch <> "" then arch
    else try_archs arch_progs

(** NB: [arch_is_win32] is broader than [os_type_win32], cf. cygwin *)

let arch_is_win32 = (arch = "win32")

let exe = exe := if arch_is_win32 then ".exe" else ""; !exe
let dll = if os_type_win32 then ".dll" else ".so"

(** * VCS

    Is the source tree checked out from a recognised
    Version Control System ? *)

let vcs =
  let git_dir = try Sys.getenv "GIT_DIR" with Not_found -> ".git" in
  if Sys.file_exists git_dir then "git"
  else if Sys.file_exists ".svn/entries" then "svn"
  else if dir_exists "{arch}" then "gnuarch"
  else "none"

(** * Git Precommit Hook *)
let _ =
  let f = ".git/hooks/pre-commit" in
  if vcs = "git" && dir_exists ".git/hooks" && not (Sys.file_exists f) then begin
    cprintf "Creating pre-commit hook in %s" f;
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

let browser =
  match !prefs.browser with
  | Some b -> b
  | None when arch_is_win32 -> "start %s"
  | None when arch = "Darwin" -> "open %s"
  | _ -> "firefox -remote \"OpenURL(%s,new-tab)\" || firefox %s &"

(** * OCaml programs *)

let camlbin, caml_version, camllib, findlib_version =
  let () = match !prefs.ocamlfindcmd with
    | Some cmd -> reset_caml_find camlexec cmd
    | None ->
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
    let () =
      if is_executable (camlbin / "ocamllex")
      then reset_caml_lex camlexec (camlbin / "ocamllex") in
    let () =
      if is_executable (camlbin / "ocamlyacc")
      then reset_caml_yacc camlexec (camlbin / "ocamlyacc") in
    let () =
      if is_executable (camlbin / "ocaml")
      then reset_caml_top camlexec (camlbin / "ocaml") in
    camlbin, caml_version, camllib, findlib_version

let camlp5compat = "-loc loc"

(** Caml version as a list of string, e.g. ["4";"00";"1"] *)

let caml_version_list = numeric_prefix_list caml_version

(** Same, with integers in the version list *)

let caml_version_nums =
  try
    if List.length caml_version_list < 2 then failwith "bad version";
    List.map s2i caml_version_list
  with _ ->
    die ("I found the OCaml compiler but cannot read its version number!\n" ^
         "Is it installed properly?")

let check_caml_version () =
  if caml_version_nums >= [4;2;3] then
    cprintf "You have OCaml %s. Good!" caml_version
  else
    let () = cprintf "Your version of OCaml is %s." caml_version in
    if !prefs.force_caml_version then
      warn "Your version of OCaml is outdated."
    else
      die "You need OCaml 4.02.3 or later."

let _ = check_caml_version ()

let findlib_version_list = numeric_prefix_list findlib_version

let findlib_version_nums =
  try
    if List.length findlib_version_list < 2 then failwith "bad version";
    List.map s2i findlib_version_list
  with _ ->
    die ("I found ocamlfind but cannot read its version number!\n" ^
         "Is it installed properly?")

let check_findlib_version () =
  if findlib_version_nums >= [1;4;1] then
    cprintf "You have OCamlfind %s. Good!" findlib_version
  else
    let () = cprintf "Your version of OCamlfind is %s." findlib_version in
    if !prefs.force_findlib_version then
      warn "Your version of OCamlfind is outdated."
    else
      die "You need OCamlfind 1.4.1 or later."

let _ = check_findlib_version ()

let camltag = match caml_version_list with
  | x::y::_ -> "OCAML"^x^y
  | _ -> assert false

(** Explanation of disabled warnings:
    4: fragile pattern matching: too common in the code and too annoying to avoid in general
    9: missing fields in a record pattern: too common in the code and not worth the bother
    27: innocuous unused variable: innocuous
    41: ambiguous constructor or label: too common
    42: disambiguated counstructor or label: too common
    44: "open" shadowing already defined identifier: too common, especially when some are aliases
    45: "open" shadowing a label or constructor: see 44
    48: implicit elimination of optional arguments: too common
    50: unexpected documentation comment: too common and annoying to avoid
    56: unreachable match case: the [_ -> .] syntax doesn't exist in 4.02.3
    58: "no cmx file was found in path": See https://github.com/ocaml/num/issues/9
    59: "potential assignment to a non-mutable value": See Coq's issue #8043
*)
let coq_warnings = "-w +a-4-9-27-41-42-44-45-48-50-58-59"
let coq_warn_error =
    if !prefs.warn_error
    then "-warn-error +a"
         ^ (if caml_version_nums > [4;2;3]
            then "-56"
            else "")
    else ""

(* Flags used to compile Coq and plugins (via coq_makefile) *)
let caml_flags =
  Printf.sprintf "-thread -rectypes %s %s %s %s %s" coq_warnings coq_annot_flag coq_bin_annot_flag coq_safe_string coq_strict_sequence

(* Flags used to compile Coq but _not_ plugins (via coq_makefile) *)
let coq_caml_flags =
  coq_warn_error

(** * Camlp5 configuration *)

(* Convention: we use camldir as a prioritary location for camlp5, if given *)
(* i.e., in the case of camlp5, we search for a copy of camlp5o which *)
(* answers the right camlp5 lib dir *)

let strip_slash dir =
  let n = String.length dir in
  if n>0 && dir.[n - 1] = '/' then String.sub dir 0 (n-1) else dir

let which_camlp5o_for camlp5lib =
  let camlp5o = Filename.concat camlbin "camlp5o" in
  let camlp5lib = strip_slash camlp5lib in
  if fst (tryrun camlp5o ["-where"]) = camlp5lib then camlp5o else
  let camlp5o = which "camlp5o" in
  if fst (tryrun camlp5o ["-where"]) = camlp5lib then camlp5o else
  die ("Error: cannot find Camlp5 binaries corresponding to Camlp5 library " ^ camlp5lib)

let which_camlp5 base =
  let file = Filename.concat camlbin base in
  if is_executable file then file else which base

(* TODO: camlp5dir should rather be the *binary* location, just as camldir *)
(* TODO: remove the late attempts at finding gramlib.cma *)

let check_camlp5 testcma = match !prefs.camlp5dir with
  | Some dir ->
    if Sys.file_exists (dir/testcma) then
      let camlp5o =
        try which_camlp5o_for dir
        with Not_found -> die "Error: cannot find Camlp5 binaries in path.\n" in
      dir, camlp5o
    else
      let msg =
        sprintf "Cannot find camlp5 libraries in '%s' (%s not found)."
          dir testcma
      in die msg
  | None ->
    try
      let camlp5o = which_camlp5 "camlp5o" in
      let dir,_ = tryrun camlp5o ["-where"] in
      dir, camlp5o
    with Not_found ->
      die "No Camlp5 installation found."

let check_camlp5_version camlp5o =
  let version_line, _ = run ~err:StdOut camlp5o ["-v"] in
  let version = List.nth (string_split ' ' version_line) 2 in
  match numeric_prefix_list version with
  | major::minor::_ when s2i major > 6 || (s2i major, s2i minor) >= (6,6) ->
    cprintf "You have Camlp5 %s. Good!" version; version
  | _ -> die "Error: unsupported Camlp5 (version < 6.06 or unrecognized).\n"

let config_camlp5 () =
    let camlp5mod = "gramlib" in
    let camlp5libdir, camlp5o = check_camlp5 (camlp5mod^".cma") in
    let camlp5_version = check_camlp5_version camlp5o in
    camlp5o, Filename.dirname camlp5o, camlp5libdir, camlp5mod, camlp5_version

let camlp5o, camlp5bindir, fullcamlp5libdir,
    camlp5mod, camlp5_version = config_camlp5 ()

let shorten_camllib s =
  if starts_with s (camllib^"/") then
    let l = String.length camllib + 1 in
    "+" ^ String.sub s l (String.length s - l)
  else s

let camlp5libdir = shorten_camllib fullcamlp5libdir

(** * Native compiler *)

let msg_byteonly =
  "Only the bytecode version of Coq will be available."

let msg_no_ocamlopt () =
  warn "Cannot find the OCaml native-code compiler.\n%s" msg_byteonly

let msg_no_camlp5_cmxa () =
  warn "Cannot find the native-code library of camlp5.\n%s" msg_byteonly

let msg_no_dynlink_cmxa () =
  warn "Cannot find native-code dynlink library.\n%s" msg_byteonly;
  cprintf "For building a native-code Coq, you may try to first";
  cprintf "compile and install a dummy dynlink.cmxa (see dev/dynlink.ml)";
  cprintf "and then run ./configure -natdynlink no"

let check_native () =
  let () = if !prefs.byteonly then raise Not_found in
  let version, _ = tryrun camlexec.find ["opt";"-version"] in
  if version = "" then let () = msg_no_ocamlopt () in raise Not_found
  else if not (Sys.file_exists (fullcamlp5libdir/camlp5mod^".cmxa"))
  then let () = msg_no_camlp5_cmxa () in raise Not_found
  else if fst (tryrun camlexec.find ["query";"dynlink"]) = ""
  then let () = msg_no_dynlink_cmxa () in raise Not_found
  else
    let () =
      if version <> caml_version then
        warn "Native and bytecode compilers do not have the same version!"
    in cprintf "You have native-code compilation. Good!"

let best_compiler =
  try check_native (); "opt" with Not_found -> "byte"

(** * Native dynlink *)

let hasnatdynlink = !prefs.natdynlink && best_compiler = "opt"

let natdynlinkflag =
  if hasnatdynlink then "true" else "false"


(** * OS dependent libraries *)

let operating_system =
  if starts_with arch "sun4" then
    let os, _ = run "uname" ["-r"] in
    if starts_with os "5" then
      "Sun Solaris "^os
    else
      "Sun OS "^os
  else
    (try Sys.getenv "OS" with Not_found -> "")

(** Num library *)

(* since 4.06, the Num library is no longer distributed with OCaml (replaced
   by Zarith)
*)

let check_for_numlib () =
  if caml_version_nums >= [4;6;0] then
    let numlib,_ = tryrun camlexec.find ["query";"num"] in
    match numlib with
    | ""  ->
       die "Num library not installed, required for OCaml 4.06 or later"
    | _   -> cprintf "You have the Num library installed. Good!"

let numlib =
  check_for_numlib ()

(** * lablgtk2 and CoqIDE *)

type source = Manual | OCamlFind | Stdlib

let get_source = function
| Manual -> "manually provided"
| OCamlFind -> "via ocamlfind"
| Stdlib -> "in OCaml library"

(** Is some location a suitable LablGtk2 installation ? *)

let check_lablgtkdir ?(fatal=false) src dir =
  let yell msg = if fatal then die msg else (warn "%s" msg; false) in
  let msg = get_source src in
  if not (dir_exists dir) then
    yell (sprintf "No such directory '%s' (%s)." dir msg)
  else if not (Sys.file_exists (dir/"gSourceView2.cmi")) then
    yell (sprintf "Incomplete LablGtk2 (%s): no %s/gSourceView2.cmi." msg dir)
  else if not (Sys.file_exists (dir/"glib.mli")) then
    yell (sprintf "Incomplete LablGtk2 (%s): no %s/glib.mli." msg dir)
  else true

(** Detect and/or verify the Lablgtk2 location *)

let get_lablgtkdir () =
  match !prefs.lablgtkdir with
  | Some dir ->
    let msg = Manual in
    if check_lablgtkdir ~fatal:true msg dir then dir, msg
    else "", msg
  | None ->
    let msg = OCamlFind in
    let d1,_ = tryrun camlexec.find ["query";"lablgtk2.sourceview2"] in
    if d1 <> "" && check_lablgtkdir msg d1 then d1, msg
    else
      (* In debian wheezy, ocamlfind knows only of lablgtk2 *)
      let d2,_ = tryrun camlexec.find ["query";"lablgtk2"] in
      if d2 <> "" && d2 <> d1 && check_lablgtkdir msg d2 then d2, msg
      else
        let msg = Stdlib in
        let d3 = camllib^"/lablgtk2" in
        if check_lablgtkdir msg d3 then d3, msg
        else "", msg

(** Detect and/or verify the Lablgtk2 version *)

let check_lablgtk_version src dir = match src with
| Manual | Stdlib ->
  warn "Could not check the version of lablgtk2.\nMake sure your version is at least 2.18.3.";
  (true, "an unknown version")
| OCamlFind ->
  let v, _ = tryrun camlexec.find ["query"; "-format"; "%v"; "lablgtk2"] in
  try
    let vi = List.map s2i (numeric_prefix_list v) in
    if vi < [2; 16; 0] then
      (false, v)
    else if vi < [2; 18; 3] then
      begin
        (* Version 2.18.3 is known to report incorrectly as 2.18.0, and Launchpad packages report as version 2.16.0 due to a misconfigured META file; see https://bugs.launchpad.net/ubuntu/+source/lablgtk2/+bug/1577236 *)
        warn "Your installed lablgtk reports as %s.\n\
It is possible that the installed version is actually more recent\n\
but reports an incorrect version. If the installed version is\n\
actually more recent than 2.18.3, that's fine; if it is not,\n
CoqIDE will compile but may be very unstable." v;
        (true, "an unknown version")
      end
    else
      (true, v)
  with _ -> (false, v)

let pr_ide = function No -> "no" | Byte -> "only bytecode" | Opt -> "native"

exception Ide of ide

(** If the user asks an impossible coqide, we abort the configuration *)

let set_ide ide msg = match ide, !prefs.coqide with
  | No, Some (Byte|Opt)
  | Byte, Some Opt -> die (msg^":\n=> cannot build requested CoqIde")
  | _ ->
    cprintf "%s:\n=> %s CoqIde will be built." msg (pr_ide ide);
    raise (Ide ide)

let lablgtkdir = ref ""

(** Which CoqIde is possible ? Which one is requested ?
    This function also sets the lablgtkdir reference in case of success. *)

let check_coqide () =
  if !prefs.coqide = Some No then set_ide No "CoqIde manually disabled";
  let dir, via = get_lablgtkdir () in
  if dir = "" then set_ide No "LablGtk2 not found";
  let (ok, version) = check_lablgtk_version via dir in
  let found = sprintf "LablGtk2 found (%s, %s)" (get_source via) version in
  if not ok then set_ide No (found^", but too old (required >= 2.18.3, found " ^ version ^ ")");
  (* We're now sure to produce at least one kind of coqide *)
  lablgtkdir := shorten_camllib dir;
  if !prefs.coqide = Some Byte then set_ide Byte (found^", bytecode requested");
  if best_compiler<>"opt" then set_ide Byte (found^", but no native compiler");
  if not (Sys.file_exists (dir/"gtkThread.cmx")) then
    set_ide Byte (found^", but no native LablGtk2");
  if not (Sys.file_exists (camllib/"threads"/"threads.cmxa")) then
    set_ide Byte (found^", but no native threads");
  set_ide Opt (found^", with native threads")

let coqide =
  try check_coqide ()
  with Ide Opt -> "opt" | Ide Byte -> "byte" | Ide No -> "no"

(** System-specific CoqIde flags *)

let lablgtkincludes = ref ""
let idearchflags = ref ""
let idearchfile = ref ""
let idecdepsflags = ref ""
let idearchdef = ref "X11"

let coqide_flags () =
  if !lablgtkdir <> "" then lablgtkincludes := sprintf "-I %S" !lablgtkdir;
  match coqide, arch with
    | "opt", "Darwin" when !prefs.macintegration ->
      let osxdir,_ = tryrun camlexec.find ["query";"lablgtkosx"] in
      if osxdir <> "" then begin
        lablgtkincludes := sprintf "%s -I %S" !lablgtkincludes osxdir;
        idearchflags := "lablgtkosx.cma";
        idearchdef := "QUARTZ"
      end
    | "opt", "win32" ->
      idearchfile := "ide/ide_win32_stubs.o ide/coq_icon.o";
      idecdepsflags := "-custom";
      idearchflags := "-ccopt '-subsystem windows'";
      idearchdef := "WIN32"
    | _, "win32" ->
      idearchflags := "-ccopt '-subsystem windows'";
      idearchdef := "WIN32"
    | _ -> ()

let _ = coqide_flags ()


(** * strip command *)

let strip =
  if arch = "Darwin" then
    if hasnatdynlink then "true" else "strip"
  else
    if !prefs.profile || !prefs.debug then "true" else begin
    let _, all = run camlexec.find ["ocamlc";"-config"] in
    let strip = String.concat "" (List.map (fun l ->
        match string_split ' ' l with
        | "ranlib:" :: cc :: _ -> (* on windows, we greb the right strip *)
             Str.replace_first (Str.regexp "ranlib") "strip" cc
        | _ -> ""
      ) all) in
    if strip = "" then "strip" else strip
    end


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

let _ = if !prefs.withdoc then check_doc ()

(** * Installation directories : bindir, libdir, mandir, docdir, etc *)

let coqtop = Sys.getcwd ()

let unix = os_type_cygwin || not arch_is_win32

(** Variable name, description, ref in prefs, default dir, prefix-relative *)

type path_style =
  | Absolute of string (* Should start with a "/" *)
  | Relative of string (* Should not start with a "/" *)

let install = [
  "BINDIR", "the Coq binaries", !prefs.bindir,
    Relative "bin", Relative "bin", Relative "bin";
  "COQLIBINSTALL", "the Coq library", !prefs.libdir,
    Relative "lib", Relative "lib/coq", Relative "";
  "CONFIGDIR", "the Coqide configuration files", !prefs.configdir,
    Relative "config", Absolute "/etc/xdg/coq", Relative "ide";
  "DATADIR", "the Coqide data files", !prefs.datadir,
    Relative "share", Relative "share/coq", Relative "ide";
  "MANDIR", "the Coq man pages", !prefs.mandir,
    Relative "man", Relative "share/man", Relative "man";
  "DOCDIR", "the Coq documentation", !prefs.docdir,
    Relative "doc", Relative "share/doc/coq", Relative "doc";
  "COQDOCDIR", "the Coqdoc LaTeX files", !prefs.coqdocdir,
    Relative "latex", Relative "share/texmf/tex/latex/misc", Relative "tools/coqdoc";
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

let do_one_instdir (var,msg,uservalue,selfcontainedlayout,unixlayout,locallayout) =
  let dir,suffix =
    if !prefs.local then (use_suffix coqtop locallayout,locallayout)
    else match uservalue, !prefs.prefix with
    | Some d, p -> d,find_suffix p d
    | _, Some p ->
      let suffix = if arch_is_win32 then selfcontainedlayout else relativize unixlayout in
      use_suffix p suffix, suffix
    | _, p ->
      let suffix = if unix then unixlayout else selfcontainedlayout in
      let base = if unix then "/usr/local" else "C:/coq" in
      let dflt = use_suffix base suffix in
      let () = printf "Where should I install %s [%s]? " msg dflt in
      let line = read_line () in
      if line = "" then (dflt,suffix) else (line,find_suffix p line)
  in (var,msg,dir,suffix)

let install_dirs = List.map do_one_instdir install

let select var = List.find (fun (v,_,_,_) -> v=var) install_dirs

let coqlib,coqlibsuffix = let (_,_,d,s) = select "COQLIBINSTALL" in d,s

let docdir,docdirsuffix = let (_,_,d,s) = select "DOCDIR" in d,s

let configdir,configdirsuffix = let (_,_,d,s) = select "CONFIGDIR" in d,s

let datadir,datadirsuffix = let (_,_,d,s) = select "DATADIR" in d,s

(** * OCaml runtime flags *)

(** Do we use -custom (yes by default on Windows and MacOS) *)

let custom_os = arch_is_win32 || arch = "Darwin"

let use_custom = match !prefs.custom with
  | Some b -> b
  | None -> custom_os

let custom_flag = if use_custom then "-custom" else ""

let build_loadpath =
  ref "# you might want to set CAML_LD_LIBRARY_PATH by hand!"

let config_runtime () =
  match !prefs.vmbyteflags with
  | Some flags -> string_split ',' flags
  | _ when use_custom -> [custom_flag]
  | _ when !prefs.local ->
    ["-dllib";"-lcoqrun";"-dllpath";coqtop/"kernel/byterun"]
  | _ ->
    let ld="CAML_LD_LIBRARY_PATH" in
    build_loadpath := sprintf "export %s:='%s/kernel/byterun':$(%s)" ld coqtop ld;
    ["-dllib";"-lcoqrun";"-dllpath";coqlib/"kernel/byterun"]

let vmbyteflags = config_runtime ()

let esc s = if String.contains s ' ' then "\"" ^ s ^ "\"" else s

(** * Summary of the configuration *)

let print_summary () =
  let pr s = printf s in
  pr "\n";
  pr "  Architecture                : %s\n" arch;
  if operating_system <> "" then
    pr "  Operating system            : %s\n" operating_system;
  pr "  Coq VM bytecode link flags  : %s\n" (String.concat " " vmbyteflags);
  pr "  Other bytecode link flags   : %s\n" custom_flag;
  pr "  OCaml version               : %s\n" caml_version;
  pr "  OCaml binaries in           : %s\n" (esc camlbin);
  pr "  OCaml library in            : %s\n" (esc camllib);
  pr "  OCaml flambda flags         : %s\n" (String.concat " " !prefs.flambda_flags);
  pr "  Camlp5 version              : %s\n" camlp5_version;
  pr "  Camlp5 binaries in          : %s\n" (esc camlp5bindir);
  pr "  Camlp5 library in           : %s\n" (esc camlp5libdir);
  if best_compiler = "opt" then
    pr "  Native dynamic link support : %B\n" hasnatdynlink;
  if coqide <> "no" then
    pr "  Lablgtk2 library in         : %s\n" (esc !lablgtkdir);
  if !idearchdef = "QUARTZ" then
    pr "  Mac OS integration is on\n";
  pr "  CoqIde                      : %s\n" coqide;
  pr "  Documentation               : %s\n"
    (if !prefs.withdoc then "All" else "None");
  pr "  Web browser                 : %s\n" browser;
  pr "  Coq web site                : %s\n" !prefs.coqwebsite;
  pr "  Bytecode VM enabled         : %B\n" !prefs.bytecodecompiler;
  pr "  Native Compiler enabled     : %B\n\n" !prefs.nativecompiler;
  if !prefs.local then
    pr "  Local build, no installation...\n"
  else
    (pr "  Paths for true installation:\n";
     List.iter
       (fun (_,msg,dir,_) -> pr "  - %s will be copied in %s\n" msg (esc dir))
       install_dirs);
  pr "\n";
  pr "If anything is wrong above, please restart './configure'.\n\n";
  pr "*Warning* To compile the system for a new architecture\n";
  pr "          don't forget to do a 'make clean' before './configure'.\n"

let _ = print_summary ()


(** * Build the dev/ocamldebug-coq file *)

let write_dbg_wrapper f =
  safe_remove f;
  let o = open_out_bin f in  (* _bin to avoid adding \r on Cygwin/Windows *)
  let pr s = fprintf o s in
  pr "#!/bin/sh\n\n";
  pr "###### ocamldebug-coq : a wrapper around ocamldebug for Coq ######\n\n";
  pr "# DO NOT EDIT THIS FILE: automatically generated by ../configure #\n\n";
  pr "export COQTOP=%S\n" coqtop;
  pr "OCAMLDEBUG=%S\n" (camlbin^"/ocamldebug");
  pr "CAMLP5LIB=%S\n\n" camlp5libdir;
  pr ". $COQTOP/dev/ocamldebug-coq.run\n";
  close_out o;
  Unix.chmod f 0o555

let _ = write_dbg_wrapper "dev/ocamldebug-coq"

(** * Build the config/coq_config.ml file *)

let write_configml f =
  safe_remove f;
  let o = open_out f in
  let pr s = fprintf o s in
  let pr_s = pr "let %s = %S\n" in
  let pr_b = pr "let %s = %B\n" in
  let pr_i = pr "let %s = %d\n" in
  let pr_p s o = pr "let %s = %S\n" s
    (match o with Relative s -> s | Absolute s -> s) in
  let pr_l  n l = pr "let %s = [%s]\n" n (String.concat ";" (List.map (fun s -> "\"" ^ s ^ "\"") l)) in
  let pr_li n l = pr "let %s = [%s]\n" n (String.concat ";" (List.map string_of_int l)) in
  pr "(* DO NOT EDIT THIS FILE: automatically generated by ../configure *)\n";
  pr "(* Exact command that generated this file: *)\n";
  pr "(* %s *)\n\n" (String.concat " " (Array.to_list Sys.argv));
  pr_b "local" !prefs.local;
  pr "let vmbyteflags = ["; List.iter (pr "%S;") vmbyteflags; pr "]\n";
  pr_s "coqlib" coqlib;
  pr_s "configdir" configdir;
  pr_s "datadir" datadir;
  pr_s "docdir" docdir;
  pr_p "coqlibsuffix" coqlibsuffix;
  pr_p "configdirsuffix" configdirsuffix;
  pr_p "datadirsuffix" datadirsuffix;
  pr_p "docdirsuffix" docdirsuffix;
  pr_s "ocaml" camlexec.top;
  pr_s "ocamlfind" camlexec.find;
  pr_s "ocamllex" camlexec.lex;
  pr_s "camlbin" camlbin;
  pr_s "camllib" camllib;
  pr_s "camlp5o" camlp5o;
  pr_s "camlp5bin" camlp5bindir;
  pr_s "camlp5lib" camlp5libdir;
  pr_s "camlp5compat" camlp5compat;
  pr_s "cflags" cflags;
  pr_s "caml_flags" caml_flags;
  pr_s "best" best_compiler;
  pr_s "version" coq_version;
  pr_s "caml_version" caml_version;
  pr_li "caml_version_nums" caml_version_nums;
  pr_s "date" short_date;
  pr_s "compile_date" full_date;
  pr_s "arch" arch;
  pr_b "arch_is_win32" arch_is_win32;
  pr_s "exec_extension" exe;
  pr_s "coqideincl" !lablgtkincludes;
  pr_s "has_coqide" coqide;
  pr "let gtk_platform = `%s\n" !idearchdef;
  pr_b "has_natdynlink" hasnatdynlink;
  pr_s "natdynlinkflag" natdynlinkflag;
  pr_l "flambda_flags" !prefs.flambda_flags;
  pr_i "vo_magic_number" vo_magic;
  pr_i "state_magic_number" state_magic;
  pr_s "browser" browser;
  pr_s "wwwcoq" !prefs.coqwebsite;
  pr_s "wwwbugtracker" (!prefs.coqwebsite ^ "bugs/");
  pr_s "wwwrefman" (!prefs.coqwebsite ^ "distrib/V" ^ coq_version ^ "/refman/");
  pr_s "wwwstdlib" (!prefs.coqwebsite ^ "distrib/V" ^ coq_version ^ "/stdlib/");
  pr_s "localwwwrefman"  ("file:/" ^ docdir ^ "/html/refman");
  pr_b "bytecode_compiler" !prefs.bytecodecompiler;
  pr_b "native_compiler" !prefs.nativecompiler;

  let core_src_dirs = [ "config"; "dev"; "lib"; "clib"; "kernel"; "library";
                        "engine"; "pretyping"; "interp"; "parsing"; "proofs";
                        "tactics"; "toplevel"; "printing";
                        "grammar"; "ide"; "stm"; "vernac" ] in
  let core_src_dirs = List.fold_left (fun acc core_src_subdir -> acc ^ "  \"" ^ core_src_subdir ^ "\";\n")
                                    ""
                                    core_src_dirs in

  pr "\nlet core_src_dirs = [\n%s]\n" core_src_dirs;
  pr "\nlet plugins_dirs = [\n";

  let plugins = Sys.readdir "plugins" in
  Array.sort compare plugins;
  Array.iter
    (fun f ->
      let f' = "plugins/"^f in
      if Sys.is_directory f' && f.[0] <> '.' then pr "  %S;\n" f')
    plugins;
  pr "]\n";

  pr "\nlet all_src_dirs = core_src_dirs @ plugins_dirs\n";

  close_out o;
  Unix.chmod f 0o444

let _ = write_configml "config/coq_config.ml"

(** * Build the config/Makefile file *)

let write_makefile f =
  safe_remove f;
  let o = open_out f in
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
  pr "# Local use (no installation)\n";
  pr "LOCAL=%B\n\n" !prefs.local;
  pr "# Bytecode link flags : should we use -custom or not ?\n";
  pr "CUSTOM=%s\n" custom_flag;
  pr "VMBYTEFLAGS=%s\n" (String.concat " " vmbyteflags);
  pr "%s\n\n" !build_loadpath;
  pr "# Paths for true installation\n";
  List.iter (fun (v,msg,_,_) -> pr "# %s: path for %s\n" v msg) install_dirs;
  List.iter (fun (v,_,dir,_) -> pr "%s=%S\n" v dir) install_dirs;
  pr "\n# Coq version\n";
  pr "VERSION=%s\n" coq_version;
  pr "VERSION4MACOS=%s\n\n" coq_macos_version;
  pr "# Objective-Caml compile command\n";
  pr "OCAML=%S\n" camlexec.top;
  pr "OCAMLFIND=%S\n" camlexec.find;
  pr "OCAMLLEX=%S\n" camlexec.lex;
  pr "OCAMLYACC=%S\n" camlexec.yacc;
  pr "# The best compiler: native (=opt) or bytecode (=byte)\n";
  pr "BEST=%s\n\n" best_compiler;
  pr "# Ocaml version number\n";
  pr "CAMLVERSION=%s\n\n" camltag;
  pr "# Ocaml libraries\n";
  pr "CAMLLIB=%S\n\n" camllib;
  pr "# Ocaml .h directory\n";
  pr "CAMLHLIB=%S\n\n" camllib;
  pr "# Caml link command and Caml make top command\n";
  pr "# Caml flags\n";
  pr "CAMLFLAGS=%s %s\n" caml_flags coq_caml_flags;
  pr "# User compilation flag\n";
  pr "USERFLAGS=\n\n";
  (* XXX make this configurable *)
  pr "FLAMBDA_FLAGS=%s\n" (String.concat " " !prefs.flambda_flags);
  pr "# Flags for GCC\n";
  pr "CFLAGS=%s\n\n" cflags;
  pr "# Compilation debug flags\n";
  pr "CAMLDEBUG=%s\n" coq_debug_flag;
  pr "CAMLDEBUGOPT=%s\n\n" coq_debug_flag;
  pr "# Compilation profile flag\n";
  pr "CAMLTIMEPROF=%s\n\n" coq_profile_flag;
  pr "# Camlp5 : flavor, binaries, libraries ...\n";
  pr "# NB : avoid using CAMLP5LIB (conflict under Windows)\n";
  pr "CAMLP5O=%s\n" (win_aware_quote_executable camlp5o);
  pr "CAMLP5COMPAT=%s\n" camlp5compat;
  pr "MYCAMLP5LIB=%S\n\n" camlp5libdir;
  pr "# Your architecture\n";
  pr "# Can be obtain by UNIX command arch\n";
  pr "ARCH=%s\n" arch;
  pr "HASNATDYNLINK=%s\n\n" natdynlinkflag;
  pr "# Supplementary libs for some systems, currently:\n";
  pr "#  . Sun Solaris: -cclib -lunix -cclib -lnsl -cclib -lsocket\n";
  pr "#  . others     : -cclib -lunix\n";
  pr "# executable files extension, currently:\n";
  pr "#  Unix systems:\n";
  pr "#  Win32 systems : .exe\n";
  pr "EXE=%s\n" exe;
  pr "DLLEXT=%s\n\n" dll;
  pr "# the command MKDIR (try to use mkdirhier if you have problems)\n";
  pr "MKDIR=mkdir -p\n\n";
  pr "#the command STRIP\n";
  pr "# Unix systems and profiling: true\n";
  pr "# Unix systems and no profiling: strip\n";
  pr "STRIP=%s\n\n" strip;
  pr "# LablGTK\n";
  pr "COQIDEINCLUDES=%s\n\n" !lablgtkincludes;
  pr "# CoqIde (no/byte/opt)\n";
  pr "HASCOQIDE=%s\n" coqide;
  pr "IDEFLAGS=%s\n" !idearchflags;
  pr "IDEOPTCDEPS=%s\n" !idearchfile;
  pr "IDECDEPS=%s\n" !idearchfile;
  pr "IDECDEPSFLAGS=%s\n" !idecdepsflags;
  pr "IDEINT=%s\n\n" !idearchdef;
  pr "# Defining REVISION\n";
  pr "CHECKEDOUT=%s\n\n" vcs;
  pr "# Option to control compilation and installation of the documentation\n";
  pr "WITHDOC=%s\n\n" (if !prefs.withdoc then "all" else "no");
  pr "# Option to produce precompiled files for native_compute\n";
  pr "NATIVECOMPUTE=%s\n" (if !prefs.nativecompiler then "-native-compiler" else "");
  pr "COQWARNERROR=%s\n" (if !prefs.warn_error then "-w +default" else "");
  close_out o;
  Unix.chmod f 0o444

let _ = write_makefile "config/Makefile"

let write_macos_metadata exec =
  let f = "config/Info-"^exec^".plist" in
  let () = safe_remove f in
  let o = open_out f in
  let pr s = fprintf o s in
  pr "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n";
  pr "<!DOCTYPE plist PUBLIC \"-//Apple//DTD PLIST 1.0//EN\" \"http://www.apple.com/DTDs/PropertyList-1.0.dtd\">\n";
  pr "<plist version=\"1.0\">\n";
  pr "<dict>\n";
  pr "    <key>CFBundleIdentifier</key>\n";
  pr "    <string>fr.inria.coq.%s</string>\n" exec;
  pr "    <key>CFBundleName</key>\n";
  pr "    <string>%s</string>\n" exec;
  pr "    <key>CFBundleVersion</key>\n";
  pr "    <string>%s</string>\n" coq_macos_version;
  pr "    <key>CFBundleShortVersionString</key>\n";
  pr "    <string>%s</string>\n" coq_macos_version;
  pr "    <key>CFBundleInfoDictionaryVersion</key>\n";
  pr "    <string>6.0</string>\n";
  pr "</dict>\n";
  pr "</plist>\n";
  let () = close_out o in
  Unix.chmod f 0o444

let () = if arch = "Darwin" then
List.iter write_macos_metadata distributed_exec

let write_configpy f =
  safe_remove f;
  let o = open_out f in
  let pr s = fprintf o s in
  let pr_s = pr "%s = '%s'\n" in
  pr "# DO NOT EDIT THIS FILE: automatically generated by ../configure\n";
  pr_s "version" coq_version

let _ = write_configpy "config/coq_config.py"
