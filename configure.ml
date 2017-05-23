(**********************************)

(**  Configuration script for Coq *)

(**********************************)

(** This file should be run via: ocaml configure.ml <opts>
    You could also use our wrapper ./configure <opts> *)

#load "unix.cma"
#load "str.cma"
open Printf

let coq_version = "trunk"
let coq_macos_version = "8.6.90" (** "[...] should be a string comprised of
three non-negative, period-separated integers [...]" *)
let vo_magic = 8691
let state_magic = 58691
let distributed_exec = ["coqtop";"coqc";"coqchk";"coqdoc";"coqmktop";"coqworkmgr";
"coqdoc";"coq_makefile";"coq-tex";"gallina";"coqwc";"csdpcert";"coqdep"]

let verbose = ref false (* for debugging this script *)

(** * Utility functions *)

let die msg = eprintf "%s\nConfiguration script failed!\n" msg; exit 1

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
      if fatal then die msg else (printf "W: %s\n" msg; "", [])

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

(** As per bug #4828, ocamlfind on Windows/Cygwin barfs if you pass it
    a quoted path to camlpXo via -pp.  So we only quote camlpXo on not
    Windows, and warn on Windows if the path contains spaces *)
let contains_suspicious_characters str =
  List.fold_left (fun b ch -> String.contains str ch || b) false [' '; '\t']

let win_aware_quote_executable str =
  if not (os_type_win32 || os_type_cygwin) then
    sprintf "%S" str
  else
    let _ = if contains_suspicious_characters str then
      printf "*Warning* The string %S contains suspicious characters; ocamlfind might fail\n" str in
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
  sprintf "%s %d %d %d:%d:%d" (String.sub month 0 3) now.Unix.tm_mday year
    now.Unix.tm_hour now.Unix.tm_min now.Unix.tm_sec

let short_date, full_date = get_date ()


(** Create the bin/ directory if non-existent *)

let _ = if not (dir_exists "bin") then Unix.mkdir "bin" 0o755


(** * Command-line parsing *)

type ide = Opt | Byte | No

let get_bool = function
  | "true" | "yes" | "y" | "all" -> true
  | "false" | "no" | "n" -> false
  | s -> raise (Arg.Bad ("boolean argument expected instead of "^s))

let get_ide = function
  | "opt" -> Opt
  | "byte" -> Byte
  | "no" -> No
  | s -> raise (Arg.Bad ("(opt|byte|no) argument expected instead of "^s))

let arg_bool r = Arg.String (fun s -> r := get_bool s)

let arg_string_option r = Arg.String (fun s -> r := Some s)

module Prefs = struct
  let prefix = ref (None : string option)
  let local = ref false
  let vmbyteflags = ref (None : string option)
  let custom = ref (None : bool option)
  let bindir = ref (None : string option)
  let libdir = ref (None : string option)
  let configdir = ref (None : string option)
  let datadir = ref (None : string option)
  let mandir = ref (None : string option)
  let docdir = ref (None : string option)
  let emacslib = ref (None : string option)
  let coqdocdir = ref (None : string option)
  let ocamlfindcmd = ref (None : string option)
  let lablgtkdir = ref (None : string option)
  let camlp5dir = ref (None : string option)
  let arch = ref (None : string option)
  let natdynlink = ref true
  let coqide = ref (None : ide option)
  let macintegration = ref true
  let browser = ref (None : string option)
  let withdoc = ref false
  let geoproof = ref false
  let byteonly = ref false
  let debug = ref true
  let profile = ref false
  let annotate = ref false
  (* Note, disabling this should be OK, but be careful with the
     sharing invariants.
  *)
  let safe_string = ref true
  let nativecompiler = ref (not (os_type_win32 || os_type_cygwin))
  let coqwebsite = ref "http://coq.inria.fr/"
  let force_caml_version = ref false
  let warn_error = ref false
end

(* TODO : earlier any option -foo was also available as --foo *)

let args_options = Arg.align [
  "-prefix", arg_string_option Prefs.prefix,
    "<dir> Set installation directory to <dir>";
  "-local", Arg.Set Prefs.local,
    " Set installation directory to the current source tree";
  "-vmbyteflags", arg_string_option Prefs.vmbyteflags,
    "<flags> Comma-separated link flags for the VM of coqtop.byte";
  "-custom", Arg.Unit (fun () -> Prefs.custom := Some true),
    " Build bytecode executables with -custom (not recommended)";
  "-no-custom", Arg.Unit (fun () -> Prefs.custom := Some false),
    " Do not build with -custom on Windows and MacOS";
  "-bindir", arg_string_option Prefs.bindir,
    "<dir> Where to install bin files";
  "-libdir", arg_string_option Prefs.libdir,
    "<dir> Where to install lib files";
  "-configdir", arg_string_option Prefs.configdir,
    "<dir> Where to install config files";
  "-datadir", arg_string_option Prefs.datadir,
    "<dir> Where to install data files";
  "-mandir", arg_string_option Prefs.mandir,
    "<dir> Where to install man files";
  "-docdir", arg_string_option Prefs.docdir,
    "<dir> Where to install doc files";
  "-emacslib", arg_string_option Prefs.emacslib,
    "<dir> Where to install emacs files";
  "-emacs", Arg.String (fun s ->
      printf "Warning: obsolete -emacs option\n";
      Prefs.emacslib := Some s),
    "<dir> Obsolete: same as -emacslib";
  "-coqdocdir", arg_string_option Prefs.coqdocdir,
    "<dir> Where to install Coqdoc style files";
  "-ocamlfind", arg_string_option Prefs.ocamlfindcmd,
    "<dir> Specifies the ocamlfind command to use";
  "-lablgtkdir", arg_string_option Prefs.lablgtkdir,
    "<dir> Specifies the path to the Lablgtk library";
  "-usecamlp5", Arg.Unit (fun () -> ()),
    "Deprecated";
  "-camlp5dir",
    Arg.String (fun s -> Prefs.camlp5dir:=Some s),
    "<dir> Specifies where is the Camlp5 library and tells to use it";
  "-arch", arg_string_option Prefs.arch,
    "<arch> Specifies the architecture";
  "-opt", Arg.Unit (fun () -> printf "Warning: obsolete -opt option\n"),
    " Obsolete: native OCaml executables detected automatically";
  "-natdynlink", arg_bool Prefs.natdynlink,
    "(yes|no) Use dynamic loading of native code or not";
  "-coqide", Arg.String (fun s -> Prefs.coqide := Some (get_ide s)),
    "(opt|byte|no) Specifies whether or not to compile Coqide";
  "-nomacintegration", Arg.Clear Prefs.macintegration,
    " Do not try to build coqide mac integration";
  "-browser", arg_string_option Prefs.browser,
    "<command> Use <command> to open URL %s";
  "-nodoc", Arg.Clear Prefs.withdoc,
    " Deprecated: use -with-doc no instead";
  "-with-doc", arg_bool Prefs.withdoc,
    "(yes|no) Compile the documentation or not";
  "-with-geoproof", arg_bool Prefs.geoproof,
    "(yes|no) Use Geoproof binding or not";
  "-byte-only", Arg.Set Prefs.byteonly,
    " Compiles only bytecode version of Coq";
  "-byteonly", Arg.Set Prefs.byteonly,
    " Compiles only bytecode version of Coq";
  "-debug", Arg.Set Prefs.debug,
    " Deprecated";
  "-nodebug", Arg.Clear Prefs.debug,
    " Do not add debugging information in the Coq executables";
  "-profile", Arg.Set Prefs.profile,
    " Add profiling information in the Coq executables";
  "-annotate", Arg.Set Prefs.annotate,
    " Dumps ml annotation files while compiling Coq";
  "-makecmd", Arg.String (fun _ -> printf "Warning: obsolete -makecmd option\n"),
    "<command> Obsolete: name of GNU Make command";
  "-native-compiler", arg_bool Prefs.nativecompiler,
    "(yes|no) Compilation to native code for conversion and normalization";
  "-coqwebsite", Arg.Set_string Prefs.coqwebsite,
    " URL of the coq website";
  "-force-caml-version", Arg.Set Prefs.force_caml_version,
    " Force OCaml version";
  "-warn-error", Arg.Set Prefs.warn_error,
    " Make OCaml warnings into errors";
]

let parse_args () =
  Arg.parse
    args_options
    (fun s -> raise (Arg.Bad ("Unknown option: "^s)))
    "Available options for configure are:";
  if !Prefs.local && !Prefs.prefix <> None then
    die "Options -prefix and -local are incompatible."

let _ = parse_args ()

(** Default OCaml binaries *)

type camlexec =
 { mutable find : string;
   mutable top : string;
   mutable lex : string; }

let camlexec =
  { find = "ocamlfind";
    top = "ocaml";
    lex = "ocamllex"; }

let reset_caml_lex c o = c.lex <- o
let reset_caml_top c o = c.top <- o
let reset_caml_find c o = c.find <- o

let coq_debug_flag = if !Prefs.debug then "-g" else ""
let coq_profile_flag = if !Prefs.profile then "-p" else ""
let coq_annotate_flag =
  if !Prefs.annotate
  then if program_in_path "ocamlmerlin" then "-bin-annot" else "-annot"
  else ""

let coq_safe_string =
  if !Prefs.safe_string then "-safe-string" else ""

let cflags = "-Wall -Wno-unused -g -O2"

(** * Architecture *)

let arch_progs =
  [("/bin/uname",["-s"]);
   ("/usr/bin/uname",["-s"]);
   ("/bin/arch", []);
   ("/usr/bin/arch", []);
   ("/usr/ucb/arch", []) ]

let query_arch () =
  printf "I can not automatically find the name of your architecture.\n";
  printf "Give me a name, please [win32 for Win95, Win98 or WinNT]: %!";
  read_line ()

let rec try_archs = function
  | (prog,args)::rest when is_executable prog ->
    let arch, _ = tryrun prog args in
    if arch <> "" then arch else try_archs rest
  | _ :: rest -> try_archs rest
  | [] -> query_arch ()

let arch = match !Prefs.arch with
  | Some a -> a
  | None ->
    let arch,_ = tryrun "uname" ["-s"] in
    if starts_with arch "CYGWIN" then "win32"
    else if starts_with arch "MINGW32" then "win32"
    else if arch <> "" then arch
    else try_archs arch_progs

(** NB: [arch_win32] is broader than [os_type_win32], cf. cygwin *)

let arch_win32 = (arch = "win32")

let exe = exe := if arch_win32 then ".exe" else ""; !exe
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

(** * Browser command *)

let browser =
  match !Prefs.browser with
  | Some b -> b
  | None when arch_win32 -> "start %s"
  | None when arch = "Darwin" -> "open %s"
  | _ -> "firefox -remote \"OpenURL(%s,new-tab)\" || firefox %s &"

(** * OCaml programs *)

let camlbin, caml_version, camllib =
  let () = match !Prefs.ocamlfindcmd with
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
    let caml_version, _ = run camlexec.find ["ocamlc";"-version"] in
    let camllib, _ = run camlexec.find ["printconf";"stdlib"] in
    let camlbin = (* TODO beurk beurk beurk *)
      Filename.dirname (Filename.dirname camllib) / "bin/" in
    let () =
      if is_executable (camlbin / "ocamllex")
      then reset_caml_lex camlexec (camlbin / "ocamllex") in
    let () =
      if is_executable (camlbin / "ocaml")
      then reset_caml_top camlexec (camlbin / "ocaml") in
    camlbin, caml_version, camllib

let camlp4compat = "-loc loc"

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
  if caml_version_nums >= [4;2;1] then
    printf "You have OCaml %s. Good!\n" caml_version
  else
    let () = printf "Your version of OCaml is %s.\n" caml_version in
    if !Prefs.force_caml_version then
      printf "*Warning* Your version of OCaml is outdated.\n"
    else
      die "You need OCaml 4.02.1 or later."

let _ = check_caml_version ()

let coq_debug_flag_opt =
  if caml_version_nums >= [3;10] then coq_debug_flag else ""

let camltag = match caml_version_list with
  | x::y::_ -> "OCAML"^x^y
  | _ -> assert false

(** Explanation of disabled warnings:
    3: deprecated warning (not error for non minimum supported ocaml)
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
*)
let coq_warn_flags =
  let warnings = "-w +a-4-9-27-41-42-44-45-48-50" in
  let errors =
    if !Prefs.warn_error
    then "-warn-error +a"
         ^ (if caml_version_nums > [4;2;3]
            then "-3-56"
            else "")
    else ""
  in
  warnings ^ " " ^ errors



(** * CamlpX configuration *)

(* Convention: we use camldir as a prioritary location for camlpX, if given *)
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

let which_camlpX base =
  let file = Filename.concat camlbin base in
  if is_executable file then file else which base

(* TODO: camlp5dir should rather be the *binary* location, just as camldir *)
(* TODO: remove the late attempts at finding gramlib.cma *)

let check_camlp5 testcma = match !Prefs.camlp5dir with
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
      let camlp5o = which_camlpX "camlp5o" in
      let dir,_ = tryrun camlp5o ["-where"] in
      dir, camlp5o
    with Not_found ->
      die "No Camlp5 installation found."

let check_camlp5_version camlp5o =
  let version_line, _ = run ~err:StdOut camlp5o ["-v"] in
  let version = List.nth (string_split ' ' version_line) 2 in
  match numeric_prefix_list version with
  | major::minor::_ when s2i major > 6 || (s2i major, s2i minor) >= (6,6) ->
    printf "You have Camlp5 %s. Good!\n" version; version
  | _ -> die "Error: unsupported Camlp5 (version < 6.06 or unrecognized).\n"

let config_camlpX () =
    let camlp5mod = "gramlib" in
    let camlp5libdir, camlp5o = check_camlp5 (camlp5mod^".cma") in
    let camlp5_version = check_camlp5_version camlp5o in
    "camlp5", camlp5o, Filename.dirname camlp5o, camlp5libdir, camlp5mod, camlp5_version

let camlpX, camlpXo, camlpXbindir, fullcamlpXlibdir, camlpXmod, camlpX_version = config_camlpX ()

let shorten_camllib s =
  if starts_with s (camllib^"/") then
    let l = String.length camllib + 1 in
    "+" ^ String.sub s l (String.length s - l)
  else s

let camlpXlibdir = shorten_camllib fullcamlpXlibdir

(** * Native compiler *)

let msg_byteonly () =
  printf "Only the bytecode version of Coq will be available.\n"

let msg_no_ocamlopt () =
  printf "Cannot find the OCaml native-code compiler.\n"; msg_byteonly ()

let msg_no_camlpX_cmxa () =
  printf "Cannot find the native-code library of %s.\n" camlpX; msg_byteonly ()

let msg_no_dynlink_cmxa () =
  printf "Cannot find native-code dynlink library.\n"; msg_byteonly ();
  printf "For building a native-code Coq, you may try to first\n";
  printf "compile and install a dummy dynlink.cmxa (see dev/dynlink.ml)\n";
  printf "and then run ./configure -natdynlink no\n"

let check_native () =
  let () = if !Prefs.byteonly then raise Not_found in
  let version, _ = tryrun camlexec.find ["opt";"-version"] in
  if version = "" then let () = msg_no_ocamlopt () in raise Not_found
  else if not (Sys.file_exists (fullcamlpXlibdir/camlpXmod^".cmxa"))
  then let () = msg_no_camlpX_cmxa () in raise Not_found
  else if fst (tryrun camlexec.find ["query";"dynlink"]) = ""
  then let () = msg_no_dynlink_cmxa () in raise Not_found
  else
    let () =
      if version <> caml_version then
	printf
	  "Warning: Native and bytecode compilers do not have the same version!\n"
    in printf "You have native-code compilation. Good!\n"

let best_compiler =
  try check_native (); "opt" with Not_found -> "byte"

(** * Native dynlink *)

let hasnatdynlink = !Prefs.natdynlink && best_compiler = "opt"

let natdynlinkflag =
  if hasnatdynlink then "true" else "false"


(** * OS dependent libraries *)

let osdeplibs = "-cclib -lunix"

let operating_system, osdeplibs =
  if starts_with arch "sun4" then
    let os, _ = run "uname" ["-r"] in
    if starts_with os "5" then
      "Sun Solaris "^os, osdeplibs^" -cclib -lnsl -cclib -lsocket"
    else
      "Sun OS "^os, osdeplibs
  else
    (try Sys.getenv "OS" with Not_found -> ""), osdeplibs


(** * lablgtk2 and CoqIDE *)

type source = Manual | OCamlFind | Stdlib

let get_source = function
| Manual -> "manually provided"
| OCamlFind -> "via ocamlfind"
| Stdlib -> "in OCaml library"

(** Is some location a suitable LablGtk2 installation ? *)

let check_lablgtkdir ?(fatal=false) src dir =
  let yell msg = if fatal then die msg else (printf "%s\n" msg; false) in
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
  match !Prefs.lablgtkdir with
  | Some dir ->
    let msg = Manual in
    if check_lablgtkdir ~fatal:true msg dir then dir, msg
    else "", msg
  | None ->
    let msg = OCamlFind in
    let d1,_ = tryrun "ocamlfind" ["query";"lablgtk2.sourceview2"] in
    if d1 <> "" && check_lablgtkdir msg d1 then d1, msg
    else
      (* In debian wheezy, ocamlfind knows only of lablgtk2 *)
      let d2,_ = tryrun "ocamlfind" ["query";"lablgtk2"] in
      if d2 <> "" && d2 <> d1 && check_lablgtkdir msg d2 then d2, msg
      else
        let msg = Stdlib in
        let d3 = camllib^"/lablgtk2" in
        if check_lablgtkdir msg d3 then d3, msg
        else "", msg

(** Detect and/or verify the Lablgtk2 version *)

let check_lablgtk_version src dir = match src with
| Manual | Stdlib ->
  let test accu f =
    if accu then
      let test = sprintf "grep -q -w %s %S/glib.mli" f dir in
      Sys.command test = 0
    else false
  in
  let heuristics = [
    "convert_with_fallback";
    "wrap_poll_func"; (** Introduced in lablgtk 2.16 *)
  ] in
  let ans = List.fold_left test true heuristics in
  if ans then printf "Warning: could not check the version of lablgtk2.\n";
  (ans, "an unknown version")
| OCamlFind ->
  let v, _ = tryrun "ocamlfind" ["query"; "-format"; "%v"; "lablgtk2"] in
  try
    let vi = List.map s2i (numeric_prefix_list v) in
    ([2; 16] <= vi, v)
  with _ -> (false, v)

let pr_ide = function No -> "no" | Byte -> "only bytecode" | Opt -> "native"

exception Ide of ide

(** If the user asks an impossible coqide, we abort the configuration *)

let set_ide ide msg = match ide, !Prefs.coqide with
  | No, Some (Byte|Opt)
  | Byte, Some Opt -> die (msg^":\n=> cannot build requested CoqIde")
  | _ ->
    printf "%s:\n=> %s CoqIde will be built.\n" msg (pr_ide ide);
    raise (Ide ide)

let lablgtkdir = ref ""

(** Which CoqIde is possible ? Which one is requested ?
    This function also sets the lablgtkdir reference in case of success. *)

let check_coqide () =
  if !Prefs.coqide = Some No then set_ide No "CoqIde manually disabled";
  let dir, via = get_lablgtkdir () in
  if dir = "" then set_ide No "LablGtk2 not found";
  let (ok, version) = check_lablgtk_version via dir in
  let found = sprintf "LablGtk2 found (%s, %s)" (get_source via) version in
  if not ok then set_ide No (found^", but too old (required >= 2.16, found " ^ version ^ ")");
  (* We're now sure to produce at least one kind of coqide *)
  lablgtkdir := shorten_camllib dir;
  if !Prefs.coqide = Some Byte then set_ide Byte (found^", bytecode requested");
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
    | "opt", "Darwin" when !Prefs.macintegration ->
      let osxdir,_ = tryrun "ocamlfind" ["query";"lablgtkosx"] in
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
    if !Prefs.profile || !Prefs.debug then "true" else begin
    let _, all = run camlexec.find ["ocamlc";"-config"] in
    let strip = String.concat "" (List.map (fun l ->
        match string_split ' ' l with
        | "ranlib:" :: cc :: _ -> (* on windows, we greb the right strip *)
             Str.replace_first (Str.regexp "ranlib") "strip" cc
        | _ -> ""
      ) all) in
    if strip = "" then "strip" else strip
    end

(** * md5sum command *)

let md5sum =
  if List.mem arch ["Darwin"; "FreeBSD"; "OpenBSD"]
  then "md5 -q" else "md5sum"


(** * Documentation : do we have latex, hevea, ... *)

let check_doc () =
  let err s =
    printf "%s was not found; documentation will not be available\n" s;
    raise Not_found
  in
  try
    if not !Prefs.withdoc then raise Not_found;
    if not (program_in_path "latex") then err "latex";
    if not (program_in_path "hevea") then err "hevea";
    if not (program_in_path "hacha") then err "hacha";
    if not (program_in_path "fig2dev") then err "fig2dev";
    if not (program_in_path "convert") then err "convert";
    true
  with Not_found -> false

let withdoc = check_doc ()


(** * Installation directories : bindir, libdir, mandir, docdir, etc *)

let coqtop = Sys.getcwd ()

let unix = os_type_cygwin || not arch_win32

(** Variable name, description, ref in Prefs, default dir, prefix-relative *)

let install = [
  "BINDIR", "the Coq binaries", Prefs.bindir,
    (if unix then "/usr/local/bin" else "C:/coq/bin"),
    "/bin";
  "COQLIBINSTALL", "the Coq library", Prefs.libdir,
    (if unix then "/usr/local/lib/coq" else "C:/coq/lib"),
    (if arch_win32 then "" else "/lib/coq");
  "CONFIGDIR", "the Coqide configuration files", Prefs.configdir,
    (if unix then "/etc/xdg/coq" else "C:/coq/config"),
    (if arch_win32 then "/config" else "/etc/xdg/coq");
  "DATADIR", "the Coqide data files", Prefs.datadir,
    (if unix then "/usr/local/share/coq" else "C:/coq/share"),
    "/share/coq";
  "MANDIR", "the Coq man pages", Prefs.mandir,
    (if unix then "/usr/local/share/man" else "C:/coq/man"),
    "/share/man";
  "DOCDIR", "the Coq documentation", Prefs.docdir,
    (if unix then "/usr/local/share/doc/coq" else "C:/coq/doc"),
    "/share/doc/coq";
  "EMACSLIB", "the Coq Emacs mode", Prefs.emacslib,
    (if unix then "/usr/local/share/emacs/site-lisp" else "C:/coq/emacs"),
    (if arch_win32 then "/emacs" else "/share/emacs/site-lisp");
  "COQDOCDIR", "the Coqdoc LaTeX files", Prefs.coqdocdir,
    (if unix then "/usr/local/share/texmf/tex/latex/misc" else "C:/coq/latex"),
    (if arch_win32 then "/latex" else "/share/emacs/site-lisp");
 ]

let do_one_instdir (var,msg,r,dflt,suff) =
  let dir = match !r, !Prefs.prefix with
    | Some d, _ -> d
    | _, Some p -> p^suff
    | _ ->
      let () = printf "Where should I install %s [%s]? " msg dflt in
      let line = read_line () in
      if line = "" then dflt else line
  in (var,msg,dir,dir<>dflt)

let do_one_noinst (var,msg,_,_,_) =
  if var="CONFIGDIR" || var="DATADIR" then (var,msg,coqtop^"/ide",true)
  else (var,msg,"",false)

let install_dirs =
  let f = if !Prefs.local then do_one_noinst else do_one_instdir in
  List.map f install

let select var = List.find (fun (v,_,_,_) -> v=var) install_dirs

let libdir = let (_,_,d,_) = select "COQLIBINSTALL" in d

let docdir = let (_,_,d,_) = select "DOCDIR" in d

let configdir =
  let (_,_,d,b) = select "CONFIGDIR" in if b then Some d else None

let datadir =
  let (_,_,d,b) = select "DATADIR" in if b then Some d else None


(** * OCaml runtime flags *)

(** Do we use -custom (yes by default on Windows and MacOS) *)

let custom_os = arch_win32 || arch = "Darwin"

let use_custom = match !Prefs.custom with
  | Some b -> b
  | None -> custom_os

let custom_flag = if use_custom then "-custom" else ""

let build_loadpath =
  ref "# you might want to set CAML_LD_LIBRARY_PATH by hand!"

let config_runtime () =
  match !Prefs.vmbyteflags with
  | Some flags -> string_split ',' flags
  | _ when use_custom -> [custom_flag]
  | _ when !Prefs.local ->
    ["-dllib";"-lcoqrun";"-dllpath";coqtop/"kernel/byterun"]
  | _ ->
    let ld="CAML_LD_LIBRARY_PATH" in
    build_loadpath := sprintf "export %s:='%s/kernel/byterun':$(%s)" ld coqtop ld;
    ["-dllib";"-lcoqrun";"-dllpath";libdir/"kernel/byterun"]

let vmbyteflags = config_runtime ()


(** * Summary of the configuration *)

let print_summary () =
  let pr s = printf s in
  pr "\n";
  pr "  Architecture                : %s\n" arch;
  if operating_system <> "" then
    pr "  Operating system            : %s\n" operating_system;
  pr "  Coq VM bytecode link flags  : %s\n" (String.concat " " vmbyteflags);
  pr "  Other bytecode link flags   : %s\n" custom_flag;
  pr "  OS dependent libraries      : %s\n" osdeplibs;
  pr "  OCaml version               : %s\n" caml_version;
  pr "  OCaml binaries in           : %s\n" camlbin;
  pr "  OCaml library in            : %s\n" camllib;
  pr "  %s version              : %s\n"     (String.capitalize camlpX) camlpX_version;
  pr "  %s binaries in          : %s\n"     (String.capitalize camlpX) camlpXbindir;
  pr "  %s library in           : %s\n"     (String.capitalize camlpX) camlpXlibdir;
  if best_compiler = "opt" then
    pr "  Native dynamic link support : %B\n" hasnatdynlink;
  if coqide <> "no" then
    pr "  Lablgtk2 library in         : %s\n" !lablgtkdir;
  if !idearchdef = "QUARTZ" then
    pr "  Mac OS integration is on\n";
  pr "  CoqIde                      : %s\n" coqide;
  pr "  Documentation               : %s\n"
    (if withdoc then "All" else "None");
  pr "  Web browser                 : %s\n" browser;
  pr "  Coq web site                : %s\n\n" !Prefs.coqwebsite;
  if not !Prefs.nativecompiler then
    pr "  Native compiler for conversion and normalization disabled\n\n";
  if !Prefs.local then
    pr "  Local build, no installation...\n"
  else
    (pr "  Paths for true installation:\n";
     List.iter
       (fun (_,msg,dir,_) -> pr "  - %s will be copied in %s\n" msg dir)
       install_dirs);
  pr "\n";
  pr "If anything is wrong above, please restart './configure'.\n\n";
  pr "*Warning* To compile the system for a new architecture\n";
  pr "          don't forget to do a 'make clean' before './configure'.\n"

let _ = print_summary ()


(** * Build the dev/ocamldebug-coq file *)

let write_dbg_wrapper f =
  safe_remove f;
  let o = open_out f in
  let pr s = fprintf o s in
  pr "#!/bin/sh\n\n";
  pr "###### ocamldebug-coq : a wrapper around ocamldebug for Coq ######\n\n";
  pr "# DO NOT EDIT THIS FILE: automatically generated by ../configure #\n\n";
  pr "export COQTOP=%S\n" coqtop;
  pr "OCAMLDEBUG=%S\n" (camlbin^"/ocamldebug");
  pr "CAMLP4LIB=%S\n\n" camlpXlibdir;
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
  let pr_o s o = pr "let %s = %s\n" s
    (match o with None -> "None" | Some d -> sprintf "Some %S" d)
  in
  pr "(* DO NOT EDIT THIS FILE: automatically generated by ../configure *)\n";
  pr "(* Exact command that generated this file: *)\n";
  pr "(* %s *)\n\n" (String.concat " " (Array.to_list Sys.argv));
  pr_b "local" !Prefs.local;
  pr "let vmbyteflags = ["; List.iter (pr "%S;") vmbyteflags; pr "]\n";
  pr_o "coqlib" (if !Prefs.local then None else Some libdir);
  pr_o "configdir" configdir;
  pr_o "datadir" datadir;
  pr_s "docdir" docdir;
  pr_s "ocaml" camlexec.top;
  pr_s "ocamlfind" camlexec.find;
  pr_s "ocamllex" camlexec.lex;
  pr_s "camlbin" camlbin;
  pr_s "camllib" camllib;
  pr_s "camlp4" camlpX;
  pr_s "camlp4o" camlpXo;
  pr_s "camlp4bin" camlpXbindir;
  pr_s "camlp4lib" camlpXlibdir;
  pr_s "camlp4compat" camlp4compat;
  pr_s "cflags" cflags;
  pr_s "best" best_compiler;
  pr_s "osdeplibs" osdeplibs;
  pr_s "version" coq_version;
  pr_s "caml_version" caml_version;
  pr_s "date" short_date;
  pr_s "compile_date" full_date;
  pr_s "arch" arch;
  pr_b "arch_is_win32" arch_win32;
  pr_s "exec_extension" exe;
  pr_s "coqideincl" !lablgtkincludes;
  pr_s "has_coqide" coqide;
  pr "let gtk_platform = `%s\n" !idearchdef;
  pr_b "has_natdynlink" hasnatdynlink;
  pr_s "natdynlinkflag" natdynlinkflag;
  pr_i "vo_magic_number" vo_magic;
  pr_i "state_magic_number" state_magic;
  pr "let with_geoproof = ref %B\n" !Prefs.geoproof;
  pr_s "browser" browser;
  pr_s "wwwcoq" !Prefs.coqwebsite;
  pr_s "wwwbugtracker" (!Prefs.coqwebsite ^ "bugs/");
  pr_s "wwwrefman" (!Prefs.coqwebsite ^ "distrib/" ^ coq_version ^ "/refman/");
  pr_s "wwwstdlib" (!Prefs.coqwebsite ^ "distrib/" ^ coq_version ^ "/stdlib/");
  pr_s "localwwwrefman"  ("file:/" ^ docdir ^ "/html/refman");
  pr_b "no_native_compiler" (not !Prefs.nativecompiler);
  pr "\nlet plugins_dirs = [\n";
  let plugins = Sys.readdir "plugins" in
  Array.sort compare plugins;
  Array.iter
    (fun f ->
      let f' = "plugins/"^f in
      if Sys.is_directory f' && f.[0] <> '.' then pr "  %S;\n" f')
    plugins;
  pr "]\n";
  close_out o;
  Unix.chmod f 0o444

let _ = write_configml "config/coq_config.ml"

(** * Symlinks or copies for the checker *)

let _ =
  let prog, args, prf =
    if arch = "win32" then "cp", [], ""
    else "ln", ["-s"], "../" in
  List.iter (fun file ->
    ignore(run "rm" ["-f"; "checker/"^file]);
    ignore(run ~fatal:true prog (args @ [prf^"kernel/"^file;"checker/"^file])))
  [ "esubst.ml"; "esubst.mli"; "names.ml"; "names.mli" ]

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
  pr "LOCAL=%B\n\n" !Prefs.local;
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
  pr "CAMLFLAGS=-rectypes %s %s %s\n" coq_warn_flags coq_annotate_flag coq_safe_string;
  pr "# User compilation flag\n";
  pr "USERFLAGS=\n\n";
  pr "# Flags for GCC\n";
  pr "CFLAGS=%s\n\n" cflags;
  pr "# Compilation debug flags\n";
  pr "CAMLDEBUG=%s\n" coq_debug_flag;
  pr "CAMLDEBUGOPT=%s\n\n" coq_debug_flag_opt;
  pr "# Compilation profile flag\n";
  pr "CAMLTIMEPROF=%s\n\n" coq_profile_flag;
  pr "# Camlp4 : flavor, binaries, libraries ...\n";
  pr "# NB : avoid using CAMLP4LIB (conflict under Windows)\n";
  pr "CAMLP4=%s\n" camlpX;
  pr "CAMLP4O=%s\n" (win_aware_quote_executable camlpXo);
  pr "CAMLP4COMPAT=%s\n" camlp4compat;
  pr "MYCAMLP4LIB=%S\n\n" camlpXlibdir;
  pr "# Your architecture\n";
  pr "# Can be obtain by UNIX command arch\n";
  pr "ARCH=%s\n" arch;
  pr "HASNATDYNLINK=%s\n\n" natdynlinkflag;
  pr "# Supplementary libs for some systems, currently:\n";
  pr "#  . Sun Solaris: -cclib -lunix -cclib -lnsl -cclib -lsocket\n";
  pr "#  . others     : -cclib -lunix\n";
  pr "OSDEPLIBS=%s\n\n" osdeplibs;
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
  pr "#the command md5sum\n";
  pr "MD5SUM=%s\n\n" md5sum;
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
  pr "WITHDOC=%s\n\n" (if withdoc then "all" else "no");
  pr "# Option to produce precompiled files for native_compute\n";
  pr "NATIVECOMPUTE=%s\n" (if !Prefs.nativecompiler then "-native-compiler" else "");
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
