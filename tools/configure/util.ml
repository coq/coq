(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Printf

let debug = ref false

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

let read_lines_and_close cin =
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

let read_lines_and_close_fd fd =
  read_lines_and_close (Unix.in_channel_of_descr fd)

(** Run some unix command and read the first line of its output.
    We avoid Unix.open_process and its non-fully-portable /bin/sh,
    especially when it comes to quoting the filenames.
    Error messages:
     - if err=StdErr, any error message goes in the stderr of our script.
     - if err=StdOut, we merge stderr and stdout (just as 2>&1).
     - if err=DevNull, we drop the error messages (same as 2>/dev/null). *)

type err = StdErr | StdOut | DevNull

let exe = ref ""  (* Will be set later on, when the call to uname is done *)

let run ?(fatal=true) ?(verbose=false) ?(err=StdErr) prog args =
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
    let line, all = read_lines_and_close_fd out_r in
    let _ = read_lines_and_close_fd nul_r in
    let () = check_exit_code (waitpid_non_intr pid) in
    line, all
  with
  | _ when not fatal && not verbose -> "", []
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
  match string_split '.' (String.sub s 0 !i) with
  | [v] -> [v;"0";"0"]
  | [v1;v2] -> [v1;v2;"0"]
  | [v1;v2;""] -> [v1;v2;"0"] (* e.g. because it ends with ".beta" *)
  | v -> v

let generic_version_nums ~name version_string =
  let version_list = numeric_prefix_list version_string in
  if !debug then
    begin
      let pp_sep = Format.pp_print_space in
      Format.(eprintf "Parsing version info for %s: @[raw: %s / split: %a@]@\n%!"
                name version_string (pp_print_list ~pp_sep pp_print_string) version_list)
    end;
  try List.map int_of_string version_list
  with _ ->
    "I found " ^ name ^ " but cannot read its version number!\n" ^
    "Is it installed properly?" |> die

(** Combined existence and directory tests *)

let dir_exists f = Sys.file_exists f && Sys.is_directory f

(** Does a file exist and is executable ? *)

let is_executable f =
  try let () = Unix.access f [Unix.X_OK] in true
  with Unix.Unix_error _ -> false

(** Equivalent of rm -f *)

let safe_remove f =
  try Unix.chmod f 0o644; Sys.remove f with Unix.Unix_error _ | Sys_error _ -> ()

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

let arch = function
  | Some a -> a
  | None ->
    let arch,_ = tryrun "uname" ["-s"] in
    if starts_with arch "CYGWIN" then "win32"
    else if starts_with arch "MINGW32" then "win32"
    else if arch <> "" then arch
    else try_archs arch_progs

let write_config_file ~file ?(bin=false) action =
  safe_remove file;
  let o = if bin then open_out_bin file else open_out file in
  try
    action o;
    close_out o;
    Unix.chmod file 0o444
  with exn ->
    close_out o;
    safe_remove file;
    raise exn
