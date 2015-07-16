(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Errors
open Util
open Unix

(** Dealing with directories *)

type unix_path = string (* path in unix-style, with '/' separator *)

type file_kind =
  | FileDir of unix_path * (* basename of path: *) string
  | FileRegular of string (* basename of file *)

(* Copy of Filename.concat but assuming paths to always be POSIX *)

let (//) dirname filename =
  let l = String.length dirname in
  if l = 0 || dirname.[l-1] = '/'
  then dirname ^ filename
  else dirname ^ "/" ^ filename

(* Excluding directories; We avoid directories starting with . as well
   as CVS and _darcs and any subdirs given via -exclude-dir *)

let skipped_dirnames = ref ["CVS"; "_darcs"]

let exclude_directory f = skipped_dirnames := f :: !skipped_dirnames

let ok_dirname f =
  not (f = "") && f.[0] != '.' &&
  not (List.mem f !skipped_dirnames) (*&&
  (match Unicode.ident_refutation f with None -> true | _ -> false)*)

(* Check directory can be opened *)

let exists_dir dir =
  try let _ = closedir (opendir dir) in true with Unix_error _ -> false

let check_unix_dir warn dir =
  if (Sys.os_type = "Win32" || Sys.os_type = "Cygwin") &&
    (String.length dir > 2 && dir.[1] = ':' ||
     String.contains dir '\\' ||
     String.contains dir ';')
  then warn ("assuming " ^ dir ^
             " to be a Unix path even if looking like a Win32 path.")

let apply_subdir f path name =
  (* we avoid all files and subdirs starting by '.' (e.g. .svn) *)
  (* as well as skipped files like CVS, ... *)
  if name.[0] <> '.' && ok_dirname name then
    let path = if path = "." then name else path//name in
    match try (stat path).st_kind with Unix_error _ -> S_BLK with
    | S_DIR -> f (FileDir (path,name))
    | S_REG -> f (FileRegular name)
    | _ -> ()

let process_directory f path =
  let dirh = opendir path in
  try while true do apply_subdir f path (readdir dirh) done
  with End_of_file -> closedir dirh

let process_subdirectories f path =
  let f = function FileDir (path,base) -> f path base | FileRegular _ -> () in
  process_directory f path

(** Returns the list of all recursive subdirectories of [root] in
    depth-first search, with sons ordered as on the file system;
    warns if [root] does not exist *)

let all_subdirs ~unix_path:root =
  let l = ref [] in
  let add f rel = l := (f, rel) :: !l in
  let rec traverse path rel =
    let f = function
      | FileDir (path,f) ->
	  let newrel = rel @ [f] in
	  add path newrel;
	  traverse path newrel
      | _ -> ()
    in process_directory f path
  in
  check_unix_dir (fun s -> msg_warning (str s)) root;
  if exists_dir root then traverse root []
  else msg_warning (str ("Cannot open " ^ root));
  List.rev !l

let file_exists_respecting_case f =
  if Coq_config.arch = "Darwin" then
    (* ensure that the file exists with expected case on the
       case-insensitive but case-preserving default MacOS file system *)
    let rec aux f =
      let bf = Filename.basename f in
      let df = Filename.dirname f in
      (String.equal df "." || String.equal df "/" || aux df)
      && Array.exists (String.equal bf) (Sys.readdir df)
    in aux f
  else Sys.file_exists f

let rec search paths test =
  match paths with
  | [] -> []
  | lpe :: rem -> test lpe @ search rem test

let where_in_path ?(warn=true) path filename =
  let check_and_warn l = match l with
  | [] -> raise Not_found
  | (lpe, f) :: l' ->
    let () = match l' with
    | _ :: _ when warn ->
      msg_warning
        (str filename ++ str " has been found in" ++ spc () ++
          hov 0 (str "[ " ++
            hv 0 (prlist_with_sep (fun () -> str " " ++ pr_semicolon())
              (fun (lpe,_) -> str lpe) l)
            ++ str " ];") ++ fnl () ++
          str "loading " ++ str f)
    | _ -> ()
    in
    (lpe, f)
  in
  check_and_warn (search path (fun lpe ->
    let f = Filename.concat lpe filename in
    if file_exists_respecting_case f then [lpe,f] else []))

let where_in_path_rex path rex =
  search path (fun lpe ->
    try
      let files = Sys.readdir lpe in
      CList.map_filter (fun name ->
        try
          ignore(Str.search_forward rex name 0);
          Some (lpe,Filename.concat lpe name)
        with Not_found -> None)
      (Array.to_list files)
    with Sys_error _ -> [])

let find_file_in_path ?(warn=true) paths filename =
  if not (Filename.is_implicit filename) then
    if file_exists_respecting_case filename then
      let root = Filename.dirname filename in
      root, filename
    else
      errorlabstrm "System.find_file_in_path"
	(hov 0 (str "Can't find file" ++ spc () ++ str filename))
  else
    try where_in_path ~warn paths filename
    with Not_found ->
      errorlabstrm "System.find_file_in_path"
	(hov 0 (str "Can't find file" ++ spc () ++ str filename ++ spc () ++
		str "on loadpath"))

let is_in_path lpath filename =
  try ignore (where_in_path ~warn:false lpath filename); true
  with Not_found -> false

let is_in_system_path filename =
  let path = try Sys.getenv "PATH"
             with Not_found -> error "system variable PATH not found" in
  let lpath = CUnix.path_to_list path in
  is_in_path lpath filename

let open_trapping_failure name =
  try open_out_bin name
  with e when Errors.noncritical e ->
    errorlabstrm "System.open" (str "Can't open " ++ str name)

let try_remove filename =
  try Sys.remove filename
  with e when Errors.noncritical e ->
    msg_warning
      (str"Could not remove file " ++ str filename ++ str" which is corrupted!")

let error_corrupted file s =
  errorlabstrm "System" (str file ++ str ": " ++ str s ++ str ". Try to rebuild it.")

let input_binary_int f ch =
  try input_binary_int ch
  with
  | End_of_file -> error_corrupted f "premature end of file"
  | Failure s -> error_corrupted f s
let output_binary_int ch x = output_binary_int ch x; flush ch

let marshal_out ch v = Marshal.to_channel ch v []; flush ch
let marshal_in filename ch =
  try Marshal.from_channel ch
  with
  | End_of_file -> error_corrupted filename "premature end of file"
  | Failure s -> error_corrupted filename s

let digest_out = Digest.output
let digest_in filename ch =
  try Digest.input ch
  with
  | End_of_file -> error_corrupted filename "premature end of file"
  | Failure s -> error_corrupted filename s

let marshal_out_segment f ch v =
  let start = pos_out ch in
  output_binary_int ch 0;  (* dummy value for stop *)
  marshal_out ch v;
  let stop = pos_out ch in
  seek_out ch start;
  output_binary_int ch stop;
  seek_out ch stop;
  digest_out ch (Digest.file f)

let marshal_in_segment f ch =
  let stop = (input_binary_int f ch : int) in
  let v = marshal_in f ch in
  let digest = digest_in f ch in
  v, stop, digest

let skip_in_segment f ch =
  let stop = (input_binary_int f ch : int) in
  seek_in ch stop;
  stop, digest_in f ch

exception Bad_magic_number of string

let raw_extern_intern magic =
  let extern_state filename =
    let channel = open_trapping_failure filename in
    output_binary_int channel magic;
    filename, channel
  and intern_state filename =
    try
      let channel = open_in_bin filename in
      if not (Int.equal (input_binary_int filename channel) magic) then
        raise (Bad_magic_number filename);
      channel
    with
    | End_of_file -> error_corrupted filename "premature end of file"
    | Failure s | Sys_error s -> error_corrupted filename s
  in
  (extern_state,intern_state)

let extern_intern ?(warn=true) magic =
  let (raw_extern,raw_intern) = raw_extern_intern magic in
  let extern_state name val_0 =
    try
      let (filename,channel) = raw_extern name in
      try
        marshal_out channel val_0;
        close_out channel
      with reraise ->
	let reraise = Errors.push reraise in
        let () = try_remove filename in
        iraise reraise
    with Sys_error s ->
      errorlabstrm "System.extern_state" (str "System error: " ++ str s)
  and intern_state paths name =
    try
      let _,filename = find_file_in_path ~warn paths name in
      let channel = raw_intern filename in
      let v = marshal_in filename channel in
      close_in channel;
      v
    with Sys_error s ->
      errorlabstrm "System.intern_state" (str "System error: " ++ str s)
  in
  (extern_state,intern_state)

let with_magic_number_check f a =
  try f a
  with Bad_magic_number fname ->
    errorlabstrm "with_magic_number_check"
    (str"File " ++ str fname ++ strbrk" has bad magic number." ++ spc () ++
    strbrk "It is corrupted or was compiled with another version of Coq.")

(* Time stamps. *)

type time = float * float * float

let get_time () =
  let t = Unix.times ()  in
  (Unix.gettimeofday(), t.tms_utime, t.tms_stime)

(* Keep only 3 significant digits *)
let round f = (floor (f *. 1e3)) *. 1e-3

let time_difference (t1,_,_) (t2,_,_) = round (t2 -. t1)

let fmt_time_difference (startreal,ustart,sstart) (stopreal,ustop,sstop) =
  real (round (stopreal -. startreal)) ++ str " secs " ++
  str "(" ++
  real (round (ustop -. ustart)) ++ str "u" ++
  str "," ++
  real (round (sstop -. sstart)) ++ str "s" ++
  str ")"

let with_time time f x =
  let tstart = get_time() in
  let msg = if time then "" else "Finished transaction in " in
  try
    let y = f x in
    let tend = get_time() in
    let msg2 = if time then "" else " (successful)" in
    msg_info (str msg ++ fmt_time_difference tstart tend ++ str msg2);
    y
  with e ->
    let tend = get_time() in
    let msg = if time then "" else "Finished failing transaction in " in
    let msg2 = if time then "" else " (failure)" in
    msg_info (str msg ++ fmt_time_difference tstart tend ++ str msg2);
    raise e

let process_id () =
  if Flags.async_proofs_is_worker () then !Flags.async_proofs_worker_id
  else Printf.sprintf "master:%d" (Thread.id (Thread.self ()))
    
