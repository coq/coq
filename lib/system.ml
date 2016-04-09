(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Errors
open Util

(* All subdirectories, recursively *)

let exists_dir dir =
  try Sys.is_directory dir with Sys_error _ -> false

let skipped_dirnames = ref ["CVS"; "_darcs"]

let exclude_search_in_dirname f = skipped_dirnames := f :: !skipped_dirnames

let ok_dirname f =
  not (String.is_empty f) && f.[0] != '.' &&
  not (String.List.mem f !skipped_dirnames) &&
  (match Unicode.ident_refutation f with None -> true | _ -> false)

let readdir dir = try Sys.readdir dir with any -> [||]

let all_subdirs ~unix_path:root =
  let l = ref [] in
  let add f rel = l := (f, rel) :: !l in
  let rec traverse dir rel =
    Array.iter (fun f ->
      if ok_dirname f then
	let file = Filename.concat dir f in
        if Sys.is_directory file then begin
          let newrel = rel @ [f] in
	  add file newrel;
	  traverse file newrel
        end)
      (readdir dir)
  in
  if exists_dir root then traverse root [];
  List.rev !l

(* Caching directory contents for efficient syntactic equality of file
   names even on case-preserving but case-insensitive file systems *)

module StrMod = struct
  type t = string
  let compare = compare
end

module StrMap = Map.Make(StrMod)
module StrSet = Set.Make(StrMod)

let dirmap = ref StrMap.empty

let make_dir_table dir =
  let filter_dotfiles s f = if f.[0] = '.' then s else StrSet.add f s in
  Array.fold_left filter_dotfiles StrSet.empty (readdir dir)

let exists_in_dir_respecting_case dir bf =
  let contents, cached =
    try StrMap.find dir !dirmap, true with Not_found ->
    let contents = make_dir_table dir in
    dirmap := StrMap.add dir contents !dirmap;
    contents, false in
  StrSet.mem bf contents ||
    if cached then begin
      (* rescan, there is a new file we don't know about *)
      let contents = make_dir_table dir in
      dirmap := StrMap.add dir contents !dirmap;
      StrSet.mem bf contents
    end
    else
      false

let file_exists_respecting_case path f =
  (* This function ensures that a file with expected lowercase/uppercase
     is the correct one, even on case-insensitive file systems *)
  let rec aux f =
    let bf = Filename.basename f in
    let df = Filename.dirname f in
    (String.equal df "." || aux df)
    && exists_in_dir_respecting_case (Filename.concat path df) bf
  in Sys.file_exists (Filename.concat path f) && aux f

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
    if file_exists_respecting_case lpe filename then [lpe,f] else []))

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
    (* the name is considered to be a physical name and we use the file
       system rules (e.g. possible case-insensitivity) to find it *)
    if Sys.file_exists filename then
      let root = Filename.dirname filename in
      root, filename
    else
      errorlabstrm "System.find_file_in_path"
	(hov 0 (str "Can't find file" ++ spc () ++ str filename))
  else
    (* the name is considered to be the transcription as a relative
       physical name of a logical name, so we deal with it as a name
       to be locate respecting case *)
    try where_in_path ~warn paths filename
    with Not_found ->
      errorlabstrm "System.find_file_in_path"
	(hov 0 (str "Can't find file" ++ spc () ++ str filename ++ spc () ++
		str "on loadpath"))

let is_in_path lpath filename =
  try ignore (where_in_path ~warn:false lpath filename); true
  with Not_found -> false

let is_in_system_path filename =
  try
    let lpath = CUnix.path_to_list (Sys.getenv "PATH") in
    is_in_path lpath filename
  with Not_found ->
    msg_warning (str "system variable PATH not found");
    false

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

type magic_number_error = {filename: string; actual: int; expected: int}
exception Bad_magic_number of magic_number_error

let raw_extern_state magic filename =
  let channel = open_trapping_failure filename in
  output_binary_int channel magic;
  channel

let raw_intern_state magic filename =
  try
    let channel = open_in_bin filename in
    let actual_magic = input_binary_int filename channel in
    if not (Int.equal actual_magic magic) then
        raise (Bad_magic_number {
            filename=filename;
            actual=actual_magic;
            expected=magic});
    channel
  with
  | End_of_file -> error_corrupted filename "premature end of file"
  | Failure s | Sys_error s -> error_corrupted filename s

let extern_state magic filename val_0 =
  try
    let channel = raw_extern_state magic filename in
    try
      marshal_out channel val_0;
      close_out channel
    with reraise ->
      let reraise = Errors.push reraise in
      let () = try_remove filename in
      iraise reraise
  with Sys_error s ->
    errorlabstrm "System.extern_state" (str "System error: " ++ str s)

let intern_state magic filename =
  try
    let channel = raw_intern_state magic filename in
    let v = marshal_in filename channel in
    close_in channel;
    v
  with Sys_error s ->
    errorlabstrm "System.intern_state" (str "System error: " ++ str s)

let with_magic_number_check f a =
  try f a
  with Bad_magic_number {filename=fname;actual=actual;expected=expected} ->
    errorlabstrm "with_magic_number_check"
    (str"File " ++ str fname ++ strbrk" has bad magic number " ++
    int actual ++ str" (expected " ++ int expected ++ str")." ++
    spc () ++
    strbrk "It is corrupted or was compiled with another version of Coq.")

(* Time stamps. *)

type time = float * float * float

let get_time () =
  let t = Unix.times ()  in
  (Unix.gettimeofday(), t.Unix.tms_utime, t.Unix.tms_stime)

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
    
