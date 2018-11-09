(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util

include Minisys

(** Returns the list of all recursive subdirectories of [root] in
    depth-first search, with sons ordered as on the file system;
    warns if [root] does not exist *)

let warn_cannot_open_dir =
  CWarnings.create ~name:"cannot-open-dir" ~category:"filesystem"
  (fun dir -> str ("Cannot open directory " ^ dir))

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
  if exists_dir root then traverse root []
  else warn_cannot_open_dir root;
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
  Array.fold_left filter_dotfiles StrSet.empty (Sys.readdir dir)

(** Don't trust in interactive mode (the default) *)
let trust_file_cache = ref false

let exists_in_dir_respecting_case dir bf =
  let cache_dir dir =
    let contents = make_dir_table dir in
    dirmap := StrMap.add dir contents !dirmap;
    contents in
  let contents, fresh =
    try
      (* in batch mode, assume the directory content is still fresh *)
      StrMap.find dir !dirmap, !trust_file_cache
    with Not_found ->
      (* in batch mode, we are not yet sure the directory exists *)
      if !trust_file_cache && not (exists_dir dir) then StrSet.empty, true
      else cache_dir dir, true in
  StrSet.mem bf contents ||
    not fresh &&
      (* rescan, there is a new file we don't know about *)
      StrSet.mem bf (cache_dir dir)

let file_exists_respecting_case path f =
  (* This function ensures that a file with expected lowercase/uppercase
     is the correct one, even on case-insensitive file systems *)
  let rec aux f =
    let bf = Filename.basename f in
    let df = Filename.dirname f in
    (* When [df] is the same as [f], it means that the root of the file system
       has been reached. There is no point in looking further up. *)
    (String.equal df "." || String.equal f df || aux df)
    && exists_in_dir_respecting_case (Filename.concat path df) bf
  in (!trust_file_cache || Sys.file_exists (Filename.concat path f)) && aux f

let rec search paths test =
  match paths with
  | [] -> []
  | lpe :: rem -> test lpe @ search rem test

let warn_ambiguous_file_name =
  CWarnings.create ~name:"ambiguous-file-name" ~category:"filesystem"
    (fun (filename,l,f) -> str filename ++ str " has been found in" ++ spc () ++
                hov 0 (str "[ " ++
                         hv 0 (prlist_with_sep (fun () -> str " " ++ pr_semicolon())
                                               (fun (lpe,_) -> str lpe) l)
                       ++ str " ];") ++ fnl () ++
                str "loading " ++ str f)


let where_in_path ?(warn=true) path filename =
  let check_and_warn l = match l with
  | [] -> raise Not_found
  | (lpe, f) :: l' ->
    let () = match l' with
    | _ :: _ when warn -> warn_ambiguous_file_name (filename,l,f)
    | _ -> ()
    in
    (lpe, f)
  in
  check_and_warn (search path (fun lpe ->
    let f = Filename.concat lpe filename in
    if file_exists_respecting_case lpe filename then [lpe,f] else []))

let find_file_in_path ?(warn=true) paths filename =
  if not (Filename.is_implicit filename) then
    (* the name is considered to be a physical name and we use the file
       system rules (e.g. possible case-insensitivity) to find it *)
    if Sys.file_exists filename then
      let root = Filename.dirname filename in
      root, filename
    else
      CErrors.user_err ~hdr:"System.find_file_in_path"
	(hov 0 (str "Can't find file" ++ spc () ++ str filename))
  else
    (* the name is considered to be the transcription as a relative
       physical name of a logical name, so we deal with it as a name
       to be locate respecting case *)
    try where_in_path ~warn paths filename
    with Not_found ->
      CErrors.user_err ~hdr:"System.find_file_in_path"
	(hov 0 (str "Can't find file" ++ spc () ++ str filename ++ spc () ++
		str "on loadpath"))

let is_in_path lpath filename =
  try ignore (where_in_path ~warn:false lpath filename); true
  with Not_found -> false

let warn_path_not_found =
  CWarnings.create ~name:"path-not-found" ~category:"filesystem"
  (fun () -> str "system variable PATH not found")

let is_in_system_path filename =
  try
    let lpath = CUnix.path_to_list (Sys.getenv "PATH") in
    is_in_path lpath filename
  with Not_found ->
    warn_path_not_found ();
    false

let open_trapping_failure name =
  try open_out_bin name
  with e when CErrors.noncritical e ->
    CErrors.user_err ~hdr:"System.open" (str "Can't open " ++ str name)

let warn_cannot_remove_file =
  CWarnings.create ~name:"cannot-remove-file" ~category:"filesystem"
  (fun filename -> str"Could not remove file " ++ str filename ++ str" which is corrupted!")

let try_remove filename =
  try Sys.remove filename
  with e when CErrors.noncritical e ->
    warn_cannot_remove_file filename

let error_corrupted file s =
  CErrors.user_err ~hdr:"System" (str file ++ str ": " ++ str s ++ str ". Try to rebuild it.")

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
      let reraise = CErrors.push reraise in
      let () = try_remove filename in
      iraise reraise
  with Sys_error s ->
    CErrors.user_err ~hdr:"System.extern_state" (str "System error: " ++ str s)

let intern_state magic filename =
  try
    let channel = raw_intern_state magic filename in
    let v = marshal_in filename channel in
    close_in channel;
    v
  with Sys_error s ->
    CErrors.user_err ~hdr:"System.intern_state" (str "System error: " ++ str s)

let with_magic_number_check f a =
  try f a
  with Bad_magic_number {filename=fname;actual=actual;expected=expected} ->
    CErrors.user_err ~hdr:"with_magic_number_check"
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

let with_time ~batch f x =
  let tstart = get_time() in
  let msg = if batch then "" else "Finished transaction in " in
  try
    let y = f x in
    let tend = get_time() in
    let msg2 = if batch then "" else " (successful)" in
    Feedback.msg_info (str msg ++ fmt_time_difference tstart tend ++ str msg2);
    y
  with e ->
    let tend = get_time() in
    let msg = if batch then "" else "Finished failing transaction in " in
    let msg2 = if batch then "" else " (failure)" in
    Feedback.msg_info (str msg ++ fmt_time_difference tstart tend ++ str msg2);
    raise e

let get_toplevel_path top =
  let dir = Filename.dirname Sys.executable_name in
  let exe = if Sys.(os_type = "Win32" || os_type = "Cygwin") then ".exe" else "" in
  let eff = if Dynlink.is_native then ".opt" else ".byte" in
  dir ^ Filename.dir_sep ^ top ^ eff ^ exe
