(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* $Id$ *)

open Pp

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

let dirmap = ref CString.Map.empty

let make_dir_table dir =
  let entries =
    try
      Sys.readdir dir
    with Sys_error _ ->
      warn_cannot_open_dir dir;
      [||] in
  let filter_dotfiles s f = if f.[0] = '.' then s else CString.Set.add f s in
  Array.fold_left filter_dotfiles CString.Set.empty entries

(** Don't trust in interactive mode (the default) *)
let trust_file_cache = ref false

let exists_in_dir_respecting_case dir bf =
  let cache_dir dir =
    let contents = make_dir_table dir in
    dirmap := CString.Map.add dir contents !dirmap;
    contents in
  let contents, fresh =
    try
      (* in batch mode, assume the directory content is still fresh *)
      CString.Map.find dir !dirmap, !trust_file_cache
    with Not_found ->
      (* in batch mode, we are not yet sure the directory exists *)
      if !trust_file_cache && not (exists_dir dir) then CString.Set.empty, true
      else cache_dir dir, true in
  CString.Set.mem bf contents ||
    not fresh &&
      (* rescan, there is a new file we don't know about *)
      CString.Set.mem bf (cache_dir dir)

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

type magic_number_error = {filename: string; actual: int32; expected: int32}
exception Bad_magic_number of magic_number_error
exception Bad_version_number of magic_number_error

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
            actual=Int32.of_int actual_magic;
            expected=Int32.of_int magic});
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
      let reraise = Exninfo.capture reraise in
      let () = try_remove filename in
      Exninfo.iraise reraise
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
  with
  | Bad_magic_number {filename=fname; _} ->
    CErrors.user_err ~hdr:"with_magic_number_check"
    (str"File " ++ str fname ++ strbrk" is corrupted.")
  | Bad_version_number {filename=fname;actual=actual;expected=expected} ->
    CErrors.user_err ~hdr:"with_magic_number_check"
    (str"File " ++ str fname ++ strbrk" has bad version number " ++
    (str @@ Int32.to_string actual) ++ str" (expected " ++ (str @@ Int32.to_string expected) ++ str")." ++
    spc () ++
    strbrk "It is corrupted or was compiled with another version of Coq.")

module ObjFile =
struct

let magic_number = 0x436F7121l (* "Coq!" *)

(*

int32: big-endian, 4 bytes
int64: big-endian, 8 bytes

-- string --
int32 | length of the next field
data  |

-- segment summary --
string | name
int64  | absolute position
int64  | length (without hash)
hash   | MD5 (16 bytes)

-- segment --
...  | binary data
hash | MD5 (16 bytes)

-- summary --
int32 | number of segment summaries
s1    |
...   | segment summaries
sn    |

-- vo --
int32   | magic number
int32   | Coq version
int64   | absolute position of the summary
...     | segments
summary |

*)

type segment = {
  name : string;
  pos : int64;
  len : int64;
  hash : Digest.t;
}

type in_handle = {
  in_filename : string;
  in_channel : in_channel;
  in_segments : segment CString.Map.t;
}

type out_handle = {
  out_filename : string;
  out_channel : out_channel;
  mutable out_segments : segment CString.Map.t;
}

let input_int32 ch =
  let accu = ref 0l in
  for _i = 0 to 3 do
    let c = input_byte ch in
    accu := Int32.add (Int32.shift_left !accu 8) (Int32.of_int c)
  done;
  !accu

let input_int64 ch =
  let accu = ref 0L in
  for _i = 0 to 7 do
    let c = input_byte ch in
    accu := Int64.add (Int64.shift_left !accu 8) (Int64.of_int c)
  done;
  !accu

let output_int32 ch n =
  for i = 0 to 3 do
    output_byte ch (Int32.to_int (Int32.shift_right_logical n (24 - 8 * i)))
  done

let output_int64 ch n =
  for i = 0 to 7 do
    output_byte ch (Int64.to_int (Int64.shift_right_logical n (56 - 8 * i)))
  done

let input_segment_summary ch =
  let nlen = input_int32 ch in
  let name = really_input_string ch (Int32.to_int nlen) in
  let pos = input_int64 ch in
  let len = input_int64 ch in
  let hash = Digest.input ch in
  { name; pos; len; hash }

let output_segment_summary ch seg =
  let nlen = Int32.of_int (String.length seg.name) in
  let () = output_int32 ch nlen in
  let () = output_string ch seg.name in
  let () = output_int64 ch seg.pos in
  let () = output_int64 ch seg.len in
  let () = Digest.output ch seg.hash in
  ()

let rec input_segment_summaries ch n accu =
  if Int32.equal n 0l then accu
  else
    let s = input_segment_summary ch in
    let accu = CString.Map.add s.name s accu in
    input_segment_summaries ch (Int32.pred n) accu

let marshal_in_segment (type a) h ~segment : a * Digest.t =
  let { in_channel = ch } = h in
  let s = CString.Map.find segment h.in_segments in
  let () = LargeFile.seek_in ch s.pos in
  let (v : a) = marshal_in h.in_filename ch in
  let () = assert (Int64.equal (LargeFile.pos_in ch) (Int64.add s.pos s.len)) in
  let h = Digest.input ch in
  let () = assert (String.equal h s.hash) in
  (v, s.hash)

let marshal_out_segment h ~segment v =
  let { out_channel = ch } = h in
  let () = assert (not (CString.Map.mem segment h.out_segments)) in
  let pos = LargeFile.pos_out ch in
  let () = Marshal.to_channel ch v [] in
  let () = flush ch in
  let pos' = LargeFile.pos_out ch in
  let len = Int64.sub pos' pos in
  let hash =
    let in_ch = open_in h.out_filename in
    let () = LargeFile.seek_in in_ch pos in
    let digest = Digest.channel in_ch (Int64.to_int len) in
    let () = close_in in_ch in
    digest
  in
  let () = Digest.output ch hash in
  let s = { name = segment; pos; len; hash } in
  let () = h.out_segments <- CString.Map.add segment s h.out_segments in
  ()

let marshal_out_binary h ~segment =
  let { out_channel = ch } = h in
  let () = assert (not (CString.Map.mem segment h.out_segments)) in
  let pos = LargeFile.pos_out ch in
  let finish () =
    let () = flush ch in
    let pos' = LargeFile.pos_out ch in
    let len = Int64.sub pos' pos in
    let hash =
      let in_ch = open_in h.out_filename in
      let () = LargeFile.seek_in in_ch pos in
      let digest = Digest.channel in_ch (Int64.to_int len) in
      let () = close_in in_ch in
      digest
    in
    let () = Digest.output ch hash in
    let s = { name = segment; pos; len; hash } in
    h.out_segments <- CString.Map.add segment s h.out_segments
  in
  ch, finish

let open_in ~file =
  try
    let ch = open_in_bin file in
    let magic = input_int32 ch in
    let version = input_int32 ch in
    let () =
      if not (Int32.equal magic magic_number) then
        let e = { filename = file; actual = version; expected = magic_number } in
        raise (Bad_magic_number e)
    in
    let () =
      let expected = Coq_config.vo_version in
      if not (Int32.equal version expected) then
        let e = { filename = file; actual = version; expected } in
        raise (Bad_version_number e)
    in
    let summary_pos = input_int64 ch in
    let () = LargeFile.seek_in ch summary_pos in
    let nsum = input_int32 ch in
    let seg = input_segment_summaries ch nsum CString.Map.empty in
    { in_filename = file; in_channel = ch; in_segments = seg }
  with
  | End_of_file -> error_corrupted file "premature end of file"
  | Failure s | Sys_error s -> error_corrupted file s

let close_in ch =
  close_in ch.in_channel

let get_segment ch ~segment =
  CString.Map.find segment ch.in_segments

let segments ch = ch.in_segments

let open_out ~file =
  let ch = open_trapping_failure file in
  let () = output_int32 ch magic_number in
  let () = output_int32 ch Coq_config.vo_version in
  let () = output_int64 ch 0L (* placeholder *) in
  { out_channel = ch; out_segments = CString.Map.empty; out_filename = file }

let close_out { out_channel = ch; out_segments = seg } =
  let () = flush ch in
  let pos = LargeFile.pos_out ch in
  (* Write the segment summary *)
  let () = output_int32 ch (Int32.of_int (CString.Map.cardinal seg)) in
  let iter _ s = output_segment_summary ch s in
  let () = CString.Map.iter iter seg in
  (* Overwrite the position place holder *)
  let () = LargeFile.seek_out ch 8L in
  let () = output_int64 ch pos in
  let () = flush ch in
  close_out ch

end

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

let with_time ~batch ~header f x =
  let tstart = get_time() in
  let msg = if batch then "" else "Finished transaction in " in
  try
    let y = f x in
    let tend = get_time() in
    let msg2 = if batch then "" else " (successful)" in
    Feedback.msg_notice (header ++ str msg ++ fmt_time_difference tstart tend ++ str msg2);
    y
  with e ->
    let tend = get_time() in
    let msg = if batch then "" else "Finished failing transaction in " in
    let msg2 = if batch then "" else " (failure)" in
    Feedback.msg_notice (header ++ str msg ++ fmt_time_difference tstart tend ++ str msg2);
    raise e

(* We use argv.[0] as we don't want to resolve symlinks *)
let get_toplevel_path ?(byte=Sys.(backend_type = Bytecode)) top =
  let open Filename in
  let dir = if String.equal (basename Sys.argv.(0)) Sys.argv.(0)
            then "" else dirname Sys.argv.(0) ^ dir_sep in
  let exe = if Sys.(os_type = "Win32" || os_type = "Cygwin") then ".exe" else "" in
  let eff = if byte then ".byte" else ".opt" in
  dir ^ top ^ eff ^ exe
