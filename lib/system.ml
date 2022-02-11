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

let all_in_path path filename =
  search path (fun (physicaldir,logicaldir) ->
      let f = Filename.concat physicaldir filename in
      if file_exists_respecting_case physicaldir filename then [logicaldir,f] else [])

let find_file_in_path ?(warn=true) paths filename =
  if not (Filename.is_implicit filename) then
    (* the name is considered to be a physical name and we use the file
       system rules (e.g. possible case-insensitivity) to find it *)
    if Sys.file_exists filename then
      let root = Filename.dirname filename in
      root, filename
    else
      CErrors.user_err
        (hov 0 (str "Can't find file" ++ spc () ++ str filename ++ str "."))
  else
    (* the name is considered to be the transcription as a relative
       physical name of a logical name, so we deal with it as a name
       to be locate respecting case *)
    try where_in_path ~warn paths filename
    with Not_found ->
      CErrors.user_err
        (hov 0 (str "Can't find file" ++ spc () ++ str filename ++ spc () ++
                str "on loadpath."))

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

let error_corrupted file s =
  CErrors.user_err (str file ++ str ": " ++ str s ++ str ". Try to rebuild it.")

let check_caml_version ~caml:s ~file:f =
  if not (String.equal Coq_config.caml_version s) then
    CErrors.user_err (str ("The file " ^ f ^ " was compiled with OCaml") ++
    spc () ++ str s ++ spc () ++ str "while this instance of Coq was compiled \
    with OCaml" ++ spc() ++ str Coq_config.caml_version ++ str "." ++ spc () ++
    str "Coq object files need to be compiled with the same OCaml toolchain to \
    be compatible.")
  else ()

let marshal_out ch v = Marshal.to_channel ch v []; flush ch
let marshal_in filename ch =
  try Marshal.from_channel ch
  with
  | End_of_file -> error_corrupted filename "premature end of file"
  | Failure s -> error_corrupted filename s

type magic_number_error = {filename: string; actual: int32; expected: int32}
exception Bad_magic_number of magic_number_error
exception Bad_version_number of magic_number_error

let with_magic_number_check f a =
  try f a
  with
  | Bad_magic_number {filename=fname; actual; expected} ->
    CErrors.user_err
    (str"File " ++ str fname ++ strbrk" has bad magic number " ++
    (str @@ Int32.to_string actual) ++ str" (expected " ++ (str @@ Int32.to_string expected) ++ str")." ++
    spc () ++
    strbrk "It is corrupted or was compiled with another version of Coq.")
  | Bad_version_number {filename=fname;actual=actual;expected=expected} ->
    CErrors.user_err
    (str"File " ++ str fname ++ strbrk" has bad version number " ++
    (str @@ Int32.to_string actual) ++ str" (expected " ++ (str @@ Int32.to_string expected) ++ str")." ++
    spc () ++
    strbrk "It is corrupted or was compiled with another version of Coq.")

(* input/ouptput of int32 and int64 *)

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
