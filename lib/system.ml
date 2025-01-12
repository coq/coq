(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* $Id$ *)

open Pp

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

(* Note: this test is possibly used for Rocq module/file names but also for
   OCaml filenames, whose syntax as of today is more restrictive for
   module names (only initial letter then letter, digits, _ or quote),
   but more permissive (though disadvised) for file names  *)

let ok_dirname f =
  not (f = "") && f.[0] != '.' &&
  not (List.mem f !skipped_dirnames) &&
  match Unicode.ident_refutation f with None -> true | _ -> false

(* Check directory can be opened *)

let exists_dir dir =
  (* See BZ#5391 on windows failing on a trailing (back)slash *)
  let rec strip_trailing_slash dir =
    let len = String.length dir in
    if len > 0 && (dir.[len-1] = '/' || dir.[len-1] = '\\')
    then strip_trailing_slash (String.sub dir 0 (len-1)) else dir in
  let dir = if Sys.os_type = "Win32" then strip_trailing_slash dir else dir in
  try Sys.is_directory dir with Sys_error _ -> false

let rec mkdir dir =
  if not (exists_dir dir) then
    begin
      mkdir (Filename.dirname dir);
      Unix.mkdir dir 0o755;
    end

let apply_subdir f path name =
  (* we avoid all files and subdirs starting by '.' (e.g. .svn) *)
  (* as well as skipped files like CVS, ... *)
  let base = try Filename.chop_extension name with Invalid_argument _ -> name in
  if ok_dirname base then
    let path = if path = "." then name else path//name in
    match try (Unix.stat path).Unix.st_kind with Unix.Unix_error _ -> Unix.S_BLK with
    | Unix.S_DIR when name = base -> f (FileDir (path,name))
    | Unix.S_REG -> f (FileRegular name)
    | _ -> ()

let readdir dir = try Sys.readdir dir with Sys_error _ -> [||]

let process_directory f path =
  Array.iter (apply_subdir f path) (readdir path)

let process_subdirectories f path =
  let f = function FileDir (path,base) -> f path base | FileRegular _ -> () in
  process_directory f path

(** Returns the list of all recursive subdirectories of [root] in
    depth-first search, with sons ordered as on the file system;
    warns if [root] does not exist *)

let warn_cannot_open_dir =
  CWarnings.create ~name:"cannot-open-dir" ~category:CWarnings.CoreCategories.filesystem
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
  CWarnings.create ~name:"ambiguous-file-name" ~category:CWarnings.CoreCategories.filesystem
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
  CWarnings.create ~name:"PATH-not-found"
  (fun () -> str "Environment variable PATH not set")

let is_in_system_path filename =
  try
    let lpath = CUnix.path_to_list (Sys.getenv "PATH") in
    is_in_path lpath filename
  with Not_found ->
    warn_path_not_found ();
    false

let warn_using_current_directory =
  CWarnings.create ~name:"default-output-directory" ~category:CWarnings.CoreCategories.filesystem
    Pp.(fun s ->
           strbrk "Output directory is unset, using \"" ++ str s ++ str "\"." ++ spc () ++
           strbrk "Use command line option \"-output-directory to set a default directory.")

let get_output_path filename =
  if not (Filename.is_relative filename) then filename
  else match !Flags.output_directory with
  | None ->
    let pwd = Sys.getcwd () in
    warn_using_current_directory pwd;
    Filename.concat pwd filename
  | Some dir -> Filename.concat dir filename

let error_corrupted file s =
  CErrors.user_err (str file ++ str ": " ++ str s ++ str ". Try to rebuild it.")

let check_caml_version ~caml:s ~file:f =
  if not (String.equal Coq_config.caml_version s) then
    CErrors.user_err (str ("The file " ^ f ^ " was compiled with OCaml") ++
    spc () ++ str s ++ spc () ++ str "while this instance of Rocq was compiled \
    with OCaml" ++ spc() ++ str Coq_config.caml_version ++ str "." ++ spc () ++
    str "Rocq object files need to be compiled with the same OCaml toolchain to \
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

let with_magic_number_check ?loc f a =
  try f a
  with
  | Bad_magic_number {filename=fname; actual; expected} ->
    CErrors.user_err ?loc
    (str"File " ++ str fname ++ strbrk" has bad magic number " ++
    (str @@ Int32.to_string actual) ++ str" (expected " ++ (str @@ Int32.to_string expected) ++ str")." ++
    spc () ++
    strbrk "It is corrupted or was compiled with another version of Rocq.")
  | Bad_version_number {filename=fname;actual=actual;expected=expected} ->
    CErrors.user_err ?loc
    (str"File " ++ str fname ++ strbrk" has bad version number " ++
    (str @@ Int32.to_string actual) ++ str" (expected " ++ (str @@ Int32.to_string expected) ++ str")." ++
    spc () ++
    strbrk "It is corrupted or was compiled with another version of Rocq.")

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

type time = {real: float; user: float; system: float; }
type duration = time

let empty_duration = { real = 0.; user = 0.; system = 0. }

let get_time () =
  let t = Unix.times ()  in
  { real = Unix.gettimeofday();
    user = t.Unix.tms_utime;
    system = t.Unix.tms_stime;
  }

(* Keep only 3 significant digits *)
let round f = (floor (f *. 1e3)) *. 1e-3

let duration_between ~start ~stop = {
  real = stop.real -. start.real;
  user = stop.user -. start.user;
  system = stop.system -. start.system;
}

let duration_add t1 t2 = {
  real = t1.real +. t2.real;
  user = t1.user +. t2.user;
  system = t1.system +. t2.system;
}

let diff1 proj ~start ~stop = round (proj stop -. proj start)

let time_difference t1 t2 = diff1 (fun t -> t.real) ~start:t1 ~stop:t2

let duration_real { real; _ } = real

let fmt_duration { real = treal; user; system } =
  real (round treal) ++ str " secs " ++
  str "(" ++
  real (round user) ++ str "u" ++
  str "," ++
  real (round system) ++ str "s" ++
  str ")"

let fmt_time_difference start stop =
  fmt_duration (duration_between ~start ~stop)

type 'a transaction_result = (('a * duration), (Exninfo.iexn * duration)) Result.t

let measure_duration f x =
  let start = get_time() in
  try
    let y = f x in
    let stop = get_time() in
    Ok (y, duration_between ~start ~stop)
  with e ->
    let stop = get_time() in
    let exn = Exninfo.capture e in
    Error (exn, duration_between ~start ~stop)

let fmt_transaction_result x =
  let msg, msg2, duration = match x with
  | Ok(_, duration) ->
    "Finished transaction in ", " (successful)", duration
  | Error(_,duration) ->
    "Finished failing transaction in ", " (failure)", duration
  in
  str msg ++ fmt_duration duration ++ str msg2

type instruction_count = (Int64.t, string) Result.t

let instruction_count_add c1 c2 =
  match (c1, c2) with
  | (Ok i1, Ok i2) -> Ok (Int64.add i1 i2)
  | (Error _, _) -> c1
  | (_, Error _) -> c2

type 'a instructions_result =
  (('a * instruction_count), (Exninfo.iexn * instruction_count)) Result.t

let instructions_between ~c_start ~c_end =
  match (c_start, c_end) with
  | (Error _, _) -> c_start
  | (_, Error _) -> c_end
  | (Ok c0, Ok c1) -> Ok (Int64.sub c1 c0)

let count_instructions f x =
  let c_start = Instr.read_counter () in
  try
    let y = f x in
    let c_end = Instr.read_counter () in
    Ok(y, instructions_between ~c_start ~c_end)
  with e ->
    let exn = Exninfo.capture e in
    let c_end = Instr.read_counter () in
    Error(exn, instructions_between ~c_start ~c_end)

let fmt_instructions_result r =
  let (failing, count, status) =
    match r with
    | Ok(_, count) -> ("", count, " (successful)")
    | Error(_, count) -> ("failing ", count, " (failure)"   )
  in
  match count with
  | Ok i ->
      str "Finished " ++ str failing ++ str "transaction in " ++ int64 i ++
      str " instructions" ++ str status
  | Error m ->
      str "Finished " ++ str failing ++
      str "transaction with instruction count error \"" ++
      str m ++ str "\"" ++ str status

(* We use argv.[0] as we don't want to resolve symlinks *)
let get_toplevel_path top =
  let open Filename in
  let dir = if String.equal (basename Sys.argv.(0)) Sys.argv.(0)
            then "" else dirname Sys.argv.(0) ^ dir_sep in
  let exe = if Sys.(os_type = "Win32" || os_type = "Cygwin") then ".exe" else "" in
  dir ^ top ^ exe
