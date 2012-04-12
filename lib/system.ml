(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Errors
open Util
open Unix

(* All subdirectories, recursively *)

let exists_dir dir =
  try let _ = closedir (opendir dir) in true with Unix_error _ -> false

let skipped_dirnames = ref ["CVS"; "_darcs"]

let exclude_search_in_dirname f = skipped_dirnames := f :: !skipped_dirnames

let ok_dirname f =
  f <> "" && f.[0] <> '.' && not (List.mem f !skipped_dirnames) &&
  match ident_refutation f with |None -> true |_ -> false

let all_subdirs ~unix_path:root =
  let l = ref [] in
  let add f rel = l := (f, rel) :: !l in
  let rec traverse dir rel =
    let dirh = opendir dir in
    try
      while true do
	let f = readdir dirh in
	if ok_dirname f then
	  let file = Filename.concat dir f in
	  try
	    if (stat file).st_kind = S_DIR then begin
	      let newrel = rel@[f] in
	      add file newrel;
	      traverse file newrel
	    end
	  with Unix_error (e,s1,s2) -> ()
      done
    with End_of_file ->
      closedir dirh
  in
  if exists_dir root then traverse root [];
  List.rev !l

let where_in_path ?(warn=true) path filename =
  let rec search = function
    | lpe :: rem ->
	let f = Filename.concat lpe filename in
	  if Sys.file_exists f
	  then (lpe,f) :: search rem
	  else search rem
    | [] -> [] in
  let rec check_and_warn l =
    match l with
      | [] -> raise Not_found
      | (lpe, f) :: l' ->
	  if warn & l' <> [] then
	    msg_warning
	      (str filename ++ str " has been found in" ++ spc () ++
	       hov 0 (str "[ " ++
	         hv 0 (prlist_with_sep (fun () -> str " " ++ pr_semicolon())
		   (fun (lpe,_) -> str lpe) l)
	         ++ str " ];") ++ fnl () ++
	       str "loading " ++ str f);
	  (lpe, f) in
  check_and_warn (search path)

let find_file_in_path ?(warn=true) paths filename =
  if not (Filename.is_implicit filename) then
    if Sys.file_exists filename then
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

let path_separator = if Sys.os_type = "Unix" then ':' else ';'

let is_in_system_path filename =
  let path = try Sys.getenv "PATH"
             with Not_found -> error "system variable PATH not found" in
  let lpath = CUnix.path_to_list path in
  is_in_path lpath filename

let open_trapping_failure name =
  try open_out_bin name with _ -> error ("Can't open " ^ name)

let try_remove filename =
  try Sys.remove filename
  with _ -> msgnl (str"Warning: " ++ str"Could not remove file " ++
                   str filename ++ str" which is corrupted!" )

let marshal_out ch v = Marshal.to_channel ch v []
let marshal_in ch =
  try Marshal.from_channel ch
  with End_of_file -> error "corrupted file: reached end of file"

exception Bad_magic_number of string

let raw_extern_intern magic suffix =
  let extern_state name =
    let filename = CUnix.make_suffix name suffix in
    let channel = open_trapping_failure filename in
    output_binary_int channel magic;
    filename,channel
  and intern_state filename =
    let channel = open_in_bin filename in
    if input_binary_int channel <> magic then
      raise (Bad_magic_number filename);
    channel
  in
  (extern_state,intern_state)

let extern_intern ?(warn=true) magic suffix =
  let (raw_extern,raw_intern) = raw_extern_intern magic suffix in
  let extern_state name val_0 =
    try
      let (filename,channel) = raw_extern name in
      try
        marshal_out channel val_0;
        close_out channel
      with e ->
	begin try_remove filename; raise e end
    with Sys_error s -> error ("System error: " ^ s)
  and intern_state paths name =
    try
      let _,filename = find_file_in_path ~warn paths (CUnix.make_suffix name suffix) in
      let channel = raw_intern filename in
      let v = marshal_in channel in
      close_in channel;
      v
    with Sys_error s ->
      error("System error: " ^ s)
  in
  (extern_state,intern_state)

let with_magic_number_check f a =
  try f a
  with Bad_magic_number fname ->
    errorlabstrm "with_magic_number_check"
    (str"File " ++ str fname ++ strbrk" has bad magic number." ++ spc () ++
    strbrk "It is corrupted or was compiled with another version of Coq.")

(* Communication through files with another executable *)

let connect writefun readfun com =
  let name = Filename.basename com in
  let tmp_to = Filename.temp_file ("coq-"^name^"-in") ".xml" in
  let tmp_from = Filename.temp_file ("coq-"^name^"-out") ".xml" in
  let ch_to_in,ch_to_out =
    try open_in tmp_to, open_out tmp_to
    with Sys_error s -> error ("Cannot set connection to "^com^"("^s^")") in
  let ch_from_in,ch_from_out =
    try open_in tmp_from, open_out tmp_from
    with Sys_error s ->
      close_out ch_to_out; close_in ch_to_in;
      error ("Cannot set connection from "^com^"("^s^")") in
  writefun ch_to_out;
  close_out ch_to_out;
  let pid =
    let ch_to' = Unix.descr_of_in_channel ch_to_in in
    let ch_from' = Unix.descr_of_out_channel ch_from_out in
    try Unix.create_process com [|com|] ch_to' ch_from' Unix.stdout
    with Unix.Unix_error (err,_,_) ->
      close_in ch_to_in; close_in ch_from_in; close_out ch_from_out;
      unlink tmp_from; unlink tmp_to;
      error ("Cannot execute "^com^"("^(Unix.error_message err)^")") in
  close_in ch_to_in;
  close_out ch_from_out;
  (match snd (Unix.waitpid [] pid) with
    | Unix.WEXITED 127 -> error (com^": cannot execute")
    | Unix.WEXITED 0 -> ()
    | _ -> error (com^" exited abnormally"));
  let a = readfun ch_from_in in
  close_in ch_from_in;
  unlink tmp_from;
  unlink tmp_to;
  a

(* Time stamps. *)

type time = float * float * float

let get_time () =
  let t = times ()  in
  (time(), t.tms_utime, t.tms_stime)

let time_difference (t1,_,_) (t2,_,_) = t2 -. t1

let fmt_time_difference (startreal,ustart,sstart) (stopreal,ustop,sstop) =
  real (stopreal -. startreal) ++ str " secs " ++
  str "(" ++
  real ((-.) ustop ustart) ++ str "u" ++
  str "," ++
  real ((-.) sstop sstart) ++ str "s" ++
  str ")"
