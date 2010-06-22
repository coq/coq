(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Unix

(* Expanding shell variables and home-directories *)

let safe_getenv_def var def =
  try
    Sys.getenv var
  with Not_found ->
    warning ("Environment variable "^var^" not found: using '"^def^"' .");
    flush Pervasives.stdout;
    def

let getenv_else s dft = try Sys.getenv s with Not_found -> dft

let home = (safe_getenv_def "HOME" ".")

let safe_getenv n = safe_getenv_def n ("$"^n)

let rec expand_atom s i =
  let l = String.length s in
  if i<l && (is_digit s.[i] or is_letter s.[i] or s.[i] = '_')
  then expand_atom s (i+1)
  else i

let rec expand_macros s i =
  let l = String.length s in
  if i=l then s else
    match s.[i] with
      | '$' ->
	  let n = expand_atom s (i+1) in
	  let v = safe_getenv (String.sub s (i+1) (n-i-1)) in
	  let s = (String.sub s 0 i)^v^(String.sub s n (l-n)) in
	  expand_macros s (i + String.length v)
      | '~' when i = 0 ->
	  let n = expand_atom s (i+1) in
	  let v =
	    if n=i+1 then home
	    else (getpwnam (String.sub s (i+1) (n-i-1))).pw_dir
	  in
	  let s = v^(String.sub s n (l-n)) in
	  expand_macros s (String.length v)
      | c -> expand_macros s (i+1)

let expand_path_macros s = expand_macros s 0

(* Files and load path. *)

type physical_path = string
type load_path = physical_path list

let physical_path_of_string s = s
let string_of_physical_path p = p

(* 
 * Split a path into a list of directories. A one-liner with Str, but Coq
 * doesn't seem to use this library at all, so here is a slighly longer version.
 *)

let lpath_from_path path path_separator =
  let n = String.length path in
  let rec aux i l =
    if i < n then
      let j =
        try String.index_from path i path_separator
        with Not_found -> n
      in
      let dir = String.sub path i (j-i) in
      aux (j+1) (dir::l)
    else
      l
  in List.rev (aux 0 [])

(* Hints to partially detects if two paths refer to the same repertory *)
let rec remove_path_dot p =
  let curdir = Filename.concat Filename.current_dir_name "" in (* Unix: "./" *)
  let n = String.length curdir in
  if String.length p > n && String.sub p 0 n = curdir then
    remove_path_dot (String.sub p n (String.length p - n))
  else
    p

let strip_path p =
  let cwd = Filename.concat (Sys.getcwd ()) "" in (* Unix: "`pwd`/" *)
  let n = String.length cwd in
  if String.length p > n && String.sub p 0 n = cwd then
    remove_path_dot (String.sub p n (String.length p - n))
  else
    remove_path_dot p

let canonical_path_name p =
  let current = Sys.getcwd () in
  try
    Sys.chdir p;
    let p' = Sys.getcwd () in
    Sys.chdir current;
    p'
  with Sys_error _ ->
    (* We give up to find a canonical name and just simplify it... *)
    strip_path p

(* All subdirectories, recursively *)

let exists_dir dir =
  try let _ = opendir dir in true with Unix_error _ -> false

let skipped_dirnames = ref ["CVS"; "_darcs"]

let exclude_search_in_dirname f = skipped_dirnames := f :: !skipped_dirnames

let ok_dirname f =
  f <> "" && f.[0] <> '.' && not (List.mem f !skipped_dirnames) &&
  try ignore (check_ident f); true with _ -> false

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
  let lpath = lpath_from_path path path_separator in
  is_in_path lpath filename

let make_suffix name suffix =
  if Filename.check_suffix name suffix then name else (name ^ suffix)

let file_readable_p name =
  try access name [R_OK];true with Unix_error (_, _, _) -> false

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
    let filename = make_suffix name suffix in
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
      let _,filename = find_file_in_path ~warn paths (make_suffix name suffix) in
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

let run_command converter f c =
  let result = Buffer.create 127 in
  let cin,cout,cerr = Unix.open_process_full c (Unix.environment ()) in
  let buff = String.make 127 ' ' in
  let buffe = String.make 127 ' ' in
  let n = ref 0 in
  let ne = ref 0 in

  while n:= input cin buff 0 127 ; ne := input cerr buffe 0 127 ;
    !n+ !ne <> 0
  do
    let r = converter (String.sub buff 0 !n) in
    f r;
    Buffer.add_string result r;
    let r = converter (String.sub buffe 0 !ne) in
    f r;
    Buffer.add_string result r
  done;
  (Unix.close_process_full (cin,cout,cerr),  Buffer.contents result)

(* Time stamps. *)

type time = float * float * float

let process_time () =
  let t = times ()  in
  (t.tms_utime, t.tms_stime)

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
