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

let home = (safe_getenv_def "HOME" ".")

let safe_getenv n = safe_getenv_def n ("$"^n)

let rec expand_atom s i =
  let l = String.length s in
  if i<l && (is_digit s.[i] or is_letter s.[i] or s.[i] = '_')
  then expand_atom s (i+1)
  else i

let rec expand_macros b s i =
  let l = String.length s in
  if i=l then s else
    match s.[i] with
      | '$' -> 
	  let n = expand_atom s (i+1) in
	  let v = safe_getenv (String.sub s (i+1) (n-i-1)) in
	  let s = (String.sub s 0 i)^v^(String.sub s n (l-n)) in
	  expand_macros false s (i + String.length v)
      | '/' ->
	  expand_macros true s (i+1)
      | '~' ->
	  let n = expand_atom s (i+1) in
	  let v =
	    if n=i+1 then home
	    else (getpwnam (String.sub s (i+1) (n-i-1))).pw_dir
	  in
	  let s = v^(String.sub s n (l-n)) in
	  expand_macros false s (String.length v)
      | c -> expand_macros false s (i+1)

let glob s = expand_macros true s 0

(* Files and load path. *)

type physical_path = string
type load_path = physical_path list

(* All subdirectories, recursively *)

let exists_dir dir =
  try let _ = opendir dir in true with Unix_error _ -> false

let all_subdirs ~unix_path:root =
  let l = ref [] in
  let add f rel = l := (f, rel) :: !l in
  let rec traverse dir rel =
    let dirh = opendir dir in
    try
      while true do
	let f = readdir dirh in
	if f <> "" && f.[0] <> '.' && (not Coq_config.local or (f <> "CVS"))
        then
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
  if exists_dir root then
   begin
     add root [];
     traverse root []
   end ;
  List.rev !l

let search_in_path path filename =
  let rec search = function
    | lpe :: rem ->
	let f = glob (Filename.concat lpe filename) in
	if Sys.file_exists f then (lpe,f) else search rem
    | [] ->
	raise Not_found
  in
  search path

let where_in_path = search_in_path

let find_file_in_path paths name =
  let globname = glob name in
  if not (Filename.is_implicit globname) then
    let root = Filename.dirname globname in
    root, globname
  else 
    try 
      search_in_path paths name
    with Not_found ->
      errorlabstrm "System.find_file_in_path"
	(hov 0 (str "Can't find file" ++ spc () ++ str name ++ spc () ++ 
		str "on loadpath"))

let is_in_path lpath filename =
  try
    let _ = search_in_path lpath filename in true
  with
    Not_found -> false

let make_suffix name suffix =
  if Filename.check_suffix name suffix then name else (name ^ suffix)

let file_readable_p na =
  try access (glob na) [R_OK];true with Unix_error (_, _, _) -> false

let open_trapping_failure open_fun name suffix =
  let rname = glob (make_suffix name suffix) in
  try open_fun rname with _ -> error ("Can't open " ^ rname)

let try_remove f =
  try Sys.remove f
  with _ -> msgnl (str"Warning: " ++ str"Could not remove file " ++
                   str f ++ str" which is corrupted!" )

let marshal_out ch v = Marshal.to_channel ch v []
let marshal_in ch =
  try Marshal.from_channel ch
  with End_of_file -> error "corrupted file: reached end of file"

exception Bad_magic_number of string

let raw_extern_intern magic suffix =
  let extern_state name = 
    let (_,channel) as filec =
      open_trapping_failure (fun n -> n,open_out_bin n) name suffix in
    output_binary_int channel magic;
    filec
  and intern_state fname = 
    let channel = open_in_bin fname in
    if input_binary_int channel <> magic then
      raise (Bad_magic_number fname);
    channel
  in 
  (extern_state,intern_state)

let extern_intern magic suffix =
  let (raw_extern,raw_intern) = raw_extern_intern magic suffix in
  let extern_state name val_0 = 
    try
      let (fname,channel) = raw_extern name in
      try
        marshal_out channel val_0;
        close_out channel
      with e -> 
	begin try_remove fname; raise e end
    with Sys_error s -> error ("System error: " ^ s)
  and intern_state paths name = 
    try
      let _,fname = find_file_in_path paths (make_suffix name suffix) in
      let channel = raw_intern fname in
      let v = marshal_in channel in
      close_in channel; 
      v
    with Sys_error s -> 
      error("System error: " ^ s)
  in 
  (extern_state,intern_state)


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
