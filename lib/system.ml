
(* $Id$ *)

open Pp
open Util
open Unix

(* Files and load path. *)
(* All subdirectories, recursively *)

type load_path_entry = {
  directory : string;
  root_dir : string;
  relative_subdir : string }

type load_path = load_path_entry list

let exists_dir dir =
  try let _ = opendir dir in true
  with Unix_error _ -> false

let all_subdirs root =
  let l = ref [] in
  let add f rel = 
    l := { directory = f; root_dir = root; relative_subdir = rel } :: !l 
  in
  let rec traverse dir rel =
    let dirh = 
      try opendir dir with Unix_error _ -> invalid_arg "all_subdirs" 
    in
    try
      while true do
	let f = readdir dirh in
	if f <> "." && f <> ".." then
	  let file = Filename.concat dir f in
	  if (stat file).st_kind = S_DIR then begin
	    let newrel = Filename.concat rel f in
	    add file newrel;
	    traverse file newrel
	  end
      done
    with End_of_file ->
      closedir dirh
  in
  traverse root ""; List.rev !l

let safe_getenv_def var def =
  try 
    Sys.getenv var
  with Not_found ->
    warning ("Environnement variable "^var^" not found: using '"^def^"' .");
    def

let home = (safe_getenv_def "HOME" ".")

(* TODO: rétablir glob (expansion ~user et $VAR) si on le juge nécessaire *)
let glob s = s

let search_in_path path filename =
  let rec search = function
    | lpe :: rem ->
	let f = glob (Filename.concat lpe.directory filename) in
	if Sys.file_exists f then (lpe,f) else search rem
    | [] ->
	raise Not_found
  in
  search path

let where_in_path = search_in_path

let find_file_in_path paths name =
  let globname = glob name in
  if not (Filename.is_relative globname) then
    let root = Filename.dirname globname in
    { directory = root; root_dir = root; relative_subdir = "" }, globname
  else 
    try 
      search_in_path paths name
    with Not_found ->
      errorlabstrm "System.find_file_in_path"
	(hOV 0 [< 'sTR"Can't find file" ; 'sPC ; 'sTR name ; 'sPC ; 
		  'sTR"on loadpath" >])

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
  let rname = make_suffix name suffix in
  try open_fun rname with _ -> error ("Can't open " ^ rname)

let try_remove f =
  try Sys.remove f
  with _ -> mSGNL [< 'sTR"Warning: " ; 'sTR"Could not remove file " ;
                     'sTR f ; 'sTR" which is corrupted!" >]

let marshal_out ch v = Marshal.to_channel ch v []
let marshal_in ch = Marshal.from_channel ch

exception Bad_magic_number of string

let raw_extern_intern magic suffix =
  let extern_state name = 
    let (_,channel) as filec =
      open_trapping_failure (fun n -> n,open_out_bin n) name suffix in
    output_binary_int channel magic;
    filec
  and intern_state paths name = 
    let lpe,fname = find_file_in_path paths (make_suffix name suffix) in
    let channel = open_in_bin fname in
    if input_binary_int channel <> magic then
      raise (Bad_magic_number fname);
    (lpe,fname,channel)
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
      let (_,fname,channel) = raw_intern paths name in
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
  [< 'rEAL(stopreal -. startreal); 'sTR" secs ";
     'sTR"(";
     'rEAL((-.) ustop ustart); 'sTR"u";
     'sTR",";
     'rEAL((-.) sstop sstart); 'sTR"s";
     'sTR")" >]
