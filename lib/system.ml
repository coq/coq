
(* $Id$ *)

open Pp
open Util

(* Files and load path. *)

let load_path = ref ([] : string list)

let add_path dir = load_path := dir :: !load_path

let del_path dir =
  if List.mem dir !load_path then
    load_path := List.filter (fun s -> s <> dir) !load_path

(* TODO: rétablir glob (expansion ~user et $VAR) si on le juge nécessaire *)
let glob s = s

let search_in_path path filename =
  let rec search = function
    | dir :: rem ->
	let f = glob (Filename.concat dir filename) in
	if Sys.file_exists f then f else search rem
    | [] ->
	raise Not_found
  in
  search path

let where_in_path = search_in_path

let find_file_in_path name =
  let globname = glob name in
  if not (Filename.is_relative globname) then
    globname
  else 
    try 
      search_in_path !load_path name
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

(*Gives the list of all the directories under dir*)
let alldir dir =
  let ini = Unix.getcwd()
  and tmp = Filename.temp_file "coq" "rec"
  and lst = ref [] in
  Unix.chdir dir;
  let bse = Unix.getcwd() in
  let _ = Sys.command ("find "^bse^" -type d >> "^tmp) in
  let inf = open_in tmp in
  try
    while true do
      lst := !lst @ [input_line inf]
    done;
    []
  with End_of_file ->
    close_in inf;
    Sys.remove tmp;
    Unix.chdir ini;
    !lst

let open_trapping_failure open_fun name suffix =
  let rname = make_suffix name suffix in
  try open_fun rname with _ -> error ("Can't open " ^ rname)

let try_remove f =
  try Sys.remove f
  with _ -> mSGNL [< 'sTR"Warning: " ; 'sTR"Could not remove file " ;
                     'sTR f ; 'sTR" which is corrupted !!" >]

exception Bad_magic_number of string

let (raw_extern_intern :
     int -> string -> 
       (string -> string * out_channel) * (string -> string * in_channel))
  = fun magic suffix ->

    let extern_state name = 
      let (_,channel) as filec =
	open_trapping_failure (fun n -> n,open_out_bin n) name suffix in
      output_binary_int channel magic;
      filec
    and intern_state name = 
      let fname = find_file_in_path (make_suffix name suffix) in
      let channel = open_in_bin fname in
      if input_binary_int channel <> magic then
        raise (Bad_magic_number fname);
      (fname,channel)
    in 
    (extern_state,intern_state)

let (extern_intern :
     int -> string -> (string -> 'a -> unit) * (string -> 'a))
  = fun magic suffix ->

    let (raw_extern,raw_intern) = raw_extern_intern magic suffix in
    let extern_state name val_0 = 
      try
	let (fname,channel) = raw_extern name in
      	try
          output_value channel val_0;
          close_out channel
      	with e -> 
	  begin try_remove fname; raise e end
      with Sys_error s -> error ("System error: " ^ s)

  and intern_state name = 
    try
      let (fname,channel) = raw_intern name in
      let v = input_value channel in
      close_in channel; 
      v
    with Sys_error s -> error("System error: " ^ s)

  in 
  (extern_state,intern_state)


(* Time stamps. *)

type time_stamp = float

let get_time_stamp () = Unix.time()

let compare_time_stamps t1 t2 =
  let dt = t2 -. t1 in
  if dt < 0.0 then -1 else if dt = 0.0 then 0 else 1

