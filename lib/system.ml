
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

let make_suffix name suffix =
  if Filename.check_suffix name suffix then name else (name ^ suffix)

let open_trapping_failure open_fun name suffix =
  let rname = make_suffix name suffix in
  try open_fun rname with _ -> error ("Can't open " ^ rname)

let (extern_intern :
      int -> string -> ((string -> 'a -> unit) * (string -> 'a)))
  = fun magic suffix ->

  let extern_state name val_0 = 
    try
      let (expname,channel) =
        open_trapping_failure (fun n -> n,open_out_bin n) name suffix in
      try
        output_binary_int channel magic;
        output_value channel val_0;
        close_out channel
      with e -> begin
        (try Sys.remove expname
         with _ -> mSGNL [< 'sTR"Warning: " ; 'sTR"Could not remove file " ;
                            'sTR expname ; 'sTR" which is corrupted !!" >]);
        raise e
      end
    with Sys_error s -> error ("System error: " ^ s)

  and intern_state name = 
    try
      let fname = find_file_in_path (make_suffix name suffix) in
      let channel = open_in_bin fname in
      if input_binary_int channel <> magic then
        error (fname^" not compiled with the current version of Coq");
      let v = input_value(channel) in
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

