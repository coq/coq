(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Printf
open Coqdep_lexer
open Unix

let stderr = Pervasives.stderr
let stdout = Pervasives.stdout

let option_c = ref false
let option_D = ref false
let option_w = ref false
let option_sort = ref false
let option_noglob = ref false
let option_slash = ref false

let suffixe = ref ".vo"

type dir = string option

(* filename for printing *)
let (//) s1 s2 =
  if !option_slash then s1^"/"^s2 else Filename.concat s1 s2

let (/) = Filename.concat

let file_concat l =
  if l=[] then "<empty>" else
    List.fold_left (//) (List.hd l) (List.tl l)

(** [get_extension f l] checks whether [f] has one of the extensions
    listed in [l]. It returns [f] without its extension, alongside with
    the extension. When no extension match, [(f,"")] is returned *)

let rec get_extension f = function
  | [] -> (f, "")
  | s :: _ when Filename.check_suffix f s -> (Filename.chop_suffix f s, s)
  | _ :: l -> get_extension f l

(** [basename_noext] removes both the directory part and the extension
    (if necessary) of a filename *)

let basename_noext filename =
  let fn = Filename.basename filename in
  try Filename.chop_extension fn with _ -> fn

(** ML Files specified on the command line. In the entries:
    - the first string is the basename of the file, without extension nor
      directory part
    - the second string of [mlAccu] is the extension (either .ml or .ml4)
    - the [dir] part is the directory, with None used as the current directory
*)

let mlAccu  = ref ([] : (string * string * dir) list)
and mliAccu = ref ([] : (string * dir) list)
and mllibAccu = ref ([] : (string * dir) list)

(** Coq files specifies on the command line:
    - first string is the full filename, with only its extension removed
    - second string is the absolute version of the previous (via getcwd)
*)

let vAccu   = ref ([] : (string * string) list)

(** Queue operations *)

let addQueue q v = q := v :: !q

let safe_hash_add clq q (k,v) =
  try
    let v2 = Hashtbl.find q k in
    if v<>v2 then 
      let rec add_clash = function
          (k1,l1)::cltl when k=k1 -> (k1,v::l1)::cltl
        | cl::cltl -> cl::add_clash cltl
        | [] -> [(k,[v;v2])] in
      clq := add_clash !clq
  with Not_found -> Hashtbl.add q k v

(** Files found in the loadpaths.
    For the ML files, the string is the basename without extension.
    To allow ML source filename to be potentially capitalized, 
    we perform a double search.
*)

let mkknown () =
  let h = (Hashtbl.create 19 : (string, dir) Hashtbl.t) in
  let add x s = Hashtbl.add h x s
  and iter f = Hashtbl.iter f h
  and search x =
    try Some (Hashtbl.find h (String.uncapitalize x))
    with Not_found ->
      try Some (Hashtbl.find h (String.capitalize x))
      with Not_found -> None
  in add, iter, search

let add_ml_known, iter_ml_known, search_ml_known = mkknown ()
let add_mli_known, iter_mli_known, search_mli_known = mkknown ()
let add_mllib_known, _, search_mllib_known = mkknown ()

let vKnown = (Hashtbl.create 19 : (string list, string) Hashtbl.t)
let coqlibKnown = (Hashtbl.create 19 : (string list, unit) Hashtbl.t)

let clash_v = ref ([]: (string list * string list) list)

let warning_module_notfound f s =
  eprintf "*** Warning : in file %s, library " f;
  eprintf "%s.v is required and has not been found in loadpath !\n"
    (String.concat "." s);
  flush stderr

let warning_notfound f s =
  eprintf "*** Warning : in file %s, the file " f;
  eprintf "%s.v is required and has not been found !\n" s;
  flush stderr

let warning_declare f s =
  eprintf "*** Warning : in file %s, Declared ML Module " f;
  eprintf "%s has not been found !\n" s;
  flush stderr

let warning_clash file dir =
  match List.assoc dir !clash_v with
    (f1::f2::fl) ->
      let f = Filename.basename f1 in
      let d1 = Filename.dirname f1 in
      let d2 = Filename.dirname f2 in
      let dl = List.map Filename.dirname (List.rev fl) in
      eprintf
        "*** Warning : in file %s, \n    required library %s is ambiguous!\n    (found %s.v in "
        file (String.concat "." dir) f;
      List.iter (fun s -> eprintf "%s, " s) dl;
      eprintf "%s and %s)\n" d2 d1
  | _ -> assert false

let safe_assoc verbose file k =
  if verbose && List.mem_assoc k !clash_v then warning_clash file k;
  Hashtbl.find vKnown k

let absolute_dir dir =
  let current = Sys.getcwd () in
    Sys.chdir dir;
    let dir' = Sys.getcwd () in
      Sys.chdir current;
      dir'

let absolute_file_name basename odir =
  let dir = match odir with Some dir -> dir | None -> "." in
  absolute_dir dir // basename

let file_name s = function
  | None     -> s
  | Some "." -> s
  | Some d   -> d // s

let depend_ML str =
  match search_mli_known str, search_ml_known str with
    | Some mlidir, Some mldir ->
	let mlifile = file_name str mlidir
	and mlfile = file_name str mldir in
	(" "^mlifile^".cmi"," "^mlfile^".cmx")
    | None, Some mldir ->
	let mlfile = file_name str mldir in
	(" "^mlfile^".cmo"," "^mlfile^".cmx")
    | Some mlidir, None ->
	let mlifile = file_name str mlidir in
	(" "^mlifile^".cmi"," "^mlifile^".cmi")
    | None, None -> "", ""

let traite_fichier_ML md ext =
  try 
    let chan = open_in (md ^ ext) in 
    let buf = Lexing.from_channel chan in 
    let deja_vu = ref [md] in
    let a_faire = ref "" in
    let a_faire_opt = ref "" in
    begin try 
      while true do
	let (Use_module str) = caml_action buf in
	if List.mem str !deja_vu then 
	  ()
	else begin
	  addQueue deja_vu str;
	  let byte,opt = depend_ML str in
	  a_faire := !a_faire ^ byte;
	  a_faire_opt := !a_faire_opt ^ opt
	end
      done
    with Fin_fichier -> ()
    end;
    close_in chan;
    (!a_faire, !a_faire_opt)
  with Sys_error _ -> ("","")

let traite_fichier_mllib md ext =
  try
    let chan = open_in (md ^ ext) in
    let list = mllib_list (Lexing.from_channel chan) in
    let a_faire = ref "" in
    let a_faire_opt = ref "" in
    List.iter
      (fun str -> match search_ml_known str with
	 | Some mldir ->
	     let file = file_name str mldir in
	     a_faire := !a_faire^" "^file^".cmo";
	     a_faire_opt := !a_faire_opt^" "^file^".cmx"
	 | None -> ()) list;
    (!a_faire, !a_faire_opt)
  with Sys_error _ -> ("","")

let cut_prefix p s =
  let lp = String.length p in
  let ls = String.length s in
  if ls >= lp && String.sub s 0 lp = p then String.sub s lp (ls - lp) else s

let canonize f =
  let f' = absolute_dir (Filename.dirname f) // Filename.basename f in
  match List.filter (fun (_,full) -> f' = full) !vAccu with
    | (f,_) :: _ -> f
    | _ -> f

let sort () = 
  let seen = Hashtbl.create 97 in
  let rec loop file =
    let file = canonize file in
    if not (Hashtbl.mem seen file) then begin
      Hashtbl.add seen file ();
      let cin = open_in (file ^ ".v") in
      let lb = Lexing.from_channel cin in
      try
	while true do
	  match coq_action lb with
	    | Require sl ->
		List.iter 
		  (fun s -> 
		    try loop (Hashtbl.find vKnown s)
		    with Not_found -> ())
		sl
	    | RequireString s -> loop s
	    | _ -> ()
	done
      with Fin_fichier ->
	close_in cin;
	printf "%s%s " file !suffixe
    end
  in
  List.iter (fun (name,_) -> loop name) !vAccu

let traite_fichier_Coq verbose f = 
  try 
    let chan = open_in f in 
    let buf = Lexing.from_channel chan in 
    let deja_vu_v = ref ([]: string list list)
    and deja_vu_ml = ref ([] : string list) in
    try 
      while true do
      	let tok = coq_action buf in
	match tok with
	  | Require strl ->
	      List.iter (fun str ->
		if not (List.mem str !deja_vu_v) then begin
	          addQueue deja_vu_v str;
                  try
                    let file_str = safe_assoc verbose f str in
                    printf " %s%s" (canonize file_str) !suffixe
                  with Not_found -> 
		    if verbose && not (Hashtbl.mem coqlibKnown str) then
                      warning_module_notfound f str
       		end) strl
	  | RequireString s -> 
	      let str = Filename.basename s in
	      if not (List.mem [str] !deja_vu_v) then begin
	        addQueue deja_vu_v [str];
                try
                  let file_str = Hashtbl.find vKnown [str] in
                  printf " %s%s" (canonize file_str) !suffixe
                with Not_found -> 
		  if not (Hashtbl.mem coqlibKnown [str]) then
		    warning_notfound f s
       	      end
	  | Declare sl ->
	      let declare suff dir s =
		let base = file_name s dir in
		let opt =
		  if Coq_config.has_natdynlink then " "^base^".cmxs" else ""
		in
		printf " %s%s%s" base suff opt
	      in
	      let decl str =
                let s = basename_noext str in
		if not (List.mem s !deja_vu_ml) then begin
		  addQueue deja_vu_ml s;
		  match search_mllib_known s with
		    | Some mldir -> declare ".cma" mldir s
		    | None ->
			match search_ml_known s with
			  | Some mldir -> declare ".cmo" mldir s
			  | None -> warning_declare f str
		end
	      in List.iter decl sl
	  | Load str -> 
	      let str = Filename.basename str in
	      if not (List.mem [str] !deja_vu_v) then begin
	        addQueue deja_vu_v [str];
                try
                  let file_str = Hashtbl.find vKnown [str] in
                  printf " %s.v" (canonize file_str)
                with Not_found -> ()
       	      end
      done
    with Fin_fichier -> ();
      close_in chan
  with Sys_error _ -> () 


let (dep_tab : (string,string list) Hashtbl.t) = Hashtbl.create 151
						     
let mL_dep_list b f = 
  try 
    Hashtbl.find dep_tab f
  with Not_found ->
    let deja_vu = ref ([] : string list) in 
    try 
      let chan = open_in f in 
      let buf = Lexing.from_channel chan in 
      try 
	while true do
	  let (Use_module str) = caml_action buf in
	  if str = b then begin
	    eprintf "*** Warning : in file %s the" f;
	    eprintf " notation %s. is useless !\n" b;
	    flush stderr
	  end else
            if not (List.mem str !deja_vu) then addQueue deja_vu str
      	done; []
      with Fin_fichier -> begin
	close_in chan; 
	let rl = List.rev !deja_vu in
      	Hashtbl.add dep_tab f rl;
	rl
      end
    with Sys_error _ -> []

let affiche_Declare f dcl = 
  printf "\n*** In file %s: \n" f;
  printf "Declare ML Module";
  List.iter (fun str -> printf " \"%s\"" str) dcl;
  printf ".\n";
  flush stdout

let warning_Declare f dcl =
  eprintf "*** Warning : in file %s, the ML modules" f;
  eprintf " declaration should be\n";
  eprintf "*** Declare ML Module";
  List.iter (fun str -> eprintf " \"%s\"" str) dcl;
  eprintf ".\n";
  flush stderr

let traite_Declare f = 
  let decl_list = ref ([] : string list) in
  let rec treat = function
    | s :: ll ->
	let s' = basename_noext s in
	(match search_ml_known s with
	   | Some mldir when not (List.mem s' !decl_list) ->
	       let fullname = file_name (String.uncapitalize s') mldir in
	       let depl = mL_dep_list s (fullname ^ ".ml") in
	       treat depl;
	       decl_list := s :: !decl_list
	   | _ -> ());
	treat ll
    | [] -> ()
  in
    try
      let chan = open_in f in
      let buf = Lexing.from_channel chan in
	begin try 
	    while true do
      	      let tok = coq_action buf in
      		(match tok with
		  | Declare sl -> 
		      decl_list := [];
		      treat sl;
		      decl_list := List.rev !decl_list;
		      if !option_D then 
			affiche_Declare f !decl_list
		      else if !decl_list <> sl then
			warning_Declare f !decl_list
		  | _ -> ())
	    done
	  with Fin_fichier -> () end;
	close_in chan
    with Sys_error _ -> ()

let file_mem (f,_,d) =
  let rec loop = function
    | (f1,_,d1) :: l -> (f1 = f && d1 = d) || (loop l)
    | _ -> false
  in
  loop

let mL_dependencies () =
  List.iter 
    (fun (name,ext,dirname) ->
       let fullname = file_name name dirname in
       let (dep,dep_opt) = traite_fichier_ML fullname ext in
       let intf =
	 if List.mem (name,dirname) !mliAccu then " "^fullname^".cmi" else ""
       in
       printf "%s.cmo: %s%s%s%s\n" fullname fullname ext intf dep;
       printf "%s.cmx: %s%s%s%s\n" fullname fullname ext intf dep_opt;
       flush stdout)
    (List.rev !mlAccu);
  List.iter
    (fun (name,dirname) ->
       let fullname = file_name name dirname in
       let (dep,_) = traite_fichier_ML fullname ".mli" in
       printf "%s.cmi: %s.mli%s\n" fullname fullname dep;
       flush stdout)
    (List.rev !mliAccu);
  List.iter
    (fun (name,dirname) ->
       let fullname = file_name name dirname in
       let (dep,dep_opt) = traite_fichier_mllib fullname ".mllib" in
       printf "%s.cma:%s\n" fullname dep;
       printf "%s.cmxa %s.cmxs:%s\n" fullname fullname dep_opt;
       flush stdout)
    (List.rev !mllibAccu)

let coq_dependencies () =
  List.iter
    (fun (name,_) ->
       let glob = if !option_noglob then "" else " "^name^".glob" in
       printf "%s%s%s: %s.v" name !suffixe glob name;
       traite_fichier_Coq true (name ^ ".v");
       printf "\n";
       flush stdout)
    (List.rev !vAccu)

let declare_dependencies () =
  List.iter
    (fun (name,_) ->
       traite_Declare (name^".v");
       flush stdout)
    (List.rev !vAccu)

let rec warning_mult suf iter =
  let tab = Hashtbl.create 151 in
  let check f d =
    begin try
      let d' = Hashtbl.find tab f in
      if (Filename.dirname (file_name f d))
        <> (Filename.dirname (file_name f d')) then begin
	  eprintf "*** Warning : the file %s is defined twice!\n" (f ^ suf);
	  flush stderr
	end
    with Not_found -> () end;
    Hashtbl.add tab f d
  in
  iter check

let usage () =
  eprintf
  "[ usage: coqdep [-w] [-I dir] [-R dir coqdir] [-coqlib dir] [-c] [-i] [-D] <filename>+ ]\n";
  flush stderr;
  exit 1

let add_coqlib_known phys_dir log_dir f =
  match get_extension f [".vo"] with
    | (basename,".vo") ->
	let name = log_dir@[basename] in
	Hashtbl.add coqlibKnown [basename] ();
	Hashtbl.add coqlibKnown name ()
    | _ -> ()


let add_known phys_dir log_dir f =
  match get_extension f [".v";".ml";".mli";".ml4";".mllib"] with
    | (basename,".v") ->
	let name = log_dir@[basename] in
	let file = phys_dir//basename in
	let paths = [name;[basename]] in
	List.iter
	  (fun n -> safe_hash_add clash_v vKnown (n,file)) paths
    | (basename,(".ml"|".ml4")) -> add_ml_known basename (Some phys_dir)
    | (basename,".mli") -> add_mli_known basename (Some phys_dir)
    | (basename,".mllib") -> add_mllib_known basename (Some phys_dir)
    | _ -> ()

(* Visits all the directories under [dir], including [dir], 
   or just [dir] if [recur=false] *)

let rec add_directory recur add_file phys_dir log_dir = 
  let dirh = opendir phys_dir in
  try
    while true do
      let f = readdir dirh in
      (* we avoid . .. and all hidden files and subdirs (e.g. .svn, _darcs) *)
      if f.[0] <> '.' && f.[0] <> '_' then
        let phys_f = phys_dir//f in
	match try (stat phys_f).st_kind with _ -> S_BLK with
	  | S_DIR when recur -> add_directory recur add_file phys_f (log_dir@[f])
	  | S_REG -> add_file phys_dir log_dir f
	  | _ -> ()
    done
  with End_of_file -> closedir dirh

let add_dir add_file phys_dir log_dir = 
  try add_directory false add_file phys_dir log_dir with Unix_error _ -> ()

let add_rec_dir add_file phys_dir log_dir = 
  handle_unix_error (add_directory true add_file phys_dir) log_dir

let rec treat_file old_dirname old_name =
  let name = Filename.basename old_name 
  and new_dirname = Filename.dirname old_name in
  let dirname = 
    match (old_dirname,new_dirname) with 
      | (d, ".") -> d
      | (None,d) -> Some d
      | (Some d1,d2) -> Some (d1//d2) 
  in
  let complete_name = file_name name dirname in
  match try (stat complete_name).st_kind with _ -> S_BLK with 
    | S_DIR ->
	(if name.[0] <> '.' then 
	   let dir=opendir complete_name in
           let newdirname = 
             match dirname with 
               | None -> name
               | Some d -> d//name 
	   in
	   try 
	     while true do treat_file (Some newdirname) (readdir dir) done
	   with End_of_file -> closedir dir)
    | S_REG ->
	(match get_extension name [".v";".ml";".mli";".ml4";".mllib"] with
	   | (base,".v") ->
	       let name = file_name base dirname
	       and absname = absolute_file_name base dirname in
	       addQueue vAccu (name, absname)
	   | (base,(".ml"|".ml4" as ext)) -> addQueue mlAccu (base,ext,dirname)
	   | (base,".mli") -> addQueue mliAccu (base,dirname)
	   | (base,".mllib") -> addQueue mllibAccu (base,dirname)
	   | _ -> ())
    | _ -> ()

let rec parse = function
  | "-c" :: ll -> option_c := true; parse ll
  | "-D" :: ll -> option_D := true; parse ll
  | "-w" :: ll -> option_w := true; parse ll
  | "-boot" :: ll -> Flags.boot := true; parse ll
  | "-sort" :: ll -> option_sort := true; parse ll
  | "-noglob" :: ll | "-no-glob" :: ll -> option_noglob := true; parse ll
  | "-I" :: r :: ll -> add_dir add_known r []; parse ll
  | "-I" :: [] -> usage ()
  | "-R" :: r :: ln :: ll -> add_rec_dir add_known r [ln]; parse ll
  | "-R" :: ([] | [_]) -> usage ()
  | "-coqlib" :: (r :: ll) -> Flags.coqlib_spec := true; Flags.coqlib := r; parse ll
  | "-coqlib" :: [] -> usage ()
  | "-suffix" :: (s :: ll) -> suffixe := s ; parse ll
  | "-suffix" :: [] -> usage ()
  | "-slash" :: ll -> option_slash := true; parse ll
  | f :: ll -> treat_file None f; parse ll
  | [] -> ()

let coqdep () =
  if Array.length Sys.argv < 2 then usage ();
  parse (List.tl (Array.to_list Sys.argv));
  if !Flags.boot then begin
    add_rec_dir add_known "theories" ["Coq"];
    add_rec_dir add_known "contrib" ["Coq"]
  end else begin
    let coqlib = Envars.coqlib () in
    add_rec_dir add_coqlib_known (coqlib//"theories") ["Coq"];
    add_rec_dir add_coqlib_known (coqlib//"contrib") ["Coq"];
    add_dir add_coqlib_known (coqlib//"user-contrib") []
  end;
  List.iter (fun (f,d) -> add_mli_known f d) !mliAccu;
  List.iter (fun (f,d) -> add_mllib_known f d) !mllibAccu;
  List.iter (fun (f,_,d) -> add_ml_known f d) !mlAccu;
  warning_mult ".mli" iter_mli_known;
  warning_mult ".ml" iter_ml_known;
  if !option_sort then begin sort (); exit 0 end;
  if !option_c && not !option_D then mL_dependencies ();
  if not !option_D then coq_dependencies ();
  if !option_w || !option_D then declare_dependencies ()

let _ = Printexc.catch coqdep ()
