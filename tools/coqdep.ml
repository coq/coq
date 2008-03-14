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

let coqlib = ref Coq_config.coqlib

let option_c = ref false
let option_D = ref false
let option_w = ref false
let option_i = ref false
let option_sort = ref false
let option_glob = ref false
let option_slash = ref false

let suffixe = ref ".vo"
let suffixe_spec = ref ".vi"

type dir = string option

(* filename for printing *)
let (//) s1 s2 =
  if !option_slash then s1^"/"^s2 else Filename.concat s1 s2

let (/) = Filename.concat

let file_concat l =
  if l=[] then "<empty>" else
    List.fold_left (//) (List.hd l) (List.tl l)

(* Files specified on the command line *)
let mlAccu  = ref ([] : (string * string * dir) list) 
and mliAccu = ref ([] : (string * string * dir) list) 
and vAccu   = ref ([] : (string * string) list)

(* Queue operations *)
let addQueue q v = q := v :: !q

let safe_addQueue clq q (k,v) =
  try
    let v2 = List.assoc k !q in
    if v<>v2 then 
      let rec add_clash = function
          (k1,l1)::cltl when k=k1 -> (k1,v::l1)::cltl
        | cl::cltl -> cl::add_clash cltl
        | [] -> [(k,[v;v2])] in
      clq := add_clash !clq
  with Not_found -> addQueue q (k,v)

(* Files found in the loadpaths *)
let mlKnown     = ref ([] : (string * dir) list) 
and mliKnown    = ref ([] : (string * dir) list) 
and vKnown      = ref ([] : (string list * string) list) 
and coqlibKnown = ref ([] : (string list * string) list)

let clash_v = ref ([]: (string list * string list) list)


let warning_module_notfound f s =
  eprintf "*** Warning : in file %s, module " f;
  eprintf "%s.v is required and has not been found in loadpath !\n"
    (String.concat "." s);
  flush stderr

let warning_notfound f s =
  eprintf "*** Warning : in file %s, the file " f;
  eprintf "%s.v is required and has not been found !\n" s;
  flush stderr

let warning_clash file dir =
  match List.assoc dir !clash_v with
    (f1::f2::fl) ->
      let f = Filename.basename f1 in
      let d1 = Filename.dirname f1 in
      let d2 = Filename.dirname f2 in
      let dl = List.map Filename.dirname (List.rev fl) in
      eprintf
        "*** Warning : in file %s, \n    required module %s is ambiguous!\n    (found %s.v in "
        file (String.concat "." dir) f;
      List.iter (fun s -> eprintf "%s, " s) dl;
      eprintf "%s and %s)\n" d2 d1
  | _ -> assert false

let safe_assoc verbose file k =
  if verbose && List.mem_assoc k !clash_v then warning_clash file k;
  List.assoc k !vKnown


let absolute_dir dir =
  let current = Sys.getcwd () in
  Sys.chdir dir;
  let dir' = Sys.getcwd () in
  Sys.chdir current;
  dir'

let absolute_file_name basename odir =
  let dir = match odir with Some dir -> dir | None -> "." in
  absolute_dir dir // basename
     
let file_name = function
  | (s,None)     -> file_concat s 
  | (s,Some ".") -> file_concat s
  | (s,Some d)   -> d // file_concat s

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
          begin try
            let mlidir = List.assoc str !mliKnown in
            let filename = file_name ([str],mlidir) in
      	    a_faire := !a_faire ^ " " ^ filename ^ ".cmi"; 
          with Not_found ->
            try
              let mldir = List.assoc str !mlKnown in
              let filename = file_name ([str],mldir) in
              a_faire := !a_faire ^ " " ^ filename ^ ".cmo";
            with Not_found -> ()
          end;
          begin try
            let mldir = List.assoc str !mlKnown in
            let filename = file_name ([str],mldir) in
    	    a_faire_opt := !a_faire_opt ^ " " ^ filename ^ ".cmx"
          with Not_found ->
            try
              let mlidir = List.assoc str !mliKnown in
              let filename = file_name ([str],mlidir) in
              a_faire_opt := !a_faire_opt ^ " " ^ filename ^ ".cmi"
            with Not_found -> ()
          end
	end
      done
    with Fin_fichier -> ()
    end;
    close_in chan;
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
	    | Require (_, sl) ->
		List.iter 
		  (fun s -> 
		    try loop (List.assoc s !vKnown) 
		    with Not_found -> ())
		sl
	    | RequireString (_, s) -> loop s
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
	  | Require (spec,strl) ->
	      List.iter (fun str ->
		if not (List.mem str !deja_vu_v) then begin
	          addQueue deja_vu_v str;
                  try
                    let file_str = safe_assoc verbose f str in
                    printf " %s%s" (canonize file_str)
                      (if spec then !suffixe_spec else !suffixe)
                  with Not_found -> 
		    if verbose && not (List.mem_assoc str !coqlibKnown) then
                      warning_module_notfound f str
       		end) strl
	  | RequireString (spec,s) -> 
	      let str = Filename.basename s in
	      if not (List.mem [str] !deja_vu_v) then begin
	        addQueue deja_vu_v [str];
                try
                  let file_str = List.assoc [str] !vKnown in
                  printf " %s%s" (canonize file_str)
                    (if spec then !suffixe_spec else !suffixe)
                with Not_found -> 
                  begin try  let _ = List.assoc [str] !coqlibKnown in ()
                  with Not_found -> warning_notfound f s end
       	      end
	  | Declare sl -> 
	      List.iter 
		(fun str ->
		   if not (List.mem str !deja_vu_ml) then begin
		     addQueue deja_vu_ml str;
               	     try
              	       let mldir = List.assoc str !mlKnown in
              	       printf " %s.cmo" (file_name ([str],mldir))
              	     with Not_found -> () 
		   end)
		sl
	  | Load str -> 
	      let str = Filename.basename str in
	      if not (List.mem [str] !deja_vu_v) then begin
	        addQueue deja_vu_v [str];
                try
                  let file_str = List.assoc [str] !vKnown in
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
	if (List.mem_assoc s !mlKnown) & not (List.mem s !decl_list) then begin
       	  let mldir = List.assoc s !mlKnown in
	  let fullname = file_name ([s],mldir) in
	  let depl = mL_dep_list s (fullname ^ ".ml") in
	  treat depl;
	  decl_list := s :: !decl_list
	end;
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
    (fun ((name,ext,dirname) as pairname) ->
       let fullname = file_name ([name],dirname) in
       let (dep,dep_opt) = traite_fichier_ML fullname ext in
       printf "%s.cmo: %s%s" fullname fullname ext;
       if file_mem pairname !mliAccu then printf " %s.cmi" fullname;
       printf "%s\n" dep;
       printf "%s.cmx: %s%s" fullname fullname ext;
       if file_mem pairname !mliAccu then printf " %s.cmi" fullname;
       printf "%s\n" dep_opt;
       flush stdout)
    (List.rev !mlAccu);
  List.iter
    (fun ((name,ext,dirname)) ->
       let fullname = file_name ([name],dirname) in
       let (dep,_) = traite_fichier_ML fullname ext in
       printf "%s.cmi: %s%s" fullname fullname ext;
       printf "%s\n" dep;
       flush stdout)
    (List.rev !mliAccu)

let coq_dependencies () =
  List.iter
    (fun (name,_) ->
       let glob = if !option_glob then " "^name^".glob" else "" in 
       printf "%s%s%s: %s.v" name !suffixe glob name;
       traite_fichier_Coq true (name ^ ".v");
       printf "\n";
       if !option_i then begin
	 printf "%s%s%s: %s.v" name !suffixe_spec glob name;
	 traite_fichier_Coq false (name ^ ".v");
	 printf "\n";
       end;
       flush stdout)
    (List.rev !vAccu)

let declare_dependencies () =
  List.iter
    (fun (name,_) ->
       traite_Declare (name^".v");      
       flush stdout)
    (List.rev !vAccu)

let rec warning_mult suf l = 
  let tab = Hashtbl.create 151 in
  List.iter 
    (fun (f,d) -> 
       begin try 
	 let d' = Hashtbl.find tab f in
	 if (Filename.dirname (file_name ([f],d)))
      	   <> (Filename.dirname (file_name ([f],d'))) then begin
	     eprintf "*** Warning : the file %s is defined twice!\n" (f ^ suf);
	     flush stderr
	   end
       with Not_found -> () end;
       Hashtbl.add tab f d) 
    l

(* Gives the list of all the directories under [dir], including [dir] *)
let all_subdirs root_dir log_dir =
  let l = ref [(root_dir,[log_dir])] in
  let add f = l := f :: !l in
  let rec traverse phys_dir dir =
    let dirh = handle_unix_error opendir phys_dir in
    try
      while true do
	let f = readdir dirh in
	if f <> "." && f <> ".." then
	  let file = dir@[f] in
          let filename = phys_dir//f in
	  if (stat filename).st_kind = S_DIR then begin
	    add (filename,file);
	    traverse filename file
	  end
      done
    with End_of_file ->
      closedir dirh
  in
  traverse root_dir [log_dir]; List.rev !l

let usage () =
  eprintf
  "[ usage: coqdep [-w] [-I dir] [-R dir coqdir] [-coqlib dir] [-c] [-i] [-D] <filename>+ ]\n";
  flush stderr;
  exit 1

let add_coqlib_known dir_name f =
  let complete_name = dir_name//f in
  let lib_name = Filename.basename dir_name in
  match try (stat complete_name).st_kind with _ -> S_BLK with 
    | S_REG -> 
	if Filename.check_suffix f ".vo" then
	  let basename = Filename.chop_suffix f ".vo" in
	  addQueue coqlibKnown ([basename],complete_name);
	  addQueue coqlibKnown (["Coq";lib_name;basename],complete_name)
    | _ -> ()

let add_coqlib_directory dir_name = 
  match try (stat dir_name).st_kind with _ -> S_BLK with 
    | S_DIR -> 
	(let dir = opendir dir_name in
      	 try
	   while true do add_coqlib_known dir_name (readdir dir) done
	 with End_of_file -> closedir dir)
    | _ -> ()

let coqdep () =
  let lg_command = Array.length Sys.argv in
  if lg_command < 2 then usage ();
  let rec treat old_dirname old_name =
    let name = Filename.basename old_name 
    and new_dirname = Filename.dirname old_name in
    let dirname = 
      match (old_dirname,new_dirname) with 
	| (d, ".") -> d
	| (None,d) -> Some d
	| (Some d1,d2) -> Some (d1//d2) 
    in
    let complete_name = file_name ([name],dirname) in
    match try (stat complete_name).st_kind with _ -> S_BLK with 
      | S_DIR ->
	  (if name <> "." & name <> ".." then
	     let dir=opendir complete_name in
             let newdirname = 
               match dirname with 
                 | None -> name
                 | Some d -> d//name 
	     in
	     try 
	       while true do treat (Some newdirname) (readdir dir) done
	     with End_of_file -> closedir dir)
      | S_REG -> 
	  if Filename.check_suffix name ".ml" then
	    let basename = Filename.chop_suffix name ".ml" in
	    addQueue mlAccu (basename,".ml",dirname)
	  else if Filename.check_suffix name ".ml4" then
	    let basename = Filename.chop_suffix name ".ml4" in
	    addQueue mlAccu (basename,".ml4",dirname)
	  else if Filename.check_suffix name ".mli" then
	    let basename = Filename.chop_suffix name ".mli" in
	    addQueue mliAccu (basename,".mli",dirname)
	  else if Filename.check_suffix name ".v" then
	    let basename = Filename.chop_suffix name ".v" in
	    let name = file_name ([basename],dirname) in
	    addQueue vAccu (name, absolute_file_name basename dirname)
      | _ -> ()
  in 
  let add_known phys_dir log_dir f =
    let complete_name = phys_dir//f in
    match try (stat complete_name).st_kind with _ -> S_BLK with 
	| S_REG ->
	    if Filename.check_suffix f ".ml" then
	      let basename = Filename.chop_suffix f ".ml" in
	      addQueue mlKnown (basename,Some phys_dir)
	    else if Filename.check_suffix f ".ml4" then
	      let basename = Filename.chop_suffix f ".ml4" in
	      addQueue mlKnown (basename,Some phys_dir)
	    else if Filename.check_suffix f ".mli" then
	      let basename = Filename.chop_suffix f ".mli" in
	      addQueue mliKnown (basename,Some phys_dir)
	    else if Filename.check_suffix f ".v" then
	      let basename = Filename.chop_suffix f ".v" in
              let name = log_dir@[basename] in
              let file = phys_dir//basename in
              let paths = [name;[basename]] in
	      List.iter
                (fun n -> safe_addQueue clash_v vKnown (n,file)) paths
        | _ -> () in
  let add_directory (phys_dir, log_dir) = 
      match try (stat phys_dir).st_kind with _ -> S_BLK with 
	| S_DIR -> 
	    (let dir = opendir phys_dir in
      	     try
	       while true do
                 add_known phys_dir log_dir (readdir dir) done
	     with End_of_file -> closedir dir)
        | _ -> ()
  in
  let add_rec_directory dir_name log_name =
    List.iter add_directory (all_subdirs dir_name log_name)
  in
  let rec parse = function
      | "-c" :: ll -> option_c := true; parse ll
      | "-D" :: ll -> option_D := true; parse ll
      | "-w" :: ll -> option_w := true; parse ll
      | "-i" :: ll -> option_i := true; parse ll
      | "-sort" :: ll -> option_sort := true; parse ll
      | "-glob" :: ll -> option_glob := true; parse ll
      | "-I" :: r :: ll -> add_directory (r, []); parse ll
      | "-I" :: [] -> usage ()
      | "-R" :: r :: ln :: ll -> add_rec_directory r ln; parse ll
      | "-R" :: ([] | [_]) -> usage ()
      | "-coqlib" :: (r :: ll) -> coqlib := r; parse ll
      | "-coqlib" :: [] -> usage ()
      | "-suffix" :: (s :: ll) -> suffixe := s ; suffixe_spec := s; parse ll
      | "-suffix" :: [] -> usage ()
      | "-slash" :: ll -> option_slash := true; parse ll
      | f :: ll -> treat None f; parse ll
      | [] -> ()
  in
(*  add_directory (".", []);*)
  parse (List.tl (Array.to_list Sys.argv));
  List.iter
    (fun (s,_) -> add_coqlib_directory s)
    (all_subdirs (!coqlib//"theories") "Coq");
  List.iter 
    (fun (s,_) -> add_coqlib_directory s)
    (all_subdirs (!coqlib//"contrib") "Coq");
  add_coqlib_directory (!coqlib//"user-contrib");
  mliKnown := !mliKnown @ (List.map (fun (f,_,d) -> (f,d)) !mliAccu);
  mlKnown  := !mlKnown @ (List.map (fun (f,_,d) -> (f,d)) !mlAccu);
  warning_mult ".mli" !mliKnown;
  warning_mult ".ml" !mlKnown;
(*  warning_mult ".v" (List.map (fun (s,d) -> (file_concat s, d))
  !vKnown);*)
  if !option_sort then begin sort (); exit 0 end;
  if !option_c && not !option_D then mL_dependencies ();
  if not !option_D then coq_dependencies ();
  if !option_w || !option_D then declare_dependencies ()

let _ = Printexc.catch coqdep ()
