(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Coqdep_lexer
open Unix

let stderr = Pervasives.stderr
let stdout = Pervasives.stdout

let option_c = ref false

let option_D = ref false

let option_w = ref false

let option_i = ref false

let suffixe = ref ".vo"
let suffixe_spec = ref ".vi"

let traite_fichier_ML md ext =
  try 
    let chan = open_in (md^ext) in 
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
	  deja_vu := str :: !deja_vu;
          begin try
            let mlidir = List.assoc str !mliKnown in
            let filename = file_name (str,mlidir) in
      	    a_faire := !a_faire ^ " " ^ filename ^ ".cmi"; 
          with Not_found ->
            try
              let mldir = List.assoc str !mlKnown in
              let filename = file_name (str,mldir) in
              a_faire := !a_faire ^ " " ^ filename ^ ".cmo";
            with Not_found -> ()
          end;
          begin try
            let mldir = List.assoc str !mlKnown in
            let filename = file_name (str,mldir) in
    	    a_faire_opt := !a_faire_opt ^ " " ^ filename ^ ".cmx"
          with Not_found ->
            try
              let mlidir = List.assoc str !mliKnown in
              let filename = file_name (str,mlidir) in
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

let warning_notfound f s =
  output_string stderr ("*** Warning : in file " ^ f ^ ", the file ");
  output_string stderr ( s ^ ".v is required and has not been found !\n");
  flush stderr

let traite_fichier_Coq f = 
  try 
    let chan = open_in f in 
    let buf = Lexing.from_channel chan in 
    let deja_vu_v = ref ([]: string list)
    and deja_vu_ml = ref ([] : string list) in
    try 
      while true do
      	let tok = coq_action buf in
	match tok with
	  | Require (spec,str) -> 
	      if not (List.mem str !deja_vu_v) then begin
	        deja_vu_v := str :: !deja_vu_v;
                try
                  let vdir = List.assoc str !vKnown in
                  print_string " ";
                  print_string (file_name (str,vdir));
                  print_string (if spec then !suffixe_spec else !suffixe)
                with Not_found -> 
                  begin 
		    try let _ = List.assoc str !coqlibKnown in ()
                    with Not_found -> warning_notfound f str end
       	      end
	  | RequireString (spec,s) -> 
	      let str = Filename.basename s in
	      if not (List.mem str !deja_vu_v) then begin
	        deja_vu_v := str :: !deja_vu_v;
                try
                  let vdir = List.assoc str !vKnown in
                  print_string " ";
                  print_string (file_name (str,vdir));
                  print_string (if spec then !suffixe_spec else !suffixe)
                with Not_found -> 
                  begin try  let _ = List.assoc s !coqlibKnown in ()
                  with Not_found -> warning_notfound f s end
       	      end
	  | Declare sl -> 
	      List.iter 
		(fun str ->
		   if not (List.mem str !deja_vu_ml) then begin
		     deja_vu_ml := str :: !deja_vu_ml;
               	     try
              	       let mldir = List.assoc str !mlKnown in
              	       print_string " ";
                       print_string (file_name (str,mldir));
              	       print_string ".cmo"
              	     with Not_found -> () 
		   end)
		sl
      done
    with Fin_fichier -> ();
      close_in chan
  with Sys_error _ -> () 

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
	    output_string stderr ("*** Warning : in file "^f^" the");
	    output_string stderr (" notation "^b^"__ is useless !\n");
	    flush stderr
	  end else if List.mem str !deja_vu then 
	    ()
	  else 
	    deja_vu := str :: !deja_vu
      	done; []
      with Fin_fichier -> begin
	close_in chan; 
	let rl = List.rev !deja_vu in
      	Hashtbl.add dep_tab f rl;
	rl
      end
    with Sys_error _ -> []

let affiche_Declare f dcl = 
  print_newline ();
  print_string ("*** In file "^f^" : ");
  print_newline ();
  print_string "Declare ML Module";
  List.iter (fun str -> print_string " ";
	       print_char '"'; print_string str;
	       print_char '"') dcl;
  print_string ".";
  print_newline();
  flush stdout

let warning_Declare f dcl =
  output_string stderr ("*** Warning : in file "^f^", the ML modules");
  output_string stderr " declaration should be\n";
  output_string stderr "*** Declare ML Module";
  List.iter (fun str -> output_string stderr " ";
	       output_char stderr '"'; output_string stderr str;
	       output_char stderr '"') dcl;
  output_string stderr ".\n";
  flush stderr

let traite_Declare f = 
  let decl_list = ref ([] : string list) in
  let rec treat = function
    | s::ll -> 
	if (List.mem_assoc s !mlKnown) & not (List.mem s !decl_list) then begin
       	  let mldir = List.assoc s !mlKnown in
	  let fullname = file_name (s,mldir) in
	  let depl = mL_dep_list s (fullname^".ml") in
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
    | (f1,_,d1) :: l -> if f1 = f && d1 = d then true else loop l
    | _ -> false
  in 
  loop

let mL_dependencies () =
  List.iter 
    (fun ((name,ext,dirname) as pairname) ->
       let fullname = file_name (name,dirname) in
       let (dep,dep_opt) = traite_fichier_ML fullname ext in
       print_string fullname; print_string ".cmo: "; 
       print_string fullname; print_string ext;
       if file_mem pairname !mliAccu then begin
	 print_string " "; print_string fullname; print_string ".cmi"
       end;
       print_string dep;
       print_newline ();
       print_string fullname; print_string ".cmx: "; 
       print_string fullname; print_string ext;
       if file_mem pairname !mliAccu then begin
	 print_string " "; print_string fullname; print_string ".cmi"
       end;
       print_string dep_opt;
       print_newline ();
       flush stdout)
    !mlAccu;
  List.iter
    (fun ((name,ext,dirname) as pairname) ->
       let fullname = file_name (name,dirname) in
       let (dep,_) = traite_fichier_ML fullname ext in
       print_string fullname; print_string ".cmi: "; 
       print_string fullname;print_string ext;
       print_string dep;
       print_newline ();
       flush stdout)
    !mliAccu

let coq_dependencies () =
  List.iter
    (fun ((name,dirname) as pairname) ->
       let fullname = file_name pairname in
       Printf.printf "%s%s: %s.v" fullname !suffixe fullname;
       traite_fichier_Coq (fullname^".v");
       print_newline ();
       if !option_i then begin
	 Printf.printf "%s%s: %s.v" fullname !suffixe_spec fullname;
	 traite_fichier_Coq (fullname^".v");
	 print_newline ();
       end;
       flush stdout)
    !vAccu

let declare_dependencies () =
  List.iter
    (fun ((name,dirname) as pairname) ->
       let fullname = file_name pairname in
       traite_Declare (fullname^".v");      
       flush stdout)
    !vAccu

let rec warning_mult suf l = 
  let tab = Hashtbl.create 151 in
  List.iter 
    (fun (f,d) -> 
       begin try 
	 let d' = Hashtbl.find tab f in
	 if (Filename.dirname (file_name (f,d)))
      	   <> (Filename.dirname (file_name (f,d'))) then begin
	     output_string stderr "*** Warning : the file ";
	     output_string stderr (f ^ suf);
	     output_string stderr " is defined twice !\n";
	     flush stderr
	   end
       with Not_found -> () end;
       Hashtbl.add tab f d) 
    l

let usage () =
  print_string 
  "[ usage: coqdep [-w] [-I dir] [-coqlib dir] [-c] [-i] [-D] <filename>+ ]\n";
  flush stdout;
  exit 1

let add_coqlib_known dir_name f =
  let complete_name = Filename.concat dir_name f in
  match try (stat complete_name).st_kind with _ -> S_BLK with 
    | S_REG -> 
	if Filename.check_suffix f ".vo" then
	  let basename = Filename.chop_suffix f ".vo" in
	  addQueue coqlibKnown (basename,Some dir_name)
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
	| (Some d1,d2) -> Some (Filename.concat d1 d2) 
    in
    let complete_name = file_name (name,dirname) in
    match try (stat (file_name (name,dirname))).st_kind with _ -> S_BLK with 
      | S_DIR ->
	  (if name <> "." & name <> ".." then
	     let dir=opendir complete_name in
             let newdirname = 
               match dirname with 
                 | None -> name
                 | Some d -> Filename.concat d name 
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
	    addQueue vAccu (basename,dirname)
      | _ -> ()
    in 
    let add_known dir_name f =
      let complete_name = Filename.concat dir_name f in
      match try (stat complete_name).st_kind with _ -> S_BLK with 
	| S_REG ->
	    if Filename.check_suffix f ".ml" then
	      let basename = Filename.chop_suffix f ".ml" in
	      addQueue mlKnown (basename,Some dir_name)
	    else if Filename.check_suffix f ".ml4" then
	      let basename = Filename.chop_suffix f ".ml4" in
	      addQueue mlKnown (basename,Some dir_name)
	    else if Filename.check_suffix f ".mli" then
	      let basename = Filename.chop_suffix f ".mli" in
	      addQueue mliKnown (basename,Some dir_name)
	    else if Filename.check_suffix f ".v" then
	      let basename = Filename.chop_suffix f ".v" in
	      addQueue vKnown (basename,Some dir_name)
        | _ -> ()
    in
    let add_directory dir_name = 
      match try (stat dir_name).st_kind with _ -> S_BLK with 
	| S_DIR -> 
	    (let dir = opendir dir_name in
      	     try
	       while true do add_known dir_name (readdir dir) done
	     with End_of_file -> closedir dir)
        | _ -> ()
    in
    let rec parse = function
      | "-c" :: ll -> option_c := true; parse ll
      | "-D" :: ll -> option_D := true; parse ll
      | "-w" :: ll -> option_w := true; parse ll
      | "-i" :: ll -> option_i := true; parse ll
      | "-I" :: (r :: ll) -> add_directory r; parse ll
      | "-I" :: [] -> usage ()
      | "-coqlib" :: (r :: ll) -> coqlib := r; parse ll
      | "-coqlib" :: [] -> usage ()
      | "-suffix" :: (s :: ll) -> suffixe := s ; suffixe_spec := s; parse ll
      | "-suffix" :: [] -> usage ()
      | f :: ll -> treat None f; parse ll
      | [] -> ()
    in
    parse (List.tl (Array.to_list Sys.argv));
    let theories = Filename.concat !coqlib "theories" in
    List.iter
      (fun s -> add_coqlib_directory (Filename.concat theories s))
      Coq_config.theories_dirs;
    let tactics = Filename.concat !coqlib "tactics" in
    add_coqlib_directory tactics;
    let contrib = Filename.concat !coqlib "contrib" in
    List.iter 
      (fun s -> add_coqlib_directory (Filename.concat contrib s))
      Coq_config.contrib_dirs;
    mliKnown := !mliKnown @ (List.map (fun (f,_,d) -> (f,d)) !mliAccu);
    mlKnown  := !mlKnown @ (List.map (fun (f,_,d) -> (f,d)) !mlAccu);
    vKnown   := !vKnown @ !vAccu;
    warning_mult ".mli" !mliKnown;
    warning_mult ".ml" !mlKnown;
    warning_mult ".v" !vKnown;
    if !option_c & not !option_D then mL_dependencies ();
    if not !option_D then coq_dependencies ();
    if !option_w or !option_D then declare_dependencies ()
      
let _ = Printexc.catch coqdep ()

