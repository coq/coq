(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Printf
open Coqdep_lexer
open Unix

(** [coqdep_boot] is a stripped-down version of [coqdep], whose
    behavior is the one of [coqdep -boot]. Its only dependencies
    are [Coqdep_lexer] and [Unix], and it should stay so.
    If it need someday some additional information, pass it via
    options (see for instance [option_natdynlk] below).
*)

let stderr = Pervasives.stderr
let stdout = Pervasives.stdout

let option_c = ref false
let option_noglob = ref false
let option_natdynlk = ref true
let option_boot = ref false
let option_mldep = ref None

let norec_dirs = ref ([] : string list)
let norec_dirnames = ref ["CVS"; "_darcs"]

let suffixe = ref ".vo"

type dir = string option

(* Filename.concat but always with a '/' *)
let is_dir_sep s i =
  match Sys.os_type with
  | "Unix" -> s.[i] = '/'
  | "Cygwin" | "Win32" ->
    let c = s.[i] in c = '/' || c = '\\' || c = ':'
  | _ -> assert false

let (//) dirname filename =
  let l = String.length dirname in
  if l = 0 || is_dir_sep dirname (l-1)
  then dirname ^ filename
  else dirname ^ "/" ^ filename

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
  try Filename.chop_extension fn with Invalid_argument _ -> fn

(** ML Files specified on the command line. In the entries:
    - the first string is the basename of the file, without extension nor
      directory part
    - the second string of [mlAccu] is the extension (either .ml or .ml4)
    - the [dir] part is the directory, with None used as the current directory
*)

let mlAccu  = ref ([] : (string * string * dir) list)
and mliAccu = ref ([] : (string * dir) list)
and mllibAccu = ref ([] : (string * dir) list)
and mlpackAccu = ref ([] : (string * dir) list)

(** Coq files specifies on the command line:
    - first string is the full filename, with only its extension removed
    - second string is the absolute version of the previous (via getcwd)
*)

let vAccu   = ref ([] : (string * string) list)

(** Queue operations *)

let addQueue q v = q := v :: !q

let safe_hash_add cmp clq q (k,v) =
  try
    let v2 = Hashtbl.find q k in
    if not (cmp v v2) then
      let rec add_clash = function
          (k1,l1)::cltl when k=k1 -> (k1,v::l1)::cltl
        | cl::cltl -> cl::add_clash cltl
        | [] -> [(k,[v;v2])] in
      clq := add_clash !clq;
      (* overwrite previous bindings, as coqc does *)
      Hashtbl.add q k v
  with Not_found -> Hashtbl.add q k v

(** Files found in the loadpaths.
    For the ML files, the string is the basename without extension.
*)

let warning_ml_clash x s suff s' suff' =
  if suff = suff' then
  eprintf
    "*** Warning: %s%s already found in %s (discarding %s%s)\n" x suff
    (match s with None -> "." | Some d -> d)
    ((match s' with None -> "." | Some d -> d) // x) suff

let mkknown () =
  let h = (Hashtbl.create 19 : (string, dir * string) Hashtbl.t) in
  let add x s suff =
    try let s',suff' = Hashtbl.find h x in warning_ml_clash x s' suff' s suff
    with Not_found -> Hashtbl.add h x (s,suff)
  and iter f = Hashtbl.iter (fun x (s,_) -> f x s) h
  and search x =
    try Some (fst (Hashtbl.find h x))
    with Not_found -> None
  in add, iter, search

let add_ml_known, iter_ml_known, search_ml_known = mkknown ()
let add_mli_known, iter_mli_known, search_mli_known = mkknown ()
let add_mllib_known, _, search_mllib_known = mkknown ()
let add_mlpack_known, _, search_mlpack_known = mkknown ()

let vKnown = (Hashtbl.create 19 : (string list, string) Hashtbl.t)
let coqlibKnown = (Hashtbl.create 19 : (string list, unit) Hashtbl.t)

let clash_v = ref ([]: (string list * string list) list)

let error_cannot_parse s (i,j) =
  Printf.eprintf "File \"%s\", characters %i-%i: Syntax error\n" s i j;
  exit 1

let warning_module_notfound f s =
  eprintf "*** Warning: in file %s, library " f;
  eprintf "%s.v is required and has not been found in the loadpath!\n"
    (String.concat "." s);
  flush stderr

let warning_notfound f s =
  eprintf "*** Warning: in file %s, the file " f;
  eprintf "%s.v is required and has not been found!\n" s;
  flush stderr

let warning_declare f s =
  eprintf "*** Warning: in file %s, declared ML module " f;
  eprintf "%s has not been found!\n" s;
  flush stderr

let warning_clash file dir =
  match List.assoc dir !clash_v with
    (f1::f2::fl) ->
      let f = Filename.basename f1 in
      let d1 = Filename.dirname f1 in
      let d2 = Filename.dirname f2 in
      let dl = List.rev_map Filename.dirname fl in
      eprintf
        "*** Warning: in file %s, \n    required library %s matches several files in path\n    (found %s.v in "
        file (String.concat "." dir) f;
      List.iter (fun s -> eprintf "%s, " s) dl;
      eprintf "%s and %s; used the latter)\n" d2 d1
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

let soustraite_fichier_ML dep md ext =
  try
    let chan = open_process_in (dep^" -modules "^md^ext) in
    let list = ocamldep_parse (Lexing.from_channel chan) in
    let a_faire = ref "" in
    let a_faire_opt = ref "" in
    List.iter
      (fun str ->
	 let byte,opt = depend_ML str in
	 a_faire := !a_faire ^ byte;
	 a_faire_opt := !a_faire_opt ^ opt)
      (List.rev list);
    (!a_faire, !a_faire_opt)
  with
    | Sys_error _ -> ("","")
    | _ ->
       Printf.eprintf "Coqdep: subprocess %s failed on file %s%s\n" dep md ext;
       exit 1

let autotraite_fichier_ML md ext =
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

let traite_fichier_ML md ext =
  match !option_mldep with
    | Some dep -> soustraite_fichier_ML dep md ext
    | None -> autotraite_fichier_ML md ext

let traite_fichier_modules md ext =
  try
    let chan = open_in (md ^ ext) in
    let list = mllib_list (Lexing.from_channel chan) in
    List.fold_left
      (fun a_faire str -> match search_mlpack_known str with
	| Some mldir ->
	  let file = file_name str mldir in
	  a_faire^" "^file
	| None ->
	  match search_ml_known str with
	    | Some mldir ->
	      let file = file_name str mldir in
	      a_faire^" "^file
	    | None -> a_faire) "" list
  with
    | Sys_error _ -> ""
    | Syntax_error (i,j) -> error_cannot_parse (md^ext) (i,j)

(* Makefile's escaping rules are awful: $ is escaped by doubling and
   other special characters are escaped by backslash prefixing while
   backslashes themselves must be escaped only if part of a sequence
   followed by a special character (i.e. in case of ambiguity with a
   use of it as escaping character).  Moreover (even if not crucial)
   it is apparently not possible to directly escape ';' and leading '\t'. *)

let escape =
  let s' = Buffer.create 10 in
  fun s ->
    Buffer.clear s';
    for i = 0 to String.length s - 1 do
      let c = s.[i] in
      if c = ' ' || c = '#' || c = ':' (* separators and comments *)
        || c = '%' (* pattern *)
	|| c = '?' || c = '[' || c = ']' || c = '*' (* expansion in filenames *)
	|| i=0 && c = '~' && (String.length s = 1 || s.[1] = '/' || 
	    'A' <= s.[1] && s.[1] <= 'Z' || 
	    'a' <= s.[1] && s.[1] <= 'z') (* homedir expansion *)
      then begin
	let j = ref (i-1) in
	while !j >= 0 && s.[!j] = '\\' do 
	  Buffer.add_char s' '\\'; decr j (* escape all preceding '\' *)
	done;
	Buffer.add_char s' '\\';
      end;
      if c = '$' then Buffer.add_char s' '$';
      Buffer.add_char s' c
    done;
    Buffer.contents s'

let compare_file f1 f2 =
  absolute_dir (Filename.dirname f1) = absolute_dir (Filename.dirname f2)

let canonize f =
  let f' = absolute_dir (Filename.dirname f) // Filename.basename f in
  match List.filter (fun (_,full) -> f' = full) !vAccu with
    | (f,_) :: _ -> escape f
    | _ -> escape f

let rec traite_fichier_Coq suffixe verbose f =
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
                    printf " %s%s" (canonize file_str) suffixe
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
                  printf " %s%s" (canonize file_str) suffixe
                with Not_found ->
		  if not (Hashtbl.mem coqlibKnown [str]) then
		    warning_notfound f s
       	      end
	  | Declare sl ->
	      let declare suff dir s =
		let base = file_name s dir in
		let opt = if !option_natdynlk then " "^base^".cmxs" else "" in
		printf " %s%s%s" (escape base) suff opt
	      in
	      let decl str =
                let s = basename_noext str in
		if not (List.mem s !deja_vu_ml) then begin
		  addQueue deja_vu_ml s;
		  match search_mllib_known s with
		    | Some mldir -> declare ".cma" mldir s
		    | None ->
		      match search_mlpack_known s with
			| Some mldir -> declare ".cmo" mldir s
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
                  let canon = canonize file_str in
                  printf " %s.v" canon;
                  traite_fichier_Coq suffixe true (canon ^ ".v")
                with Not_found -> ()
       	      end
          | AddLoadPath _ | AddRecLoadPath _ -> (* TODO *) ()
      done
    with Fin_fichier -> close_in chan
       | Syntax_error (i,j) -> close_in chan; error_cannot_parse f (i,j)
  with Sys_error _ -> ()


let mL_dependencies () =
  List.iter
    (fun (name,ext,dirname) ->
       let fullname = file_name name dirname in
       let (dep,dep_opt) = traite_fichier_ML fullname ext in
       let intf = match search_mli_known name with
	 | None -> ""
	 | Some mldir -> " "^(file_name name mldir)^".cmi"
       in
       let efullname = escape fullname in
       printf "%s.cmo:%s%s\n" efullname dep intf;
       printf "%s.cmx:%s%s\n" efullname dep_opt intf;
       flush stdout)
    (List.rev !mlAccu);
  List.iter
    (fun (name,dirname) ->
       let fullname = file_name name dirname in
       let (dep,_) = traite_fichier_ML fullname ".mli" in
       printf "%s.cmi:%s\n" (escape fullname) dep;
       flush stdout)
    (List.rev !mliAccu);
  List.iter
    (fun (name,dirname) ->
       let fullname = file_name name dirname in
       let dep = traite_fichier_modules fullname ".mllib" in
       let efullname = escape fullname in
       printf "%s_MLLIB_DEPENDENCIES:=%s\n" efullname dep;
       printf "%s.cma:$(addsuffix .cmo,$(%s_MLLIB_DEPENDENCIES))\n" efullname efullname;
       printf "%s.cmxa %s.cmxs:$(addsuffix .cmx,$(%s_MLLIB_DEPENDENCIES))\n" efullname efullname efullname;
       flush stdout)
    (List.rev !mllibAccu);
  List.iter
    (fun (name,dirname) ->
       let fullname = file_name name dirname in
       let dep = traite_fichier_modules fullname ".mlpack" in
       let efullname = escape fullname in
       printf "%s_MLPACK_DEPENDENCIES:=%s\n" efullname dep;
       printf "%s.cmo:$(addsuffix .cmo,$(%s_MLPACK_DEPENDENCIES))\n" efullname efullname;
       printf "%s.cmx %s.cmxs:$(addsuffix .cmx,$(%s_MLPACK_DEPENDENCIES))\n" efullname efullname efullname;
       flush stdout)
    (List.rev !mlpackAccu)

let coq_dependencies () =
  List.iter
    (fun (name,_) ->
       let ename = escape name in
       let glob = if !option_noglob then "" else " "^ename^".glob" in
       printf "%s%s%s %s.v.beautified: %s.v" ename !suffixe glob ename ename;
       traite_fichier_Coq !suffixe true (name ^ ".v");
       printf "\n";
       printf "%s.vio: %s.v" ename ename;
       traite_fichier_Coq ".vio" true (name ^ ".v");
       printf "\n";
       flush stdout)
    (List.rev !vAccu)

let rec suffixes = function
  | [] -> assert false
  | [name] -> [[name]]
  | dir::suffix as l -> l::suffixes suffix

let add_caml_known phys_dir _ f =
  let basename,suff =
    get_extension f [".ml";".mli";".ml4";".mllib";".mlpack"] in
  match suff with
    | ".ml"|".ml4" -> add_ml_known basename (Some phys_dir) suff
    | ".mli" -> add_mli_known basename (Some phys_dir) suff
    | ".mllib" -> add_mllib_known basename (Some phys_dir) suff
    | ".mlpack" -> add_mlpack_known basename (Some phys_dir) suff
    | _ -> ()

let add_known recur phys_dir log_dir f =
  match get_extension f [".v";".vo"] with
    | (basename,".v") ->
	let name = log_dir@[basename] in
	let file = phys_dir//basename in
	let paths = if recur then suffixes name else [name] in
	List.iter
	  (fun n -> safe_hash_add compare_file clash_v vKnown (n,file)) paths
    | (basename,".vo") when not(!option_boot) ->
        let name = log_dir@[basename] in
	let paths = if recur then suffixes name else [name] in
        List.iter (fun f -> Hashtbl.add coqlibKnown f ()) paths
    | _ -> ()

(* Visits all the directories under [dir], including [dir],
   or just [dir] if [recur=false] *)

let rec add_directory recur add_file phys_dir log_dir =
  let dirh = opendir phys_dir in
  try
    while true do
      let f = readdir dirh in
      (* we avoid all files and subdirs starting by '.' (e.g. .svn),
         plus CVS and _darcs and any subdirs given via -exclude-dirs *)
      if f.[0] <> '.' then
        let phys_f = if phys_dir = "." then f else phys_dir//f in
	match try (stat phys_f).st_kind with _ -> S_BLK with
	  | S_DIR when recur ->
              if List.mem f !norec_dirnames then ()
              else
	        if List.mem phys_f !norec_dirs then ()
	        else
		  add_directory recur add_file phys_f (log_dir@[f])
	  | S_REG -> add_file phys_dir log_dir f
	  | _ -> ()
    done
  with End_of_file -> closedir dirh

(** -Q semantic: go in subdirs but only full logical paths are known. *)
let add_dir add_file phys_dir log_dir =
  try add_directory true (add_file false) phys_dir log_dir with Unix_error _ -> ()

(** -R semantic: go in subdirs and suffixes of logical paths are known. *)
let add_rec_dir add_file phys_dir log_dir =
  handle_unix_error (add_directory true (add_file true) phys_dir) log_dir

(** -I semantic: do not go in subdirs. *)
let add_caml_dir phys_dir =
  handle_unix_error (add_directory true add_caml_known phys_dir) []


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
	(match get_extension name [".v";".ml";".mli";".ml4";".mllib";".mlpack"] with
	   | (base,".v") ->
	       let name = file_name base dirname
	       and absname = absolute_file_name base dirname in
	       addQueue vAccu (name, absname)
	   | (base,(".ml"|".ml4" as ext)) -> addQueue mlAccu (base,ext,dirname)
	   | (base,".mli") -> addQueue mliAccu (base,dirname)
	   | (base,".mllib") -> addQueue mllibAccu (base,dirname)
	   | (base,".mlpack") -> addQueue mlpackAccu (base,dirname)
	   | _ -> ())
    | _ -> ()
