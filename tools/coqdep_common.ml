(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Format
open Unix
open Coqdep_lexer
open Minisys

(** [coqdep_boot] is a stripped-down version of [coqdep], whose
    behavior is the one of [coqdep -boot]. Its only dependencies
    are [Coqdep_lexer], [Unix] and [Minisys], and it should stay so.
    If it need someday some additional information, pass it via
    options (see for instance [option_dynlink] below).
*)

let coqdep_warning args =
  eprintf "*** Warning: @[";
  kfprintf (fun fmt -> fprintf fmt "@]\n%!") err_formatter args

module StrSet = Set.Make(String)

module StrList = struct type t = string list let compare = compare end
module StrListMap = Map.Make(StrList)

type dynlink = Opt | Byte | Both | No | Variable

let option_c = ref false
let option_noglob = ref false
let option_dynlink = ref Both
let option_boot = ref false
let option_mldep = ref None

let norec_dirs = ref StrSet.empty

let suffixe = ref ".vo"

[@@@ocaml.warning "-3"]       (* String.capitalize_ascii since 4.03.0 GPR#124 *)
let capitalize = String.capitalize
[@@@ocaml.warning "+3"]

type dir = string option

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

let safe_hash_add cmp clq q (k, (v, b)) =
  try
    let (v2, _) = Hashtbl.find q k in
    if not (cmp v v2) then
      let nv =
        try v :: StrListMap.find k !clq
        with Not_found -> [v; v2]
      in
      clq := StrListMap.add k nv !clq;
      (* overwrite previous bindings, as coqc does *)
      Hashtbl.add q k (v, b)
  with Not_found -> Hashtbl.add q k (v, b)

(** Files found in the loadpaths.
    For the ML files, the string is the basename without extension.
*)

let same_path_opt s s' =
  let nf s = (* ./foo/a.ml and foo/a.ml are the same file *)
    if Filename.is_implicit s
    then "." // s
    else s
  in
  let s = match s with None -> "." | Some s -> nf s in
  let s' = match s' with None -> "." | Some s' -> nf s' in
  s = s'

let warning_ml_clash x s suff s' suff' =
  if suff = suff' && not (same_path_opt s s') then
  coqdep_warning "%s%s already found in %s (discarding %s%s)\n" x suff
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

let vKnown = (Hashtbl.create 19 : (string list, string * bool) Hashtbl.t)
(** The associated boolean is true if this is a root path. *)
let coqlibKnown = (Hashtbl.create 19 : (string list, unit) Hashtbl.t)

let get_prefix p l =
  let rec drop_prefix_rec = function
    | (h1::tp, h2::tl) when h1 = h2 -> drop_prefix_rec (tp,tl)
    | ([], tl) -> Some tl
    | _ -> None
  in
  drop_prefix_rec (p, l)

let search_table (type r) is_root table ?from s = match from with
| None -> Hashtbl.find table s
| Some from ->
  let module M = struct exception Found of r end in
  let iter logpath binding =
    if is_root binding then match get_prefix from logpath with
    | None -> ()
    | Some rem ->
      match get_prefix (List.rev s) (List.rev rem) with
      | None -> ()
      | Some _ -> raise (M.Found binding)
  in
  try Hashtbl.iter iter table; raise Not_found
  with M.Found s -> s

let search_v_known ?from s =
  let is_root (_, root) = root in
  try
    let (phys_dir, _) = search_table is_root vKnown ?from s in
    Some phys_dir
  with Not_found -> None

let is_in_coqlib ?from s =
  let is_root _ = true in
  try search_table is_root coqlibKnown ?from s; true with Not_found -> false

let clash_v = ref (StrListMap.empty : string list StrListMap.t)

let error_cannot_parse s (i,j) =
  Printf.eprintf "File \"%s\", characters %i-%i: Syntax error\n" s i j;
  exit 1

let warning_module_notfound f s =
  coqdep_warning "in file %s, library %s is required and has not been found in the loadpath!"
    f (String.concat "." s)

let warning_declare f s =
  coqdep_warning "in file %s, declared ML module %s has not been found!" f s

let warning_clash file dir =
  match StrListMap.find dir !clash_v with
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

let warning_cannot_open_dir dir =
  coqdep_warning "cannot open %s" dir

let safe_assoc from verbose file k =
  if verbose && StrListMap.mem k !clash_v then warning_clash file k;
  match search_v_known ?from k with
  | None -> raise Not_found
  | Some path -> path

let absolute_dir dir =
  let current = Sys.getcwd () in
    Sys.chdir dir;
    let dir' = Sys.getcwd () in
      Sys.chdir current;
      dir'

let absolute_file_name basename odir =
  let dir = match odir with Some dir -> dir | None -> "." in
  absolute_dir dir // basename

(** [find_dir_logpath dir] Return the logical path of directory [dir]
    if it has been given one. Raise [Not_found] otherwise. In
    particular we can check if "." has been attributed a logical path
    after processing all options and silently give the default one if
    it hasn't. We may also use this to warn if ap hysical path is met
    twice.*)
let register_dir_logpath,find_dir_logpath =
  let tbl: (string, string list) Hashtbl.t = Hashtbl.create 19 in
  let reg physdir logpath = Hashtbl.add tbl (absolute_dir physdir) logpath in
  let fnd physdir = Hashtbl.find tbl (absolute_dir physdir) in
  reg,fnd

let file_name s = function
  | None     -> s
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
    let deja_vu = ref (StrSet.singleton md) in
    let a_faire = ref "" in
    let a_faire_opt = ref "" in
    begin try
      while true do
	let (Use_module str) = caml_action buf in
	if StrSet.mem str !deja_vu then
	  ()
	else begin
	  deja_vu := StrSet.add str !deja_vu;
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
          a_faire @ [file]
	| None ->
	  match search_ml_known str with
	    | Some mldir ->
	      let file = file_name str mldir in
              a_faire @ [file]
            | None -> a_faire) [] list
  with
    | Sys_error _ -> []
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
  absolute_file_name (Filename.basename f1) (Some (Filename.dirname f1))
  = absolute_file_name (Filename.basename f2) (Some (Filename.dirname f2))

let canonize f =
  let f' = absolute_dir (Filename.dirname f) // Filename.basename f in
  match List.filter (fun (_,full) -> f' = full) !vAccu with
    | (f,_) :: _ -> escape f
    | _ -> escape f

module VData = struct
  type t = string list option * string list
  let compare = Pervasives.compare
end

module VCache = Set.Make(VData)

let rec traite_fichier_Coq suffixe verbose f =
  try
    let chan = open_in f in
    let buf = Lexing.from_channel chan in
    let deja_vu_v = ref VCache.empty in
    let deja_vu_ml = ref StrSet.empty in
    try
      while true do
      	let tok = coq_action buf in
	match tok with
	  | Require (from, strl) ->
	      List.iter (fun str ->
		if not (VCache.mem (from, str) !deja_vu_v) then begin
	          deja_vu_v := VCache.add (from, str) !deja_vu_v;
                  try
                    let file_str = safe_assoc from verbose f str in
                    printf " %s%s" (canonize file_str) suffixe
                  with Not_found ->
		    if verbose && not (is_in_coqlib ?from str) then
		      let str =
			match from with
			  | None -> str
			  | Some pth -> pth @ str
		      in
                      warning_module_notfound f str
       		end) strl
	  | Declare sl ->
	      let declare suff dir s =
		let base = escape (file_name s dir) in
                match !option_dynlink with
                | No -> ()
                | Byte -> printf " %s%s" base suff
                | Opt -> printf " %s.cmxs" base
                | Both -> printf " %s%s %s.cmxs" base suff base
                | Variable ->
                   printf " %s%s" base
                    (if suff=".cmo" then "$(DYNOBJ)" else "$(DYNLIB)")
              in
	      let decl str =
                let s = basename_noext str in
		if not (StrSet.mem s !deja_vu_ml) then begin
		  deja_vu_ml := StrSet.add s !deja_vu_ml;
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
	      if not (VCache.mem (None, [str]) !deja_vu_v) then begin
	        deja_vu_v := VCache.add (None, [str]) !deja_vu_v;
                try
                  let (file_str, _) = Hashtbl.find vKnown [str] in
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
       printf "%s.cmx:%s%s\n%!" efullname dep_opt intf)
    (List.rev !mlAccu);
  List.iter
    (fun (name,dirname) ->
       let fullname = file_name name dirname in
       let (dep,_) = traite_fichier_ML fullname ".mli" in
       printf "%s.cmi:%s\n%!" (escape fullname) dep)
    (List.rev !mliAccu);
  List.iter
    (fun (name,dirname) ->
       let fullname = file_name name dirname in
       let dep = traite_fichier_modules fullname ".mllib" in
       let efullname = escape fullname in
       printf "%s_MLLIB_DEPENDENCIES:=%s\n" efullname (String.concat " " dep);
       printf "%s.cma:$(addsuffix .cmo,$(%s_MLLIB_DEPENDENCIES))\n" efullname efullname;
       printf "%s.cmxa:$(addsuffix .cmx,$(%s_MLLIB_DEPENDENCIES))\n%!" efullname efullname)
    (List.rev !mllibAccu);
  List.iter
    (fun (name,dirname) ->
       let fullname = file_name name dirname in
       let dep = traite_fichier_modules fullname ".mlpack" in
       let efullname = escape fullname in
       printf "%s_MLPACK_DEPENDENCIES:=%s\n" efullname (String.concat " " dep);
       printf "%s.cmo:$(addsuffix .cmo,$(%s_MLPACK_DEPENDENCIES))\n" efullname efullname;
       printf "%s.cmx:$(addsuffix .cmx,$(%s_MLPACK_DEPENDENCIES))\n" efullname efullname;
       let efullname_capital = capitalize (Filename.basename efullname) in
       List.iter (fun dep ->
         printf "%s.cmx : FOR_PACK=-for-pack %s\n" dep efullname_capital)
         dep;
       printf "%!")
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
       printf "\n%!")
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

let add_coqlib_known recur phys_dir log_dir f =
  match get_extension f [".vo"; ".vio"] with
    | (basename, (".vo" | ".vio")) ->
        let name = log_dir@[basename] in
        let paths = if recur then suffixes name else [name] in
        List.iter (fun f -> Hashtbl.add coqlibKnown f ()) paths
    | _ -> ()

let add_known recur phys_dir log_dir f =
  match get_extension f [".v"; ".vo"; ".vio"] with
    | (basename,".v") ->
	let name = log_dir@[basename] in
	let file = phys_dir//basename in
	let () = safe_hash_add compare_file clash_v vKnown (name, (file, true)) in
	if recur then
          let paths = List.tl (suffixes name) in
          let iter n = safe_hash_add compare_file clash_v vKnown (n, (file, false)) in
          List.iter iter paths
    | (basename, (".vo" | ".vio")) when not(!option_boot) ->
        let name = log_dir@[basename] in
	let paths = if recur then suffixes name else [name] in
        List.iter (fun f -> Hashtbl.add coqlibKnown f ()) paths
    | _ -> ()

(* Visits all the directories under [dir], including [dir] *)

let is_not_seen_directory phys_f =
  not (StrSet.mem phys_f !norec_dirs)

let rec add_directory recur add_file phys_dir log_dir =
  register_dir_logpath phys_dir log_dir;
  let f = function
    | FileDir (phys_f,f) ->
        if is_not_seen_directory phys_f && recur then
          add_directory true add_file phys_f (log_dir @ [f])
    | FileRegular f ->
        add_file phys_dir log_dir f
  in
  if exists_dir phys_dir then
    process_directory f phys_dir
  else
    warning_cannot_open_dir phys_dir

(** Simply add this directory and imports it, no subdirs. This is used
    by the implicit adding of the current path (which is not recursive). *)
let add_norec_dir_import add_file phys_dir log_dir =
  try add_directory false (add_file true) phys_dir log_dir with Unix_error _ -> ()

(** -Q semantic: go in subdirs but only full logical paths are known. *)
let add_rec_dir_no_import add_file phys_dir log_dir =
  try add_directory true (add_file false) phys_dir log_dir with Unix_error _ -> ()

(** -R semantic: go in subdirs and suffixes of logical paths are known. *)
let add_rec_dir_import add_file phys_dir log_dir =
  add_directory true (add_file true) phys_dir log_dir

(** -I semantic: do not go in subdirs. *)
let add_caml_dir phys_dir =
  add_directory false add_caml_known phys_dir []

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
           let newdirname =
             match dirname with
               | None -> name
               | Some d -> d//name
	   in
           Array.iter (treat_file (Some newdirname)) (Sys.readdir complete_name))
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
