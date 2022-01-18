(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Format
open Unix
open Coqdep_lexer
(* The whole Minisys module used to be required due to bootstrapping,
   thanks to dune it is not needed anymore and we could just remove it. *)
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

type dynlink = Opt | Byte | Both | No | Variable

let option_noglob = ref false
let option_dynlink = ref Both
let option_boot = ref false

type dir = string option

(** [get_extension f l] checks whether [f] has one of the extensions
    listed in [l]. It returns [f] without its extension, alongside with
    the extension. When no extension match, [(f,"")] is returned *)

let rec get_extension f = function
  | [] -> (f, "")
  | s :: _ when Filename.check_suffix f s -> (Filename.chop_suffix f s, s)
  | _ :: l -> get_extension f l

(** File comparison *)

let absolute_dir dir =
  let current = Sys.getcwd () in
    Sys.chdir dir;
    let dir' = Sys.getcwd () in
      Sys.chdir current;
      dir'

let absolute_file_name basename odir =
  let dir = match odir with Some dir -> dir | None -> "." in
  absolute_dir dir // basename

let compare_file f1 f2 =
  absolute_file_name (Filename.basename f1) (Some (Filename.dirname f1))
  = absolute_file_name (Filename.basename f2) (Some (Filename.dirname f2))

(** [basename_noext] removes both the directory part and the extension
    (if necessary) of a filename *)

let basename_noext filename =
  let fn = Filename.basename filename in
  try Filename.chop_extension fn with Invalid_argument _ -> fn

(** Coq files specifies on the command line:
    - first string is the full filename, with only its extension removed
    - second string is the absolute version of the previous (via getcwd)
*)

let vAccu   = ref ([] : (string * string) list)

(** Queue operations *)

let addQueue q v = q := v :: !q

type dirname = string
type basename = string
type filename = string
type dirpath = string list
type root = filename * dirpath

type result =
  | ExactMatches of filename list
  | PartialMatchesInSameRoot of root * filename list

let add_set f l = f :: CList.remove compare_file f l

let insert_key root (full,f) m =
  (* An exact match takes precedence over non-exact matches *)
  match full, m with
  | true, ExactMatches l -> (* We add a conflict *) ExactMatches (add_set f l)
  | true, PartialMatchesInSameRoot _ -> (* We give priority to exact match *) ExactMatches [f]
  | false, ExactMatches l -> (* We keep the exact match *) m
  | false, PartialMatchesInSameRoot (root',l) ->
    PartialMatchesInSameRoot (root, if root = root' then add_set f l else [f])

let safe_add_key q root key (full,f as file) =
  try
    let l = Hashtbl.find q key in
    Hashtbl.add q key (insert_key root file l)
  with Not_found ->
    Hashtbl.add q key (if full then ExactMatches [f] else PartialMatchesInSameRoot (root,[f]))

let safe_add q root ((from, suffixes), file) =
  List.iter (fun (full,suff) -> safe_add_key q root (from,suff) (full,file)) suffixes

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

let add_mllib_known, _, search_mllib_known = mkknown ()
let add_mlpack_known, _, search_mlpack_known = mkknown ()

let vKnown = (Hashtbl.create 19 : (dirpath * dirpath, result) Hashtbl.t)
(* The associated boolean is true if this is a root path. *)
let coqlibKnown = (Hashtbl.create 19 : (dirpath * dirpath, result) Hashtbl.t)

let search_table table ?(from=[]) s =
  Hashtbl.find table (from, s)

let search_v_known ?from s =
  try Some (search_table vKnown ?from s)
  with Not_found -> None

let is_in_coqlib ?from s =
  try let _ = search_table coqlibKnown ?from s in true with Not_found -> false

let error_cannot_parse s (i,j) =
  Printf.eprintf "File \"%s\", characters %i-%i: Syntax error\n" s i j;
  exit 1

let error_cannot_open_project_file msg =
  Printf.eprintf "%s\n" msg;
  exit 1

let error_cannot_parse_project_file file msg =
  Printf.eprintf "Project file \"%s\": Syntax error: %s\n" file msg;
  exit 1

let error_cannot_stat s unix_error =
  Printf.eprintf "%s\n" (error_message unix_error);
  exit 1

let error_cannot_stat_in f s unix_error =
  Printf.eprintf "In file \"%s\": %s\n" f (error_message unix_error);
  exit 1

let error_cannot_open s msg =
  (* Print an arbitrary line number, such that the message matches
     common error message pattern. *)
  Printf.eprintf "%s: %s\n" s msg;
  exit 1

let warning_module_notfound from f s =
  match from with
  | None ->
      coqdep_warning "in file %s, library %s is required and has not been found in the loadpath!"
        f (String.concat "." s)
  | Some pth ->
      coqdep_warning "in file %s, library %s is required from root %s and has not been found in the loadpath!"
        f (String.concat "." s) (String.concat "." pth)

let warning_declare f s =
  coqdep_warning "in file %s, declared ML module %s has not been found!" f s

let warning_clash exact file dir f1 = function
  | f2::fl ->
      let f = Filename.basename f1 in
      let d1 = Filename.dirname f1 in
      let d2 = Filename.dirname f2 in
      let dl = List.rev_map Filename.dirname fl in
      if exact then
        begin
          eprintf
            "*** Warning: in file %s, \n    required library %s exactly matches several files in path\n    (found %s.v in "
            file (String.concat "." dir) f;
          List.iter (fun s -> eprintf "%s, " s) dl;
          eprintf "%s and %s; used the latter).\n" d2 d1
        end
      else
        begin
          eprintf
            "*** Warning: in file %s, \n    required library %s matches several files in path\n    (found %s.v in "
            file (String.concat "." dir) f;
          List.iter (fun s -> eprintf "%s, " s) dl;
          eprintf "%s and %s; Require will fail).\n" d2 d1
        end
  | [] -> assert false

let warning_cannot_open_dir dir =
  coqdep_warning "cannot open %s" dir

let safe_assoc from verbose file k =
  match search_v_known ?from k with
  | None -> None
  | Some (ExactMatches (f :: l)) ->
    if verbose && not (CList.is_empty l) then warning_clash true file k f l; Some [f]
  | Some (PartialMatchesInSameRoot (root, l)) ->
    (match List.sort String.compare l with [] -> assert false | f :: l as all ->
    (* If several files match, it will fail at Require;
       To be "fair", in coqdep, we add dependencies on all matching files *)
    if verbose && not (CList.is_empty l) then warning_clash false file k f l; Some all)
  | Some (ExactMatches []) -> assert false

(** [find_dir_logpath dir] Return the logical path of directory [dir]
    if it has been given one. Raise [Not_found] otherwise. In
    particular we can check if "." has been attributed a logical path
    after processing all options and silently give the default one if
    it hasn't. We may also use this to warn if a physical path is met
    twice. *)
let register_dir_logpath,find_dir_logpath =
  let tbl: (string, string list) Hashtbl.t = Hashtbl.create 19 in
  let reg physdir logpath = Hashtbl.add tbl (absolute_dir physdir) logpath in
  let fnd physdir = Hashtbl.find tbl (absolute_dir physdir) in
  reg,fnd

let file_name s = function
  | None     -> s
  | Some d   -> d // s

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

let canonize f =
  let f' = absolute_dir (Filename.dirname f) // Filename.basename f in
  match List.filter (fun (_,full) -> f' = full) !vAccu with
    | (f,_) :: _ -> escape f
    | _ -> escape f

module VData = struct
  type t = string list option * string list
  let compare = compare
end

module VCache = Set.Make(VData)

(** To avoid reading .v files several times for computing dependencies,
    once for .vo, once for .vio, and once for .vos extensions, the
    following code performs a single pass and produces a structured
    list of dependencies, separating dependencies on compiled Coq files
    (those loaded by [Require]) from other dependencies, e.g. dependencies
    on ".v" files (for [Load]) or ".cmx", ".cmo", etc... (for [Declare]). *)

type dependency =
  | DepRequire of string (* one basename, to which we later append .vo or .vio or .vos *)
  | DepOther of string   (* filenames of dependencies, separated by spaces *)

let string_of_dependency_list suffix_for_require deps =
  let string_of_dep = function
    | DepRequire basename -> basename ^ suffix_for_require
    | DepOther s -> s
    in
  String.concat " " (List.map string_of_dep deps)

let rec find_dependencies basename =
  let verbose = true in (* for past/future use? *)
  try
    (* Visited marks *)
    let visited_ml = ref StrSet.empty in
    let visited_v = ref VCache.empty in
    let should_visit_v_and_mark from str =
       if not (VCache.mem (from, str) !visited_v) then begin
          visited_v := VCache.add (from, str) !visited_v;
          true
       end else false
       in
    (* Output: dependencies found *)
    let dependencies = ref [] in
    let add_dep dep =
       dependencies := dep::!dependencies in
    let add_dep_other s =
       add_dep (DepOther s) in

    (* Reading file contents *)
    let f = basename ^ ".v" in
    let chan = open_in f in
    let buf = Lexing.from_channel chan in
    try
      while true do
        let tok = coq_action buf in
        match tok with
        | Require (from, strl) ->
            List.iter (fun str ->
              if should_visit_v_and_mark from str then begin
              match safe_assoc from verbose f str with
              | Some files -> List.iter (fun file_str -> add_dep (DepRequire (canonize file_str))) files
              | None ->
                  if verbose && not (is_in_coqlib ?from str) then
                  warning_module_notfound from f str
              end) strl
        | Declare sl ->
            let declare suff dir s =
              let base = escape (file_name s dir) in
              match !option_dynlink with
              | No -> ()
              | Byte -> add_dep_other (sprintf "%s%s" base suff)
              | Opt -> add_dep_other (sprintf "%s.cmxs" base)
              | Both -> add_dep_other (sprintf "%s%s" base suff);
                        add_dep_other (sprintf "%s.cmxs" base)
              | Variable -> add_dep_other (sprintf "%s%s" base
                  (if suff=".cmo" then "$(DYNOBJ)" else "$(DYNLIB)"))
              in
            let decl str =
              let s = basename_noext str in
              if not (StrSet.mem s !visited_ml) then begin
                visited_ml := StrSet.add s !visited_ml;
                match search_mllib_known s with
                  | Some mldir -> declare ".cma" mldir s
                  | None ->
                    match search_mlpack_known s with
                  | Some mldir -> declare ".cmo" mldir s
                  | None -> warning_declare f str
                end
                in
              List.iter decl sl
        | Load file ->
            let canon =
              match file with
              | Logical str ->
                if should_visit_v_and_mark None str then
                  Option.map (List.map canonize) (safe_assoc None verbose f str)
                else None
              | Physical str ->
                (* TODO: look in the physical part of the path even
                   when str contains "/", as coqc does *)
                if String.equal (Filename.basename str) str then
                  if should_visit_v_and_mark None [str] then safe_assoc None verbose f [str]
                  else None
                else
                  Some [canonize str]
            in
            (match canon with
            | None -> ()
            | Some l ->
              List.iter (fun canon ->
              add_dep_other (sprintf "%s.v" canon);
              let deps = find_dependencies canon in
              List.iter add_dep deps) l)
        | AddLoadPath _ | AddRecLoadPath _ -> (* TODO: will this be handled? *) ()
      done;
      List.rev !dependencies
    with
    | Fin_fichier ->
        close_in chan;
        List.rev !dependencies
    | Syntax_error (i,j) ->
        close_in chan;
        error_cannot_parse f (i,j)
  with Sys_error msg -> error_cannot_open (basename ^ ".v") msg


let write_vos = ref false

let coq_dependencies () =
  List.iter
    (fun (name,_) ->
       let ename = escape name in
       let glob = if !option_noglob then "" else ename^".glob " in
       let deps = find_dependencies name in
       printf "%s.vo %s%s.v.beautified %s.required_vo: %s.v %s\n" ename glob ename ename ename
        (string_of_dependency_list ".vo" deps);
       printf "%s.vio: %s.v %s\n" ename ename
         (string_of_dependency_list ".vio" deps);
       if !write_vos then
         printf "%s.vos %s.vok %s.required_vos: %s.v %s\n" ename ename ename ename
           (string_of_dependency_list ".vos" deps);
       printf "%!")
    (List.rev !vAccu)

(** Compute the suffixes of a logical path together with the length of the missing part *)
let rec suffixes full = function
  | [] -> assert false
  | [name] -> [full,[name]]
  | dir::suffix as l -> (full,l)::suffixes false suffix

(** Compute all the pairs [(from,suffs] such that a logical path
    decomposes into [from @ ... @ suff] for some [suff] in [suffs],
    i.e. such that once [from] is fixed, [From from Require suff]
    refers (in the absence of ambiguity) to this logical path for
    exactly the [suff] in [suffs] *)
let rec cuts recur = function
  | [] -> []
  | [dir] ->
    [[],[true,[dir]]]
  | dir::tail as l ->
    ([],if recur then suffixes true l else [true,l]) ::
    List.map (fun (fromtail,suffixes) -> (dir::fromtail,suffixes)) (cuts true tail)

let add_caml_known _ phys_dir _ f =
  let basename,suff =
    get_extension f [".mllib"; ".mlpack"] in
  match suff with
    | ".mllib" -> add_mllib_known basename (Some phys_dir) suff
    | ".mlpack" -> add_mlpack_known basename (Some phys_dir) suff
    | _ -> ()

let add_paths recur root table phys_dir log_dir basename =
  let name = log_dir@[basename] in
  let file = phys_dir//basename in
  let paths = cuts recur name in
  let iter n = safe_add table root (n, file) in
  List.iter iter paths

let add_coqlib_known recur root phys_dir log_dir f =
  let root = (phys_dir, log_dir) in
  match get_extension f [".vo"; ".vio"; ".vos"] with
    | (basename, (".vo" | ".vio" | ".vos")) ->
        add_paths recur root coqlibKnown phys_dir log_dir basename
    | _ -> ()

let add_v_known recur root phys_dir log_dir f =
  match get_extension f [".v"; ".vo"; ".vio"; ".vos"] with
    | (basename,".v") ->
        add_paths recur root vKnown phys_dir log_dir basename
    | (basename, (".vo" | ".vio" | ".vos")) when not(!option_boot) ->
        add_paths recur root vKnown phys_dir log_dir basename
    | _ -> ()

(** Visit all the directories under [dir], including [dir], in the
    same order as for [coqc]/[coqtop] in [System.all_subdirs], that
    is, assuming Sys.readdir to have this structure:
    ├── B
    │   └── E.v
    │   └── C1
    │   │   └── E.v
    │   │   └── D1
    │   │       └── E.v
    │   │   └── F.v
    │   │   └── D2
    │   │       └── E.v
    │   │   └── G.v
    │   └── F.v
    │   └── C2
    │   │   └── E.v
    │   │   └── D1
    │   │       └── E.v
    │   │   └── F.v
    │   │   └── D2
    │   │       └── E.v
    │   │   └── G.v
    │   └── G.v
    it goes in this (reverse) order:
    B.C2.D1.E, B.C2.D2.E,
    B.C2.E, B.C2.F, B.C2.G
    B.C1.D1.E, B.C1.D2.E,
    B.C1.E, B.C1.F, B.C1.G,
    B.E, B.F, B.G,
    (see discussion at PR #14718)
*)

let add_directory recur add_file phys_dir log_dir =
  let root = (phys_dir, log_dir) in
  let stack = ref [] in
  let curdirfiles = ref [] in
  let subdirfiles = ref [] in
  let rec aux phys_dir log_dir =
    if exists_dir phys_dir then
      begin
        register_dir_logpath phys_dir log_dir;
        let f = function
          | FileDir (phys_f,f) ->
              if recur then begin
                stack := (!curdirfiles, !subdirfiles) :: !stack;
                curdirfiles := []; subdirfiles := [];
                aux phys_f (log_dir @ [f]);
                let curdirfiles', subdirfiles' = List.hd !stack in
                subdirfiles := subdirfiles' @ !subdirfiles @ !curdirfiles;
                curdirfiles := curdirfiles'; stack := List.tl !stack
              end
          | FileRegular f ->
              curdirfiles := (phys_dir, log_dir, f) :: !curdirfiles
        in
        process_directory f phys_dir
      end
    else
      warning_cannot_open_dir phys_dir
  in
  aux phys_dir log_dir;
  List.iter (fun (phys_dir, log_dir, f) -> add_file root phys_dir log_dir f) !subdirfiles;
  List.iter (fun (phys_dir, log_dir, f) -> add_file root phys_dir log_dir f) !curdirfiles

(** Simply add this directory and imports it, no subdirs. This is used
    by the implicit adding of the current path (which is not recursive). *)
let add_norec_dir_import add_file phys_dir log_dir =
  add_directory false (add_file true) phys_dir log_dir

(** -Q semantic: go in subdirs but only full logical paths are known. *)
let add_rec_dir_no_import add_file phys_dir log_dir =
  add_directory true (add_file false) phys_dir log_dir

(** -R semantic: go in subdirs and suffixes of logical paths are known. *)
let add_rec_dir_import add_file phys_dir log_dir =
  add_directory true (add_file true) phys_dir log_dir

(** -I semantic: do not go in subdirs. *)
let add_caml_dir phys_dir =
  add_directory false add_caml_known phys_dir []

exception Cannot_stat_file of string * Unix.error

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
  let stat_res =
    try stat complete_name
    with Unix_error(error, _, _) -> raise (Cannot_stat_file (complete_name, error))
  in
  match stat_res.st_kind
  with
    | S_DIR ->
        (if name.[0] <> '.' then
           let newdirname =
             match dirname with
               | None -> name
               | Some d -> d//name
           in
           Array.iter (treat_file (Some newdirname)) (Sys.readdir complete_name))
    | S_REG ->
      (match get_extension name [".v"] with
       | base,".v" ->
         let name = file_name base dirname
         and absname = absolute_file_name base dirname in
         addQueue vAccu (name, absname)
       | _ -> ())
    | _ -> ()

let treat_file_command_line old_name =
  try treat_file None old_name
  with Cannot_stat_file (f, msg) ->
    error_cannot_stat f msg

let treat_file_coq_project where old_name =
  try treat_file None old_name
  with Cannot_stat_file (f, msg) ->
    error_cannot_stat_in where f msg

(* "[sort]" outputs `.v` files required by others *)
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
            | Require (from, sl) ->
                List.iter
                  (fun s ->
                    match safe_assoc from false file s with
                    | None -> ()
                    | Some l -> List.iter loop l)
                sl
            | _ -> ()
        done
      with Fin_fichier ->
        close_in cin;
        printf "%s.v " file
    end
  in
  List.iter (fun (name,_) -> loop name) !vAccu

let usage () =
  eprintf " usage: coqdep [options] <filename>+\n";
  eprintf " options:\n";
  eprintf "  -boot : For coq developers, prints dependencies over coq library files (omitted by default).\n";
  eprintf "  -sort : output the given file name ordered by dependencies\n";
  eprintf "  -noglob | -no-glob : \n";
  eprintf "  -noinit : currently no effect\n";
  eprintf "  -f file : read -I, -Q, -R and filenames from _CoqProject-formatted FILE.\n";
  eprintf "  -I dir : add (non recursively) dir to ocaml path\n";
  eprintf "  -R dir logname : add and import dir recursively to coq load path under logical name logname\n";
  eprintf "  -Q dir logname : add (recursively) and open (non recursively) dir to coq load path under logical name logname\n";
  eprintf "  -vos : also output dependencies about .vos files\n";
  eprintf "  -exclude-dir dir : skip subdirectories named 'dir' during -R/-Q search\n";
  eprintf "  -coqlib dir : set the coq standard library directory\n";
  eprintf "  -dyndep (opt|byte|both|no|var) : set how dependencies over ML modules are printed\n";
  exit 1

let option_sort = ref false

let split_period = Str.split (Str.regexp (Str.quote "."))

let add_q_include path l = add_rec_dir_no_import add_v_known path (split_period l)
let add_r_include path l = add_rec_dir_import add_v_known path (split_period l)

let treat_coqproject f =
  let open CoqProject_file in
  let iter_sourced f = List.iter (fun {thing} -> f thing) in
  let warning_fn x = coqdep_warning "%s" x in
  let project =
    try read_project_file ~warning_fn f
    with
    | Parsing_error msg -> error_cannot_parse_project_file f msg
    | UnableToOpenProjectFile msg -> error_cannot_open_project_file msg
  in
  iter_sourced (fun { path } -> add_caml_dir path) project.ml_includes;
  iter_sourced (fun ({ path }, l) -> add_q_include path l) project.q_includes;
  iter_sourced (fun ({ path }, l) -> add_r_include path l) project.r_includes;
  iter_sourced (fun f' -> treat_file_coq_project f f') (all_files project)

let rec parse = function
  | "-boot" :: ll -> option_boot := true; parse ll
  | "-sort" :: ll -> option_sort := true; parse ll
  | "-vos" :: ll -> write_vos := true; parse ll
  | ("-noglob" | "-no-glob") :: ll -> option_noglob := true; parse ll
  | "-noinit" :: ll -> (* do nothing *) parse ll
  | "-f" :: f :: ll -> treat_coqproject f; parse ll
  | "-I" :: r :: ll -> add_caml_dir r; parse ll
  | "-I" :: [] -> usage ()
  | "-R" :: r :: ln :: ll -> add_r_include r ln; parse ll
  | "-Q" :: r :: ln :: ll -> add_q_include r ln; parse ll
  | "-R" :: ([] | [_]) -> usage ()
  | "-exclude-dir" :: r :: ll -> System.exclude_directory r; parse ll
  | "-exclude-dir" :: [] -> usage ()
  | "-coqlib" :: r :: ll -> Boot.Env.set_coqlib r; parse ll
  | "-coqlib" :: [] -> usage ()
  | "-dyndep" :: "no" :: ll -> option_dynlink := No; parse ll
  | "-dyndep" :: "opt" :: ll -> option_dynlink := Opt; parse ll
  | "-dyndep" :: "byte" :: ll -> option_dynlink := Byte; parse ll
  | "-dyndep" :: "both" :: ll -> option_dynlink := Both; parse ll
  | "-dyndep" :: "var" :: ll -> option_dynlink := Variable; parse ll
  | ("-h"|"--help"|"-help") :: _ -> usage ()
  | opt :: ll when String.length opt > 0 && opt.[0] = '-' ->
    coqdep_warning "unknown option %s" opt;
    parse ll
  | f :: ll -> treat_file_command_line f; parse ll
  | [] -> ()

let init () =
  if Array.length Sys.argv < 2 then usage ();
  if not Coq_config.has_natdynlink then option_dynlink := No;
  parse (List.tl (Array.to_list Sys.argv))
