(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open System
open Format
open Unix
open Lexer

let coqdep_warning args =
  eprintf "*** Warning: @[";
  kfprintf (fun fmt -> fprintf fmt "@]\n%!") err_formatter args

module StrSet = Set.Make(String)

type dynlink = Opt | Byte | Both | No | Variable

let option_noglob = ref false
let option_dynlink = ref Both

let meta_files = ref []

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

(** Exceptions *)

module Error = struct

  exception CannotParseFile of string * (int * int)
  exception CannotParseProjectFile of string * string
  exception CannotParseMetaFile of string * string

  exception CannotOpenFile of string * string
  exception CannotOpenProjectFile of string

  exception MetaLacksFieldForPackage of string * string * string
  exception DeclaredMLModuleNotFound of string * string * string
  exception InvalidFindlibPluginName of string * string
  exception CannotFindMeta of string * string

  let _ = CErrors.register_handler @@ function
    | CannotParseFile (s,(i,j)) ->
      Some Pp.(str "File \"" ++ str s ++ str "\"," ++ str "characters" ++ spc ()
        ++ int i ++ str "-" ++ int j ++ str ":" ++ spc () ++ str "Syntax error")

    | CannotParseProjectFile (file, msg) ->
      Some Pp.(str "Project file" ++ spc () ++ str  "\"" ++ str file ++ str "\":" ++ spc ()
        ++ str "Syntax error:" ++ str msg)

    | CannotParseMetaFile (file, msg) ->
      Some Pp.(str "META file \"" ++ str file ++ str "\":" ++ spc ()
        ++ str "Syntax error:" ++ spc () ++ str msg)

    | CannotOpenFile (s, msg) ->
      Some Pp.(str s ++ str ":" ++ spc () ++ str msg)

    | CannotOpenProjectFile msg ->
      (* TODO: more info? *)
      Some Pp.(str msg)

    | MetaLacksFieldForPackage (meta_file, package, field) ->
      Some Pp.(str "META file \"" ++ str meta_file ++ str "\"" ++ spc () ++ str "lacks field" ++ spc ()
        ++ str field ++ spc () ++ str "for package" ++ spc () ++ str package ++ str ".")

    | DeclaredMLModuleNotFound (f, s, m) ->
      Some Pp.(str "in file " ++ str f ++ str "," ++ spc() ++ str "declared ML module" ++ spc ()
        ++ str s ++ spc () ++ str "has not been found in" ++ spc () ++ str m ++ str ".")

    | InvalidFindlibPluginName (f, s) ->
      Some Pp.(str (Printf.sprintf "in file %s, %s is not a valid plugin name anymore." f s)
        ++ str "Plugins should be loaded using their public name according to findlib," ++ spc ()
        ++ str "for example package-name.foo and not foo_plugin." ++ spc ()
        ++ str "If you are building with dune < 2.9.4 you must specify both" ++ spc ()
        ++ str "the legacy and the findlib plugin name as in:" ++ spc ()
        ++ str "Declare ML Module \"foo_plugin:package-name.foo\".")

    | CannotFindMeta (f, package) ->
      Some Pp.(str "in file" ++ spc () ++ str f ++ str "," ++ spc ()
        ++ str "could not find META." ++ str package ++ str ".")

    | _ -> None

  let cannot_parse s ij = raise @@ CannotParseFile (s, ij)
  let cannot_open_project_file msg = raise @@ CannotOpenProjectFile msg
  let cannot_parse_project_file file msg = raise @@ CannotParseProjectFile (file, msg)
  let cannot_parse_meta_file file msg = raise @@ CannotParseMetaFile (file, msg)
  let meta_file_lacks_field meta_file package field = raise @@ MetaLacksFieldForPackage (meta_file, package, field)
  let cannot_open s msg = raise @@ CannotOpenFile (s, msg)
  let declare_in_META f s m = raise @@ DeclaredMLModuleNotFound (f, s, m)
  let findlib_name f s = raise @@ InvalidFindlibPluginName (f, s)
  let no_meta f package = raise @@ CannotFindMeta (f, package)
end

type what = Library | External
let str_of_what = function Library -> "library" | External -> "external file"

let warning_module_notfound ?(what=Library) from f s =
  let what = str_of_what what in
  match from with
  | None ->
      coqdep_warning "in file %s, %s %s is required and has not been found in the loadpath!"
        f what (String.concat "." s)
  | Some pth ->
      coqdep_warning "in file %s, %s %s is required from root %s and has not been found in the loadpath!"
        f what (String.concat "." s) (String.concat "." pth)

let warning_declare f s =
  coqdep_warning "in file %s, declared ML module %s has not been found!" f s

let warn_if_clash ?(what=Library) exact file dir f1 = function
  | f2::fl ->
      let f =
        match what with
        | Library -> Filename.basename f1 ^ ".v"
        | External -> Filename.basename f1 in
      let what = str_of_what what in
      let d1 = Filename.dirname f1 in
      let d2 = Filename.dirname f2 in
      let dl = List.rev_map Filename.dirname fl in
      if exact then
        begin
          eprintf
            "*** Warning: in file %s, \n    required %s %s exactly matches several files in path\n    (found %s in "
            file what (String.concat "." dir) f;
          List.iter (fun s -> eprintf "%s, " s) dl;
          eprintf "%s and %s; used the latter).\n" d2 d1
        end
      else
        begin
          eprintf
            "*** Warning: in file %s, \n    required %s %s matches several files in path\n    (found %s in "
            file what (String.concat "." dir) f;
          List.iter (fun s -> eprintf "%s, " s) dl;
          eprintf "%s and %s; Require will fail).\n" d2 d1
        end
  | [] -> ()

let safe_assoc st ?(what=Library) from verbose file k =
  let search =
    match what with
    | Library -> Loadpath.search_v_known st
    | External -> Loadpath.search_other_known st in
  match search ?from k with
  | None -> None
  | Some (Loadpath.ExactMatches (f :: l)) ->
    if verbose then warn_if_clash ~what true file k f l; Some [f]
  | Some (Loadpath.PartialMatchesInSameRoot (root, l)) ->
    (match List.sort String.compare l with [] -> assert false | f :: l as all ->
    (* If several files match, it will fail at Require;
       To be "fair", in coqdep, we add dependencies on all matching files *)
    if verbose then warn_if_clash ~what false file k f l; Some all)
  | Some (Loadpath.ExactMatches []) -> assert false

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
  let f' = Loadpath.absolute_dir (Filename.dirname f) // Filename.basename f in
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

module Dep = struct
  type t =
  | Require of string (* one basename, to which we later append .vo or .vio or .vos *)
  | Other of string   (* filenames of dependencies, separated by spaces *)

  let to_string ~suffix = function
    | Require basename -> basename ^ suffix
    | Other s -> s
end

let string_of_dependency_list suffix_for_require deps =
  String.concat " " (List.map (Dep.to_string ~suffix:suffix_for_require) deps)

let parse_META package f =
  try
    let ic = open_in f in
    let m = Fl_metascanner.parse ic in
    close_in ic;
    Some (f, m)
  with
  | Stream.Error msg -> Error.cannot_parse_meta_file package msg
  | Sys_error _msg -> None

let find_META package =
  let rec aux = function
    | [] ->
      (* this is needed by stdlib2 for example, since it loads a package it
         does not own, so we check it is installed. *)
      begin try
        let m = Findlib.package_meta_file package in
        parse_META package m
      with Fl_package_base.No_such_package _ -> None end
    | m :: ms ->
        if Filename.extension m = "." ^ package then
          parse_META package m
        else
          aux ms
  in
    aux !meta_files

let findlib_resolve f package legacy_name plugin =
  let open Fl_metascanner in
  match find_META package, legacy_name with
  | None, Some p -> None, p
  | None, None -> Error.no_meta f package
  | Some (meta_file, meta), _ ->
      let rec find_plugin path p { pkg_defs ; pkg_children  } =
        match p with
        | [] -> path, pkg_defs
        | p :: ps ->
            let rec find_child = function
              | [] -> Error.declare_in_META f (String.concat "." plugin) meta_file
              | (s, def) :: _ when s = p -> def
              | _ :: rest -> find_child rest
            in
            let c = find_child pkg_children in
            let path = path @ [find_plugin_field "directory" (Some ".") c.pkg_defs] in
            find_plugin path ps c
      and find_plugin_field fld def = function
        | { def_var; def_value; _ } :: _ when def_var = fld -> def_value
        | _ :: rest -> find_plugin_field fld def rest
        | [] ->
            match def with
            | Some x -> x
            | None -> Error.meta_file_lacks_field meta_file package fld
      in
      let path = [find_plugin_field "directory" (Some ".") meta.pkg_defs] in
      let path, plug = find_plugin path plugin meta in
      Some meta_file, String.concat "/" path ^ "/" ^
        Filename.chop_extension @@ find_plugin_field "plugin" None plug

let legacy_mapping = Core_plugins_findlib_compat.legacy_to_findlib

let rec find_dependencies st basename =
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
       add_dep (Dep.Other s) in

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
              match safe_assoc st from verbose f str with
              | Some files -> List.iter (fun file_str -> add_dep (Dep.Require (canonize file_str))) files
              | None ->
                  if verbose && not (Loadpath.is_in_coqlib st ?from str) then
                  warning_module_notfound from f str
              end) strl
        | Declare sl ->
            let public_to_private_name = function
              | [[x]] when List.mem_assoc x legacy_mapping ->
                  findlib_resolve f "coq-core" (Some x) (List.assoc x legacy_mapping)
              | [[x]] ->
                  Error.findlib_name f x
              | [[legacy]; package :: plugin] ->
                  findlib_resolve f package (Some legacy) plugin
              | [package :: plugin] ->
                  findlib_resolve f package None plugin
              | _ -> assert false in
            let sl = List.map (String.split_on_char ':') sl in
            let sl = List.map (List.map (String.split_on_char '.')) sl in
            let sl = List.map public_to_private_name sl in
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
            let decl (meta_file,str) =
              Option.iter add_dep_other meta_file;
              let s = basename_noext str in
              if not (StrSet.mem s !visited_ml) then begin
                visited_ml := StrSet.add s !visited_ml;
                match Loadpath.search_mllib_known st s with
                  | Some mldir -> declare ".cma" mldir s
                  | None ->
                    match Loadpath.search_mlpack_known st s with
                  | Some mldir -> declare ".cmo" mldir s
                  | None -> warning_declare f str
                end
                in
              List.iter decl sl
        | Load file ->
            let canon =
              match file with
              | Logical str ->
                if should_visit_v_and_mark None [str] then safe_assoc st None verbose f [str]
                else None
              | Physical str ->
                if String.equal (Filename.basename str) str then
                  if should_visit_v_and_mark None [str] then safe_assoc st None verbose f [str]
                  else None
                else
                  Some [canonize str]
            in
            (match canon with
            | None -> ()
            | Some l ->
              List.iter (fun canon ->
              add_dep_other (sprintf "%s.v" canon);
              let deps = find_dependencies st canon in
              List.iter add_dep deps) l)
        | External(from,str) ->
            begin match safe_assoc st ~what:External (Some from) verbose f [str] with
            | Some (file :: _) -> add_dep (Dep.Other (canonize file))
            | Some [] -> assert false
            | None -> warning_module_notfound ~what:External (Some from) f [str]
            end
        | AddLoadPath _ | AddRecLoadPath _ -> (* TODO: will this be handled? *) ()
      done;
      List.rev !dependencies
    with
    | Fin_fichier ->
        close_in chan;
        List.rev !dependencies
    | Syntax_error (i,j) ->
        close_in chan;
        Error.cannot_parse f (i,j)
  with Sys_error msg -> Error.cannot_open (basename ^ ".v") msg


let write_vos = ref false

module Dep_info = struct

  type t =
    { name : string  (* This should become [module : Coq_module.t] eventually *)
    ; deps : Dep.t list
    }

  let make name deps = { name; deps }

  open Format

  let print fmt { name; deps } =
    let ename = escape name in
    let glob = if !option_noglob then "" else ename^".glob " in
    fprintf fmt "%s.vo %s%s.v.beautified %s.required_vo: %s.v %s\n" ename glob ename ename ename
      (string_of_dependency_list ".vo" deps);
    fprintf fmt "%s.vio: %s.v %s\n" ename ename
      (string_of_dependency_list ".vio" deps);
    if !write_vos then
      fprintf fmt "%s.vos %s.vok %s.required_vos: %s.v %s\n" ename ename ename ename
        (string_of_dependency_list ".vos" deps);
    fprintf fmt "%!"

end

module State = struct

  type t = Loadpath.State.t
  let loadpath x = x

end

let compute_deps st =
  let mk_dep (name, _) = Dep_info.make name (find_dependencies st name) in
  !vAccu |> List.rev |> List.map mk_dep

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
      (match Loadpath.get_extension name [".v"] with
       | base,".v" ->
         let name = file_name base dirname
         and absname = Loadpath.absolute_file_name base dirname in
         addQueue vAccu (name, absname)
       | _ -> ())
    | _ -> ()

let treat_file_command_line old_name =
  treat_file None old_name

let treat_file_coq_project where old_name =
  treat_file None old_name

(* "[sort]" outputs `.v` files required by others *)
let sort st =
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
                    match safe_assoc st from false file s with
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
  eprintf "  -m META : resolve plugins names using the META file\n";
  exit 1

let option_sort = ref false

let treat_coqproject st f =
  let open CoqProject_file in
  let iter_sourced f = List.iter (fun {thing} -> f thing) in
  let warning_fn x = coqdep_warning "%s" x in
  let project =
    try read_project_file ~warning_fn f
    with
    | Parsing_error msg -> Error.cannot_parse_project_file f msg
    | UnableToOpenProjectFile msg -> Error.cannot_open_project_file msg
  in
  iter_sourced (fun { path } -> Loadpath.add_caml_dir st path) project.ml_includes;
  iter_sourced (fun ({ path }, l) -> Loadpath.add_q_include st path l) project.q_includes;
  iter_sourced (fun ({ path }, l) -> Loadpath.add_r_include st path l) project.r_includes;
  iter_sourced (fun f' -> treat_file_coq_project f f') (all_files project)

module Args = struct

  type t =
    { coqproject : string option
    ; ml_path : string list
    ; vo_path : (bool * string * string) list
    ; files : string list
    }

  let make () =
    { coqproject = None
    ; ml_path = []
    ; vo_path = []
    ; files = []
    }

end

let parse st args =
  let rec parse st =
    function
    | "-boot" :: ll -> Options.boot := true; parse st ll
    | "-sort" :: ll -> option_sort := true; parse st ll
    | "-vos" :: ll -> write_vos := true; parse st ll
    | ("-noglob" | "-no-glob") :: ll -> option_noglob := true; parse st ll
    | "-noinit" :: ll -> (* do nothing *) parse st ll
    | "-f" :: f :: ll -> parse { st with Args.coqproject = Some f } ll
    | "-I" :: r :: ll -> parse { st with Args.ml_path = r :: st.Args.ml_path } ll
    | "-I" :: [] -> usage ()
    | "-R" :: r :: ln :: ll -> parse { st with Args.vo_path = (true, r, ln) :: st.Args.vo_path } ll
    | "-Q" :: r :: ln :: ll -> parse { st with Args.vo_path = (false, r, ln) :: st.Args.vo_path } ll
    | "-R" :: ([] | [_]) -> usage ()
    | "-exclude-dir" :: r :: ll -> System.exclude_directory r; parse st ll
    | "-exclude-dir" :: [] -> usage ()
    | "-coqlib" :: r :: ll -> Boot.Env.set_coqlib r; parse st ll
    | "-coqlib" :: [] -> usage ()
    | "-dyndep" :: "no" :: ll -> option_dynlink := No; parse st ll
    | "-dyndep" :: "opt" :: ll -> option_dynlink := Opt; parse st ll
    | "-dyndep" :: "byte" :: ll -> option_dynlink := Byte; parse st ll
    | "-dyndep" :: "both" :: ll -> option_dynlink := Both; parse st ll
    | "-dyndep" :: "var" :: ll -> option_dynlink := Variable; parse st ll
    | "-m" :: m :: ll -> meta_files := !meta_files @ [m]; parse st ll
    | ("-h"|"--help"|"-help") :: _ -> usage ()
    | opt :: ll when String.length opt > 0 && opt.[0] = '-' ->
      coqdep_warning "unknown option %s" opt;
      parse st ll
    | f :: ll -> parse { st with Args.files = f :: st.Args.files } ll
    | [] -> st
  in
  let st = parse st args in
  let open Args in
  { st with
    ml_path = List.rev st.ml_path
  ; vo_path = List.rev st.vo_path
  ; files = List.rev st.files
  }

let add_include st (rc, r, ln) =
  if rc then
    Loadpath.add_r_include st r ln
  else
    Loadpath.add_q_include st r ln

let init args =
  vAccu := [];
  if not Coq_config.has_natdynlink then option_dynlink := No;
  let { Args.coqproject; ml_path; vo_path; files } = parse (Args.make ()) args in
  let st = Loadpath.State.make () in
  Option.iter (treat_coqproject st) coqproject;
  List.iter (Loadpath.add_caml_dir st) ml_path;
  List.iter (add_include st) vo_path;
  files, st
