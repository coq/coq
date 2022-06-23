(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module StrSet = Set.Make(String)

(** [basename_noext] removes both the directory part and the extension
    (if necessary) of a filename *)
let basename_noext filename =
  let fn = Filename.basename filename in
  try Filename.chop_extension fn with Invalid_argument _ -> fn

(** Coq files specifies on the command line:
    - first string is the full filename, with only its extension removed
    - second string is the absolute version of the previous (via getcwd)
*)
let vAccu = ref ([] : (string * string) list)

let separator_hack = ref true
let filename_concat dir name =
  if !separator_hack
  then System.(dir // name)
  else Filename.concat dir name

(* This is used to overcome makefile limitations w.r.t. filenames,
   (bar/../foo is not the same than ./foo for make) but it is a crude
   hack and we should remove it, and instead require users to follow
   the same naming convention *)
let canonize f =
  let f' = filename_concat (Loadpath.absolute_dir (Filename.dirname f)) (Filename.basename f) in
  match List.filter (fun (_,full) -> f' = full) !vAccu with
    | (f,_) :: _ -> f
    | _ -> f

(** Queue operations *)
let addQueue q v = q := v :: !q

type what = Library | External
let str_of_what = function Library -> "library" | External -> "external file"

let warning_module_notfound ?(what=Library) from f s =
  let what = str_of_what what in
  match from with
  | None ->
    Warning.give "in file %s, %s %s is required and has not been found in the loadpath!"
      f what (String.concat "." s)
  | Some pth ->
    Warning.give "in file %s, %s %s is required from root %s and has not been found in the loadpath!"
      f what (String.concat "." s) (String.concat "." pth)

let warning_declare f s =
  Warning.give "in file %s, declared ML module %s has not been found!" f s

let warn_if_clash ?(what=Library) exact file dir f1 = let open Format in function
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
  | Some d   -> filename_concat d s

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

let legacy_mapping = Core_plugins_findlib_compat.legacy_to_findlib

let meta_files = ref []

(* Transform "Declare ML %DECL" to a pair of (meta, cmxs). Something
   very similar is in ML top *)
let declare_ml_to_file file decl =
  let decl = String.split_on_char ':' decl in
  let decl = List.map (String.split_on_char '.') decl in
  let meta_files = !meta_files in
  match decl with
  | [[x]] when List.mem_assoc x legacy_mapping ->
    Fl.findlib_resolve ~meta_files ~file ~package:"coq-core" ~legacy_name:(Some x) ~plugin_name:(List.assoc x legacy_mapping)
  | [[x]] ->
    Error.findlib_name file x
  | [[legacy]; package :: plugin_name] ->
    Fl.findlib_resolve ~meta_files ~file ~package ~legacy_name:(Some legacy) ~plugin_name
  | [package :: plugin_name] ->
    Fl.findlib_resolve ~meta_files ~file ~package ~legacy_name:None ~plugin_name
  | plist ->
    CErrors.user_err
      Pp.(str "Failed to resolve plugin " ++
          pr_sequence (pr_sequence str) plist)

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
    let add_dep dep = dependencies := dep :: !dependencies in
    let add_dep_other s = add_dep (Dep_info.Dep.Other s) in

    (* Reading file contents *)
    let f = basename ^ ".v" in
    let chan = open_in f in
    let buf = Lexing.from_channel chan in
    let open Lexer in
    try
      while true do
        let tok = coq_action buf in
        match tok with
        | Require (from, strl) ->
          let decl str =
            if should_visit_v_and_mark from str then begin
              match safe_assoc st from verbose f str with
              | Some files ->
                List.iter (fun file_str ->
                    let file_str = canonize file_str in
                    add_dep (Dep_info.Dep.Require file_str)) files
              | None ->
                if verbose && not (Loadpath.is_in_coqlib st ?from str) then
                  warning_module_notfound from f str
            end
          in
          List.iter decl strl
        | Declare sl ->
          let sl = List.map (declare_ml_to_file f) sl in
          let declare suff dir s =
            let base = file_name s dir in
            add_dep (Dep_info.Dep.Ml (base,suff))
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
             let decl canon =
               add_dep_other (Format.sprintf "%s.v" canon);
               let deps = find_dependencies st canon in
               List.iter add_dep deps
             in
             List.iter decl l)
        | External(from,str) ->
          begin match safe_assoc st ~what:External (Some from) verbose f [str] with
          | Some (file :: _) -> add_dep (Dep_info.Dep.Other (canonize file))
          | Some [] -> assert false
          | None -> warning_module_notfound ~what:External (Some from) f [str]
          end
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

module State = struct
  type t = Loadpath.State.t
  let loadpath x = x
end

let compute_deps st =
  let mk_dep (name, _orig_path) = Dep_info.make ~name ~deps:(find_dependencies st name) in
  !vAccu |> List.rev |> List.map mk_dep

let rec treat_file old_dirname old_name =
  let name = Filename.basename old_name
  and new_dirname = Filename.dirname old_name in
  let dirname =
    match (old_dirname,new_dirname) with
      | (d, ".") -> d
      (* EGJA: We should disable this buggy normalization stuff for
         "./foo -> foo" but it breaks dune coq.theory! *)
      | (None,d) -> Some d
      | (Some d1,d2) -> Some (filename_concat d1 d2)
  in
  let complete_name = file_name name dirname in
  let stat_res =
    try Unix.stat complete_name
    with Unix.Unix_error(error, _, _) ->
      Error.cannot_open complete_name (Unix.error_message error)
  in
  match stat_res.Unix.st_kind with
  | Unix.S_DIR ->
    (if name.[0] <> '.' then
       let newdirname =
         match dirname with
         | None -> name
         | Some d -> filename_concat d name
       in
       Array.iter (treat_file (Some newdirname)) (Sys.readdir complete_name))
  | Unix.S_REG ->
    (match Loadpath.get_extension name [".v"] with
     | base,".v" ->
       let name = file_name base dirname in
       let absname = Loadpath.absolute_file_name ~filename_concat base dirname in
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
          match Lexer.coq_action lb with
          | Lexer.Require (from, sl) ->
                List.iter
                  (fun s ->
                    match safe_assoc st from false file s with
                    | None -> ()
                    | Some l -> List.iter loop l)
                sl
            | _ -> ()
        done
      with Lexer.Fin_fichier ->
        close_in cin;
        Format.printf "%s.v " file
    end
  in
  List.iter (fun (name, _) -> loop name) !vAccu

let treat_coqproject st f =
  let open CoqProject_file in
  let iter_sourced f = List.iter (fun {thing} -> f thing) in
  let warning_fn x = Warning.give "%s" x in
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

let add_include st (rc, r, ln) =
  if rc then
    Loadpath.add_r_include st r ln
  else
    Loadpath.add_q_include st r ln

let init ~make_separator_hack args =
  separator_hack := make_separator_hack;
  vAccu := [];
  if not Coq_config.has_natdynlink then Makefile.set_dyndep "no";
  let st = Loadpath.State.make ~boot:args.Args.boot in
  Makefile.set_write_vos args.Args.vos;
  Makefile.set_noglob args.Args.noglob;
  Option.iter (treat_coqproject st) args.Args.coqproject;
  List.iter (Loadpath.add_caml_dir st) args.Args.ml_path;
  List.iter (add_include st) args.Args.vo_path;
  Makefile.set_dyndep args.Args.dyndep;
  meta_files := args.Args.meta_files;
  st
