(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module StrSet = Set.Make(String)

(** Rocq files specifies on the command line:
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

let warning_module_notfound =
  let warn (what, from, f, s) =
    let open Pp in
    str "in file " ++ str f ++ str ", " ++
    str (str_of_what what) ++ spc () ++ str (String.concat "." s) ++ str " is required" ++
    pr_opt (fun pth -> str "from root " ++ str (String.concat "." pth)) from ++
    str " and has not been found in the loadpath!"
  in
  CWarnings.create ~name:"module-not-found"
    ~category:CWarnings.CoreCategories.filesystem warn

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

let safe_assoc ?(warn_clashes=true) st ?(what=Library) from file k =
  let search =
    match what with
    | Library -> Loadpath.search_v_known st
    | External -> Loadpath.search_other_known st in
  match search ?from k with
  | None -> None
  | Some (Loadpath.ExactMatches (f :: l)) ->
    if warn_clashes then warn_if_clash ~what true file k f l;
    Some [f]
  | Some (Loadpath.PartialMatchesInSameRoot (root, l)) ->
    (match List.sort String.compare l with [] -> assert false | f :: l as all ->
    (* If several files match, it will fail at Require;
       To be "fair", in rocq dep, we add dependencies on all matching files *)
    if warn_clashes then warn_if_clash ~what false file k f l;
    Some all)
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
    once for .vo, and once for .vos extensions, the
    following code performs a single pass and produces a structured
    list of dependencies, separating dependencies on compiled Rocq files
    (those loaded by [Require]) from other dependencies, e.g. dependencies
    on ".v" files (for [Load]) or ".cmx", ".cmo", etc... (for [Declare]). *)

(* Transform "Declare ML %DECL" to a pair of (meta, cmxs). Something
   very similar is in ML top *)
let declare_ml_to_file file (decl : string) =
  let legacy_decl = String.split_on_char ':' decl in
  match legacy_decl with
  | [package] ->
    Fl.findlib_deep_resolve ~file ~package
  | [cmxs; package] ->
    (* rocq compile will warn *)
    Fl.findlib_deep_resolve ~file ~package
  | bad_pkg ->
    CErrors.user_err Pp.(str "Failed to resolve plugin: " ++ str decl)

let coq_to_stdlib from strl =
  let tr_qualid = function
    | "Coq" :: l -> "Stdlib" :: l
    | l -> l in
  match from with
  | Some from -> Some (tr_qualid from), strl
  | None -> None, List.map tr_qualid strl

let with_in_channel ~fname f =
  let chan = try open_in fname
    with Sys_error msg -> Error.cannot_open fname msg
  in
  Util.try_finally f chan close_in chan

(* recursive because of Load *)
let rec find_dependencies st basename =
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
  let module DepSet = Dep_info.Dep.Set in
  let dependencies = ref DepSet.empty in
  let add_dep dep = dependencies := DepSet.add dep !dependencies in
  let add_dep_other s = add_dep (Dep_info.Dep.Other s) in

  (* worker dep *)
  let () = add_dep_other (Loadpath.get_worker_path st) in

  (* Reading file contents *)
  let f = basename ^ ".v" in
  with_in_channel ~fname:f @@ fun chan ->
  let buf = Lexing.from_channel chan in
  let open Lexer in
  let rec loop () =
    match coq_action buf with
    | exception Fin_fichier ->
      DepSet.elements !dependencies
    | exception Syntax_error (i,j) ->
      Error.cannot_parse f (i,j)
    | tok ->  match tok with
      | Require (from, strl) ->
        let from, strl = coq_to_stdlib from strl in
        let decl str =
          if should_visit_v_and_mark from str then begin
            let files = safe_assoc st from f str in
            let files = match from, files with
              | Some _, _ | None, Some _ -> files
              | None, None -> safe_assoc st (Some ["Stdlib"]) f str in
            match files with
            | Some files ->
              List.iter (fun file_str ->
                  let file_str = canonize file_str in
                  add_dep (Dep_info.Dep.Require file_str)) files
            | None ->
              if not (Loadpath.is_in_coqlib st ?from str) then
                warning_module_notfound (Library, from, f, str)
          end
        in
        List.iter decl strl;
        loop ()
      | Declare sl ->
        (* We resolve "pkg_name" to a .cma file, using the META *)
        let sl = List.map (declare_ml_to_file f) sl in
        let decl (meta_file, str) =
          List.iter add_dep_other meta_file;
          str |> List.iter (fun str ->
          let plugin_file = Filename.chop_extension str in
          if not (StrSet.mem plugin_file !visited_ml) then begin
            visited_ml := StrSet.add plugin_file !visited_ml;
            add_dep (Dep_info.Dep.Ml plugin_file)
          end)
        in
        List.iter decl sl;
        loop ()
      | Load file ->
        let canon =
          match file with
          | Logical str ->
            if should_visit_v_and_mark None [str] then safe_assoc st None f [str]
            else None
          | Physical str ->
            if String.equal (Filename.basename str) str then
              if should_visit_v_and_mark None [str] then safe_assoc st None f [str]
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
           List.iter decl l);
        loop ()
      | External(from,str) ->
        begin match safe_assoc st ~what:External (Some from) f [str] with
        | Some (file :: _) -> add_dep (Dep_info.Dep.Other (canonize file))
        | Some [] -> assert false
        | None -> warning_module_notfound (External, Some from, f, [str])
        end;
        loop ()
  in
  loop ()

module State = struct
  type t = Loadpath.State.t
  let loadpath x = x
end

let compute_deps st =
  let mk_dep (name, _orig_path) = Dep_info.make ~name ~deps:(find_dependencies st name) in
  !vAccu |> CList.rev_map mk_dep

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
                    match safe_assoc st from ~warn_clashes:false file s with
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

let add_include st (rc, r, ln) =
  if rc then
    Loadpath.add_r_include st r ln
  else
    Loadpath.add_q_include st r ln

let findlib_init dirs =
  let env_ocamlpath =
    try [Sys.getenv "OCAMLPATH"]
    with Not_found -> []
  in
  let env_ocamlpath = dirs @ env_ocamlpath in
  let ocamlpathsep = if Sys.unix then ":" else ";" in
  let env_ocamlpath = String.concat ocamlpathsep env_ocamlpath in
  Findlib.init ~env_ocamlpath ()

let init ~make_separator_hack args =
  separator_hack := make_separator_hack;
  vAccu := [];
  if not Coq_config.has_natdynlink then Makefile.set_dyndep "no";
  let st = Loadpath.State.make ~worker:args.Args.worker ~boot:args.Args.boot in
  Makefile.set_write_vos args.Args.vos;
  Makefile.set_noglob args.Args.noglob;
  (* Add to the findlib search path, common with sysinit/coqinit *)
  let ml_path = args.Args.ml_path in
  let ml_path =
    if args.Args.boot then ml_path
    else
      let env = Boot.Env.init () in
      Boot.Env.Path.(to_string @@ relative (Boot.Env.corelib env) "..") :: ml_path
  in
  findlib_init ml_path;
  List.iter (add_include st) args.Args.vo_path;
  Makefile.set_dyndep args.Args.dyndep;
  st
