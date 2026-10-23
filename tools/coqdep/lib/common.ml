(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* count newlines to get a nice error location instead of raw chars *)
let get_loc f { Lexer.loc_start = start; loc_end = end_ } =
  let ch = open_in f in
  let rec loop lnum bol read =
    if read = start then lnum, bol
    else match input_char ch with
      | '\n' -> loop (lnum+1) (read+1) (read+1)
      | _ -> loop lnum bol (read+1)
  in
  let lnum, bol = Fun.protect ~finally:(fun () -> close_in ch) (fun () -> loop 1 0 0) in
  { Loc.fname = InFile { dirpath=None; file=f };
    line_nb = lnum;
    bol_pos = bol;
    bp = start;
    ep = end_;

    (* not used by printing *)
    line_nb_last = 0;
    bol_pos_last = 0;
  }

(** Rocq files specifies on the command line:
    - first string is the full filename, with only its extension removed
    - second string is the absolute version of the previous (via getcwd)
*)
type vAccu = { acc : string list; map : string CString.Map.t }

let add_vAccu (f, f') vAccu =
  let acc = f :: vAccu.acc in
  let map = CString.Map.add f' f vAccu.map in
  { acc; map }

let empty_vAccu = { acc = []; map = CString.Map.empty }

let filename_concat ~separator_hack dir name =
  if separator_hack
  then System.(dir // name)
  else Filename.concat dir name

(* This is used to overcome makefile limitations w.r.t. filenames,
   (bar/../foo is not the same than ./foo for make) but it is a crude
   hack and we should remove it, and instead require users to follow
   the same naming convention *)
let canonize ~separator_hack vAccu f =
  let dir = Loadpath.Filename.dirname f in
  let f = Loadpath.Filename.repr f in
  let f' = filename_concat ~separator_hack
      dir
      (Filename.basename f)
  in
  match CString.Map.find_opt f' vAccu.map with
  | None -> f
  | Some f -> f

type what = Library | External
let str_of_what = function Library -> "library" | External -> "external file"

let warning_module_notfound =
  CWarnings.create ~name:"module-not-found"
    ~category:CWarnings.CoreCategories.filesystem
    ~default:AsError
    Pp.(fun (what, from, s) ->
        str (str_of_what what) ++ spc () ++ str (String.concat "." s) ++ str " is required" ++
        pr_opt (fun pth -> str "from root " ++ str (String.concat "." pth)) from ++
        str " and has not been found in the loadpath!")

let warn_if_clash ?(what=Library) exact file dir f1 = function
  | f2::fl ->
      let open Format in
      let f1 = Loadpath.Filename.repr f1 in
      let f2 = Loadpath.Filename.repr f2 in
      let fl = List.map Loadpath.Filename.repr fl in
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
  | Some (Loadpath.ExactMatches fs) ->
    let f = fs.Loadpath.point in
    let l = Loadpath.FileSet.remove f fs.files in
    let l = Loadpath.FileSet.elements l in
    if warn_clashes then warn_if_clash ~what true file k f l;
    Some [f]
  | Some (Loadpath.PartialMatchesInSameRoot (root, l)) ->
    let l = Loadpath.FileSet.elements l.files in
    let sort f1 f2 = String.compare (Loadpath.Filename.repr f1) (Loadpath.Filename.repr f2) in
    let all = List.sort sort l in
    let f, l = match all with [] -> assert false | f :: l -> f, l in
    (* If several files match, it will fail at Require;
       To be "fair", in rocq dep, we add dependencies on all matching files *)
    let () = if warn_clashes then warn_if_clash ~what false file k f l in
    Some all

let file_name ~separator_hack s = function
  | None     -> s
  | Some d   -> filename_concat ~separator_hack d s

module VData = struct
  type t = string list option * string list
  let cmp_list l1 l2 = List.compare String.compare l1 l2
  let compare (from1, str1) (from2, str2) =
    let c = Option.compare cmp_list from1 from2 in
    if Int.equal c 0 then cmp_list str1 str2 else c
end

module VCache = Set.Make(VData)

(** To avoid reading .v files several times for computing dependencies,
    once for .vo, and once for .vos extensions, the
    following code performs a single pass and produces a structured
    list of dependencies, separating dependencies on compiled Rocq files
    (those loaded by [Require]) from other dependencies, e.g. dependencies
    on ".v" files (for [Load]) or ".cmx", ".cmo", etc... (for [Declare]). *)

let coq_to_stdlib from strl =
  let tr_qualid = function
    | "Coq" :: l -> "Stdlib" :: l
    | l -> l in
  match from with
  | Some from -> Some (tr_qualid from), strl
  | None -> None, List.map (Util.on_snd tr_qualid) strl

let with_in_descr ~fname f =
  let descr =
    try Unix.openfile fname [O_RDONLY] 0o000
    with Unix.Unix_error (_, _, msg) -> Error.cannot_open fname msg
  in
  Util.try_finally f descr Unix.close descr

let lexbuf_from_descr ?with_positions ic =
  Lexing.from_function ?with_positions (fun buf n -> Unix.read ic buf 0 n)

module State = struct
  type t = {
    loadpath : Loadpath.State.t;
    separator_hack : bool;
    vAccu : vAccu;
  }
  let loadpath x = x.loadpath
end

(* recursive because of Load *)
let rec find_dependencies ({State.vAccu; separator_hack; loadpath} as st) basename =
  (* Visited marks *)
  let visited_package = ref CString.Set.empty in
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

  (* Reading file contents *)
  let f = basename ^ ".v" in
  with_in_descr ~fname:f @@ fun chan ->
  (* For lexing efficiency purposes, we ignore the positions in this function.
     We can still get accurate character counts, we're just missing newline info. *)
  let buf = lexbuf_from_descr ~with_positions:false chan in
  let open Lexer in
  let rec loop () =
    match coq_action buf with
    | exception Fin_fichier ->
      DepSet.elements !dependencies
    | exception Syntax_error loc ->
      (* The locations are garbage due to with_positions:false, ignore them *)
      Error.cannot_parse ~loc:(get_loc f loc)
    | tok ->  match tok with
      | Require (from, strl) ->
        let from, strl = coq_to_stdlib from strl in
        let decl (loc, str) =
          if should_visit_v_and_mark from str then begin
            let files = safe_assoc loadpath from f str in
            let files = match from, files with
              | Some _, _ | None, Some _ -> files
              | None, None -> safe_assoc loadpath (Some ["Stdlib"]) f str in
            match files with
            | Some files ->
              List.iter (fun file_str ->
                  let file_str = canonize ~separator_hack vAccu file_str in
                  add_dep (Dep_info.Dep.Require file_str)) files
            | None ->
              if not (Loadpath.is_in_coqlib loadpath ?from str) then
                warning_module_notfound ~loc:(get_loc f loc) (Library, from, str)
          end
        in
        List.iter decl strl;
        loop ()
      | Declare sl ->
        let decl dep =
          if not (CString.Set.mem dep !visited_package) then begin
            visited_package := CString.Set.add dep !visited_package;
            add_dep (Dep_info.Dep.Ml dep)
          end
        in
        List.iter decl sl;
        loop ()
      | Load file ->
        let canon =
          match file with
          | Logical str ->
            if should_visit_v_and_mark None [str] then safe_assoc loadpath None f [str]
            else None
          | Physical str ->
            if String.equal (Filename.basename str) str then
              if should_visit_v_and_mark None [str] then safe_assoc loadpath None f [str]
              else None
            else
              let ans = canonize ~separator_hack vAccu (Loadpath.Filename.make str) in
              Some [Loadpath.Filename.make ans]
        in
        (match canon with
         | None -> ()
         | Some l ->
           let decl canon =
             let canon = Loadpath.Filename.repr canon in
             add_dep_other (Format.sprintf "%s.v" canon);
             let deps = find_dependencies st canon in
             List.iter add_dep deps
           in
           List.iter decl l);
        loop ()
      | External(loc,from,str) ->
        begin match safe_assoc loadpath ~what:External (Some from) f [str] with
        | Some (file :: _) -> add_dep (Dep_info.Dep.Other (canonize ~separator_hack vAccu file))
        | Some [] -> assert false
        | None ->
          if not (Loadpath.is_other_in_coqlib loadpath ~from [str]) then
            warning_module_notfound ~loc:(get_loc f loc) (External, Some from, [str])
        end;
        loop ()
  in
  loop ()

let compute_deps st =
  let mk_dep name = Dep_info.make ~name ~deps:(find_dependencies st name) in
  List.rev st.vAccu.acc |> List.to_seq |> Seq.map mk_dep

let rec treat_file ~separator_hack vAccu old_dirname old_name =
  let name = Filename.basename old_name
  and new_dirname = Filename.dirname old_name in
  let dirname =
    match (old_dirname,new_dirname) with
    | (d, ".") -> d
    (* EGJA: We should disable this buggy normalization stuff for
       "./foo -> foo" but it breaks dune coq.theory! *)
    | (None,d) -> Some d
    | (Some d1,d2) -> Some (filename_concat ~separator_hack d1 d2)
  in
  let complete_name = file_name ~separator_hack name dirname in
  let stat_res =
    try Unix.stat complete_name
    with Unix.Unix_error(error, _, _) ->
      Error.cannot_open complete_name (Unix.error_message error)
  in
  match stat_res.Unix.st_kind with
  | Unix.S_DIR ->
    (if name.[0] = '.' then vAccu else
       let newdirname =
         match dirname with
         | None -> name
         | Some d -> filename_concat ~separator_hack d name
       in
       Array.fold_left (fun vAccu x -> treat_file ~separator_hack vAccu (Some newdirname) x) vAccu
         (Sys.readdir complete_name))
  | Unix.S_REG ->
    (match Loadpath.get_extension name [".v"] with
     | base,".v" ->
       let name = file_name ~separator_hack base dirname in
       let filename_concat = filename_concat ~separator_hack in
       let absname = Loadpath.absolute_file_name ~filename_concat base dirname in
       add_vAccu (name, absname) vAccu
     | _ -> vAccu)
  | _ -> vAccu

let treat_file_command_line ({State.vAccu; separator_hack} as st) old_name =
  let vAccu = treat_file ~separator_hack vAccu None old_name in
  { st with State.vAccu }

(* "[sort]" outputs `.v` files required by others *)
let sort {State.vAccu; separator_hack; loadpath} =
  let seen = Hashtbl.create 97 in
  let rec loop file =
    let file = canonize ~separator_hack vAccu file in
    if not (Hashtbl.mem seen file) then begin
      Hashtbl.add seen file ();
      let cin = open_in (file ^ ".v") in
      let lb = Lexing.from_channel cin in
      try
        while true do
          match Lexer.coq_action lb with
          | Lexer.Require (from, sl) ->
                List.iter
                  (fun (_,s) ->
                    match safe_assoc loadpath from ~warn_clashes:false file s with
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
  List.iter (fun name -> loop (Loadpath.Filename.make name)) vAccu.acc

let add_include st (rc, r, ln) =
  if rc then
    Loadpath.add_r_include st r ln
  else
    Loadpath.add_q_include st r ln

let add_packages st ps =
  let add_package p =
    Loadpath.add_q_include st p.Rocq_package.dir p.Rocq_package.logpath
  in
  List.iter add_package (Rocq_package.resolve ps)

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
  if not Coq_config.has_natdynlink then Makefile.set_dyndep "no";
  let loadpath = Loadpath.State.make ~worker:args.Args.worker ~boot:args.Args.boot in
  Makefile.set_write_vos args.Args.vos;
  Makefile.set_noglob args.Args.noglob;
  (* Add to the findlib search path, common with sysinit/coqinit *)
  let ml_path = args.Args.ml_path in
  let rocqenv = Boot.Env.maybe_init ~boot:args.boot ~coqlib:args.coqlib
      ~warn_ignored_coqlib:CWarnings.warn_ignored_coqlib
  in
  let ml_path = match rocqenv with
    | Boot -> ml_path
    | Env env ->
      ml_path @ Boot.Env.Path.[to_string @@ relative (Boot.Env.runtimelib env) ".."]
  in
  findlib_init ml_path;
  add_packages loadpath args.Args.packages;
  List.iter (add_include loadpath) args.Args.vo_path;
  Makefile.set_dyndep args.Args.dyndep;
  rocqenv, { State.vAccu = empty_vAccu; loadpath; separator_hack = make_separator_hack }
