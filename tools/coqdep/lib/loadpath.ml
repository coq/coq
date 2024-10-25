(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Common types *)
type basename = string
type dirname = string
type dir = string option
type dirpath = string list
type filename = string
type root = filename * dirpath

(** File operations *)
let absolute_dir dir =
  let current = Sys.getcwd () in
    Sys.chdir dir;
    let dir' = Sys.getcwd () in
      Sys.chdir current;
      dir'

let absolute_file_name ~filename_concat basename odir =
  let dir = match odir with Some dir -> dir | None -> "." in
  (* XXX: Attention to System.(//) which does weird things and it is
     not the same than Filename.concat ; using Filename.concat here
     makes the windows build fail *)
  filename_concat (absolute_dir dir) basename

let equal_file f1 f2 =
  let filename_concat = Filename.concat in
  String.equal
    (absolute_file_name ~filename_concat (Filename.basename f1) (Some (Filename.dirname f1)))
    (absolute_file_name ~filename_concat (Filename.basename f2) (Some (Filename.dirname f2)))

(** [find_dir_logpath dir] Return the logical path of directory [dir]
    if it has been given one. Raise [Not_found] otherwise. In
    particular we can check if "." has been attributed a logical path
    after processing all options and silently give the default one if
    it hasn't. We may also use this to warn if a physical path is met
    twice. *)
let register_dir_logpath, find_dir_logpath =
  let tbl: (string, string list) Hashtbl.t = Hashtbl.create 19 in
  let reg physdir logpath = Hashtbl.add tbl (absolute_dir physdir) logpath in
  let fnd physdir = Hashtbl.find tbl (absolute_dir physdir) in
  reg,fnd

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
    if System.exists_dir phys_dir then
      begin
        register_dir_logpath phys_dir log_dir;
        let f = function
          | System.FileDir (phys_f,f) ->
              if recur then begin
                stack := (!curdirfiles, !subdirfiles) :: !stack;
                curdirfiles := []; subdirfiles := [];
                aux phys_f (log_dir @ [f]);
                let curdirfiles', subdirfiles' = List.hd !stack in
                subdirfiles := subdirfiles' @ !subdirfiles @ !curdirfiles;
                curdirfiles := curdirfiles'; stack := List.tl !stack
              end
          | System.FileRegular f ->
              curdirfiles := (phys_dir, log_dir, f) :: !curdirfiles
        in
        System.process_directory f phys_dir
      end
    else
      System.warn_cannot_open_dir phys_dir
  in
  aux phys_dir log_dir;
  List.iter (fun (phys_dir, log_dir, f) -> add_file root phys_dir log_dir f) !subdirfiles;
  List.iter (fun (phys_dir, log_dir, f) -> add_file root phys_dir log_dir f) !curdirfiles

(** [get_extension f l] checks whether [f] has one of the extensions
    listed in [l]. It returns [f] without its extension, alongside with
    the extension. When no extension match, [(f,"")] is returned *)

let rec get_extension f = function
  | [] -> (f, "")
  | s :: _ when Filename.check_suffix f s -> (Filename.chop_suffix f s, s)
  | _ :: l -> get_extension f l

(** Compute the suffixes of a logical path together with the length of the missing part *)
let rec suffixes full = function
  | [] -> assert false
  | [name] -> [full,[name]]
  | dir::suffix as l -> (full,l)::suffixes false suffix

(** Compute all the pairs [(from,suffs)] such that a logical path
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

type result =
  | ExactMatches of filename list
  | PartialMatchesInSameRoot of root * filename list

module State = struct

  type t =
    { vfiles : (dirpath * dirpath, result) Hashtbl.t
    ; coqlib : (dirpath * dirpath, result) Hashtbl.t
    ; other : (dirpath * dirpath, result) Hashtbl.t
    ; boot : bool
    ; mutable worker : string option
    }

  let make ~worker ~boot =
    { vfiles = Hashtbl.create 4101
    ; coqlib = Hashtbl.create 19
    ; other = Hashtbl.create 17317
    ; boot
    ; worker
    }

end

let get_worker_path st =
  match st.State.worker with
  | Some w -> w
  | None ->
    let w = Fl.Internal.get_worker_path () in
    st.worker <- Some w;
    w

let add_set f l = f :: CList.remove equal_file f l

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

let search_table table ?(from=[]) s =
  Hashtbl.find table (from, s)

let search_v_known st ?from s =
  try Some (search_table st.State.vfiles ?from s)
  with Not_found -> None

let search_other_known st ?from s =
  try Some (search_table st.State.other ?from s)
  with Not_found -> None

let is_in_coqlib st ?from s =
  try let _ = search_table st.State.coqlib ?from s in true
  with Not_found -> match from with Some _ -> false | None ->
  try let _ = search_table st.State.coqlib ~from:["Stdlib"] s in true
  with Not_found -> false

let add_paths recur root table phys_dir log_dir basename =
  let name = log_dir@[basename] in
  let file = System.(phys_dir // basename) in
  let paths = cuts recur name in
  let iter n = safe_add table root (n, file) in
  List.iter iter paths

let add_coqlib_known st recur root phys_dir log_dir f =
  let root = (phys_dir, log_dir) in
  match get_extension f [".vo"; ".vos"] with
    | (basename, (".vo" | ".vos")) ->
        add_paths recur root st.State.coqlib phys_dir log_dir basename
    | _ -> ()

let add_known st recur root phys_dir log_dir f =
  match get_extension f [".v"; ".vo"; ".vos"] with
    | (basename,".v") ->
        add_paths recur root st.State.vfiles phys_dir log_dir basename
    | (basename, (".vo" | ".vos")) when not st.State.boot ->
        add_paths recur root st.State.vfiles phys_dir log_dir basename
    | (f,_) ->
        add_paths recur root st.State.other phys_dir log_dir f

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

let split_period = Str.split (Str.regexp (Str.quote "."))

let add_current_dir st dir = add_norec_dir_import (add_known st) dir []
let add_q_include st path l = add_rec_dir_no_import (add_known st) path (split_period l)
let add_r_include st path l = add_rec_dir_import (add_known st) path (split_period l)
