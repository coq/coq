(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t =
  { boot : bool
  ; sort : bool
  ; vos : bool
  ; noglob : bool
  ; ml_path : string list
  ; vo_path : (bool * string * string) list
  ; dyndep : string
  ; worker : string option
  ; files : string list
  }

let make () =
  { boot = false
  ; sort = false
  ; vos = false
  ; noglob = false
  ; ml_path = []
  ; vo_path = []
  ; dyndep = "both"
  ; worker = None
  ; files = []
  }


let warn_unknown_option =
  CWarnings.create ~name:"unknown-option"
    Pp.(fun opt -> str "Unknown option \"" ++ str opt ++ str "\".")

let usage () =
  let open Printf in
  eprintf " usage: rocq dep [options] <filename>+\n";
  eprintf " options:\n";
  eprintf "  -boot : For rocq developers, prints dependencies over rocq library files (omitted by default).\n";
  eprintf "  -sort : output the given file name ordered by dependencies\n";
  eprintf "  -noglob | -no-glob : \n";
  eprintf "  -noinit : currently no effect\n";
  eprintf "  -f file : read -I, -Q, -R and filenames from _CoqProject-formatted file.\n";
  eprintf "  -I dir : add (non recursively) dir to ocaml path\n";
  eprintf "  -R dir logname : add and import dir recursively to rocq load path under logical name logname\n";
  eprintf "  -Q dir logname : add (recursively) and open (non recursively) dir to rocq load path under logical name logname\n";
  eprintf "  -vos : also output dependencies about .vos files\n";
  eprintf "  -exclude-dir dir : skip subdirectories named 'dir' during -R/-Q search\n";
  eprintf "  -coqlib dir : set the rocq core library directory\n";
  eprintf "  -dyndep (opt|byte|both|no|var) : set how dependencies over ML modules are printed\n";
  eprintf "  -worker WORKER : output WORKER instead of the rocqworker path\n";
  eprintf "  -w (w1,..,wn) : configure display of warnings\n";
  eprintf "%!"; (* flush *)
  exit 1

let warn_project_file =
  let category = CWarnings.CoreCategories.filesystem in
  CWarnings.create ~name:"project-file" ~category Pp.str

let add_ml_path st f = { st with ml_path = f :: st.ml_path }

let add_vo_path st (isr,path,logic) =
  let logic = if String.equal logic "Coq" then "Corelib" else logic in
  { st with vo_path = (isr,path,logic) :: st.vo_path }

let add_file st f = { st with files = f :: st.files }

let add_from_coqproject st f =
  let open CoqProject_file in
  let fold_sourced f acc l = List.fold_left (fun acc {thing} -> f acc thing) acc l in
  let project =
    try read_project_file ~warning_fn:warn_project_file f
    with
    | Parsing_error msg -> Error.cannot_parse_project_file f msg
    | UnableToOpenProjectFile msg -> Error.cannot_open_project_file msg
  in
  let st = fold_sourced (fun st { path } -> add_ml_path st path) st project.ml_includes in
  let st = fold_sourced (fun st ({path}, l) -> add_vo_path st (false,path,l)) st project.q_includes in
  let st = fold_sourced (fun st ({path}, l) -> add_vo_path st (true,path,l)) st project.r_includes in
  let st = fold_sourced add_file st (all_files project) in
  st

let parse st args =
  let rec parse st =
    function
    | "-boot" :: ll -> parse { st with boot = true } ll
    | "-sort" :: ll -> parse { st with sort = true } ll
    | "-vos" :: ll -> parse { st with vos = true } ll
    | ("-noglob" | "-no-glob") :: ll -> parse { st with noglob = true } ll
    | "-noinit" :: ll -> (* do nothing *) parse st ll
    | "-f" :: f :: ll -> parse (add_from_coqproject st f) ll
    | "-I" :: r :: ll -> parse (add_ml_path st r) ll
    | "-I" :: [] -> usage ()
    | "-R" :: r :: ln :: ll -> parse (add_vo_path st (true, r, ln)) ll
    | "-Q" :: r :: ln :: ll -> parse (add_vo_path st (false, r, ln)) ll
    | ("-Q"|"-R") :: ([] | [_]) -> usage ()
    | "-exclude-dir" :: r :: ll -> System.exclude_directory r; parse st ll
    | "-exclude-dir" :: [] -> usage ()
    | "-coqlib" :: r :: ll -> Boot.Env.set_coqlib r; parse st ll
    | "-coqlib" :: [] -> usage ()
    | "-dyndep" :: dyndep :: ll -> parse { st with dyndep } ll
    | "-worker" :: w :: ll -> parse { st with worker = Some w } ll
    | "-w" :: w :: ll ->
      let w = if w = "none" then w else CWarnings.get_flags() ^ "," ^ w in
      CWarnings.set_flags w;
      parse st ll
    | ("-h"|"--help"|"-help") :: _ -> usage ()
    | opt :: ll when String.length opt > 0 && opt.[0] = '-' ->
      warn_unknown_option opt;
      parse st ll
    | f :: ll -> parse (add_file st f) ll
    | [] -> st
  in
  let st = parse st args in
  { st with
    ml_path = List.rev st.ml_path
  ; vo_path = List.rev st.vo_path
  ; files = List.rev st.files
  }
