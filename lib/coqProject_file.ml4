(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type project = {
  project_file  : string option;
  makefile : string option;
  install_kind  : install option;
  use_ocamlopt : bool;

  v_files : string list;
  mli_files : string list;
  ml4_files : string list;
  ml_files : string list;
  mllib_files : string list;
  mlpack_files : string list;

  ml_includes : path list;
  r_includes  : (path * logic_path) list;
  q_includes  : (path * logic_path) list;
  extra_args : string list;
  defs : (string * string) list;
  
  extra_targets : extra_target list;
  subdirs : string list;

  cmdline_vfiles : string list;
}
and extra_target = {
  target : string;
  dependencies : string;
  phony : bool;
  command : string;
}
and logic_path = string
and path = { path : string; canonical_path : string }
and install =
  | NoInstall
  | TraditionalInstall
  | UserInstall

(* TODO generate with PPX *)
let mk_project project_file makefile install_kind use_ocamlopt = {
  project_file;
  makefile;
  install_kind;
  use_ocamlopt;

  v_files = [];
  mli_files = [];
  ml4_files = [];
  ml_files = [];
  mllib_files = [];
  mlpack_files = [];
  extra_targets = [];
  subdirs = [];
  ml_includes = [];
  r_includes = [];
  q_includes = [];
  extra_args = [];
  defs = [];
  cmdline_vfiles = [];
}

(********************* utils ********************************************)

let rec post_canonize f =
  if Filename.basename f = Filename.current_dir_name
  then let dir = Filename.dirname f in
    if dir = Filename.current_dir_name then f else post_canonize dir
  else f

(********************* parser *******************************************)

exception Parsing_error of string

let rec parse_string = parser
  | [< '' ' | '\n' | '\t' >] -> ""
  | [< 'c; s >] -> (String.make 1 c)^(parse_string s)
  | [< >] -> ""
and parse_string2 = parser
  | [< ''"' >] -> ""
  | [< 'c; s >] -> (String.make 1 c)^(parse_string2 s)
  | [< >] -> raise (Parsing_error "unterminated string")
and parse_skip_comment = parser
  | [< ''\n'; s >] -> s
  | [< 'c; s >] -> parse_skip_comment s
  | [< >] -> [< >]
and parse_args = parser
  | [< '' ' | '\n' | '\t'; s >] -> parse_args s
  | [< ''#'; s >] -> parse_args (parse_skip_comment s)
  | [< ''"'; str = parse_string2; s >] -> ("" ^ str) :: parse_args s
  | [< 'c; str = parse_string; s >] -> ((String.make 1 c) ^ str) :: (parse_args s)
  | [< >] -> []

let parse f =
  let c = open_in f in
  let res = parse_args (Stream.of_channel c) in
  close_in c;
  res
;;

(* Copy from minisys.ml, since we don't see that file here *)
let exists_dir dir =
  let rec strip_trailing_slash dir =
    let len = String.length dir in
    if len > 0 && (dir.[len-1] = '/' || dir.[len-1] = '\\')
    then strip_trailing_slash (String.sub dir 0 (len-1)) else dir in
  try Sys.is_directory (strip_trailing_slash dir) with Sys_error _ -> false


let process_cmd_line orig_dir proj args =
  let parsing_project_file = ref (proj.project_file <> None) in
  let orig_dir = (* avoids turning foo.v in ./foo.v *)
    if orig_dir = "." then "" else orig_dir in
  let error s = Format.eprintf "@[%a]@@\n%!" Pp.pp_with Pp.(str (s^".")); exit 1 in
  let mk_path d =
    let p = CUnix.correct_path d orig_dir in
    { path = CUnix.remove_path_dot (post_canonize p);
      canonical_path = CUnix.canonical_path_name p } in
  let rec aux proj = function
  | [] -> proj
  | "-impredicative-set" :: _ ->
    error "Use \"-arg -impredicative-set\" instead of \"-impredicative-set\""
  | "-no-install" :: _ ->
    error "Use \"-install none\" instead of \"-no-install\""
  | "-custom" :: _ ->
    error "Use \"-extra[-phony] target deps command\" instead of \"-custom command deps target\""
  
  | ("-no-opt"|"-byte") :: r -> aux { proj with use_ocamlopt =  false } r
  | ("-full"|"-opt") :: r -> aux { proj with use_ocamlopt =  true } r
  | "-install" :: d :: r ->
    if proj.install_kind <> None then
      Feedback.msg_warning (Pp.str "-install set more than once.");
    let install = match d with
      | "user" -> UserInstall
      | "none" -> NoInstall
      | "global" -> TraditionalInstall
      | _ -> error ("invalid option \""^d^"\" passed to -install") in
    aux { proj with install_kind = Some install } r
  | "-extra" :: target :: dependencies :: command :: r ->
    let tgt = { target; dependencies; phony = false; command } in
    aux { proj with extra_targets = proj.extra_targets @ [tgt] } r
  | "-extra-phony" :: target :: dependencies :: command :: r ->
    let tgt = { target; dependencies; phony = true; command } in
    aux { proj with extra_targets = proj.extra_targets @ [tgt] } r

  | "-Q" :: d :: lp :: r ->
    aux { proj with q_includes = proj.q_includes @ [mk_path d,lp] } r
  | "-I" :: d :: r ->
    aux { proj with ml_includes = proj.ml_includes @ [mk_path d] } r
  | "-R" :: d :: lp :: r ->
    aux { proj with r_includes = proj.r_includes @ [mk_path d,lp] } r

  | "-f" :: file :: r ->
    if !parsing_project_file then
      raise (Parsing_error ("Invalid option -f in project file " ^ Option.get proj.project_file));
    let file = CUnix.remove_path_dot (CUnix.correct_path file orig_dir) in
    let () = match proj.project_file with
      | None -> ()
      | Some _ -> Feedback.msg_warning (Pp.str
	"Multiple project files are deprecated.")
    in
    parsing_project_file := true;
    let proj = aux { proj with project_file = Some file } (parse file) in
    parsing_project_file := false;
    aux proj r

  | "-o" :: file :: r ->
    if !parsing_project_file then
     raise (Parsing_error ("Invalid option -o in project file " ^ Option.get proj.project_file));
    if String.contains file '/' then
      error "Output file must be in the current directory";
    if proj.makefile <> None then
      error "Option -o given more than once";
    aux { proj with makefile = Some file } r  
  | v :: "=" :: def :: r ->
    aux { proj with defs = proj.defs @ [v,def] } r
  | "-arg" :: a :: r ->
    aux { proj with extra_args = proj.extra_args @ [a] } r
  | f :: r ->
      let f = CUnix.correct_path f orig_dir in
      let proj =
        if exists_dir f then { proj with subdirs = proj.subdirs @ [f] }
        else match CUnix.get_extension f with
          | ".v" ->
            let { cmdline_vfiles } = proj in
            let cmdline_vfiles = if !parsing_project_file
              then cmdline_vfiles
              else cmdline_vfiles @ [f]
            in
            { proj with v_files = proj.v_files @ [f]; cmdline_vfiles }
        | ".ml" -> { proj with ml_files = proj.ml_files @ [f] }
        | ".ml4" -> { proj with ml4_files = proj.ml4_files @ [f] }
        | ".mli" -> { proj with mli_files = proj.mli_files @ [f] }
        | ".mllib" -> { proj with mllib_files = proj.mllib_files @ [f] }
        | ".mlpack" -> { proj with mlpack_files = proj.mlpack_files @ [f] }
        | _ -> raise (Parsing_error ("Unknown option "^f)) in
      aux proj r
 in
   aux proj args

 (******************************* API ************************************)

let cmdline_args_to_project ~curdir args =
  process_cmd_line curdir (mk_project None None None true) args

let read_project_file f =
  process_cmd_line (Filename.dirname f)
    (mk_project (Some f) None (Some NoInstall) true) (parse f)

let rec find_project_file ~from ~projfile_name =
  let fname = Filename.concat from projfile_name in
  if Sys.file_exists fname then Some fname
  else
    let newdir = Filename.dirname from in
    if newdir = from then None
    else find_project_file ~from:newdir ~projfile_name
;;

let coqtop_args_from_project
  { ml_includes; r_includes; q_includes; extra_args }
=
  let map = List.map in
  let args =
    map (fun { canonical_path = i } -> ["-I"; i]) ml_includes @
    map (fun ({ canonical_path = i }, l) -> ["-Q"; i; l]) q_includes @
    map (fun ({ canonical_path = p }, l) -> ["-R"; p; l]) r_includes @
    [extra_args] in
  List.flatten args
;;

(* vim:set ft=ocaml: *)
