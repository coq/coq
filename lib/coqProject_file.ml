(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This needs to go trou feedback as it is invoked from IDEs, but
   ideally we would like to make this independent so it can be
   bootstrapped. *)

(* Note the problem with the error invokation below calling exit... *)
(* let error msg = Feedback.msg_error msg *)
let warning msg = Feedback.msg_warning Pp.(str msg)

type arg_source = CmdLine | ProjectFile

type 'a sourced = { thing : 'a; source : arg_source }

type project = {
  project_file  : string option;
  makefile : string option;
  install_kind  : install option;
  use_ocamlopt : bool;

  v_files : string sourced list;
  mli_files : string sourced list;
  ml4_files : string sourced list;
  ml_files : string sourced list;
  mllib_files : string sourced list;
  mlpack_files : string sourced list;

  ml_includes : path sourced list;
  r_includes  : (path * logic_path) sourced list;
  q_includes  : (path * logic_path) sourced list;
  extra_args : string sourced list;
  defs : (string * string) sourced list;

  (* deprecated in favor of a Makefile.local using :: rules *)
  extra_targets : extra_target sourced list;
  subdirs : string sourced list;
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
}

(********************* utils ********************************************)

let rec post_canonize f =
  if Filename.basename f = Filename.current_dir_name
  then let dir = Filename.dirname f in
    if dir = Filename.current_dir_name then f else post_canonize dir
  else f

(********************* parser *******************************************)

exception Parsing_error of string

let buffer buf =
  let ans = Buffer.contents buf in
  let () = Buffer.clear buf in
  ans

let rec parse_string buf s = match Stream.next s with
| ' ' | '\n' | '\t' -> buffer buf
| c ->
  let () = Buffer.add_char buf c in
  parse_string buf s
| exception Stream.Failure -> buffer buf

and parse_string2 buf s = match Stream.next s with
| '"' -> buffer buf
| c ->
  let () = Buffer.add_char buf c in
  parse_string2 buf s
| exception Stream.Failure -> raise (Parsing_error "unterminated string")

and parse_skip_comment s = match Stream.next s with
| '\n' -> ()
| _ -> parse_skip_comment s
| exception Stream.Failure -> ()

and parse_args buf accu s = match Stream.next s with
| ' ' | '\n' | '\t' -> parse_args buf accu s
| '#' ->
  let () = parse_skip_comment s in
  parse_args buf accu s
| '"' ->
  let str = parse_string2 buf s in
  parse_args buf (str :: accu) s
| c ->
  let () = Buffer.add_char buf c in
  let str = parse_string buf s in
  parse_args buf (str :: accu) s
| exception Stream.Failure -> accu

let parse f =
  let c = open_in f in
  let buf = Buffer.create 64 in
  let res = parse_args buf [] (Stream.of_channel c) in
  close_in c;
  List.rev res
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
  let sourced x = { thing = x; source = if !parsing_project_file then ProjectFile else CmdLine } in
  let orig_dir = (* avoids turning foo.v in ./foo.v *)
    if orig_dir = "." then "" else orig_dir in
  let error s = (Format.eprintf "Error: @[%s@].@\n%!" s; exit 1) in
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
      (warning "-install set more than once.@\n%!");
    let install = match d with
      | "user" -> UserInstall
      | "none" -> NoInstall
      | "global" -> TraditionalInstall
      | _ -> error ("invalid option \""^d^"\" passed to -install") in
    aux { proj with install_kind = Some install } r
  | "-extra" :: target :: dependencies :: command :: r ->
    let tgt = { target; dependencies; phony = false; command } in
    aux { proj with extra_targets = proj.extra_targets @ [sourced tgt] } r
  | "-extra-phony" :: target :: dependencies :: command :: r ->
    let tgt = { target; dependencies; phony = true; command } in
    aux { proj with extra_targets = proj.extra_targets @ [sourced tgt] } r

  | "-Q" :: d :: lp :: r ->
    aux { proj with q_includes = proj.q_includes @ [sourced (mk_path d,lp)] } r
  | "-I" :: d :: r ->
    aux { proj with ml_includes = proj.ml_includes @ [sourced (mk_path d)] } r
  | "-R" :: d :: lp :: r ->
    aux { proj with r_includes = proj.r_includes @ [sourced (mk_path d,lp)] } r

  | "-f" :: file :: r ->
    if !parsing_project_file then
      raise (Parsing_error ("Invalid option -f in project file " ^ Option.get proj.project_file));
    let file = CUnix.remove_path_dot (CUnix.correct_path file orig_dir) in
    let () = match proj.project_file with
      | None -> ()
      | Some _ -> warning "Multiple project files are deprecated.@\n%!"
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
    aux { proj with defs = proj.defs @ [sourced (v,def)] } r
  | "-arg" :: a :: r ->
    aux { proj with extra_args = proj.extra_args @ [sourced a] } r
  | f :: r ->
      let f = CUnix.correct_path f orig_dir in
      let proj =
        if exists_dir f then { proj with subdirs = proj.subdirs @ [sourced f] }
        else match CUnix.get_extension f with
          | ".v" ->
            { proj with v_files = proj.v_files @ [sourced f] }
        | ".ml" -> { proj with ml_files = proj.ml_files @ [sourced f] }
        | ".ml4" -> { proj with ml4_files = proj.ml4_files @ [sourced f] }
        | ".mli" -> { proj with mli_files = proj.mli_files @ [sourced f] }
        | ".mllib" -> { proj with mllib_files = proj.mllib_files @ [sourced f] }
        | ".mlpack" -> { proj with mlpack_files = proj.mlpack_files @ [sourced f] }
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

let all_files { v_files; ml_files; mli_files; ml4_files;
                mllib_files; mlpack_files } =
  v_files @ mli_files @ ml4_files @ ml_files @ mllib_files @ mlpack_files

let map_sourced_list f l = List.map (fun x -> f x.thing) l
;;

let map_cmdline f l = CList.map_filter (function
    | {thing=x; source=CmdLine} -> Some (f x)
    | {source=ProjectFile} -> None) l

let coqtop_args_from_project
  { ml_includes; r_includes; q_includes; extra_args }
=
  let map = map_sourced_list  in
  let args =
    map (fun { canonical_path = i } -> ["-I"; i]) ml_includes @
    map (fun ({ canonical_path = i }, l) -> ["-Q"; i; l]) q_includes @
    map (fun ({ canonical_path = p }, l) -> ["-R"; p; l]) r_includes @
    [map (fun x -> x) extra_args] in
  List.flatten args
;;

let filter_cmdline l = CList.map_filter
    (function {thing; source=CmdLine} -> Some thing | {source=ProjectFile} -> None)
    l
;;

let forget_source {thing} = thing

(* vim:set ft=ocaml: *)
