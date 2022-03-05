(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This needs to go through feedback as it is invoked from IDEs, but
   ideally we would like to make this independent so it can be
   bootstrapped. *)

type arg_source = CmdLine | ProjectFile

type 'a sourced = { thing : 'a; source : arg_source }

type meta_file = Absent | Present of string | Generate of string

type project = {
  project_file  : string option;
  makefile : string option;
  native_compiler : native_compiler option;
  docroot : string option;

  v_files : string sourced list;
  mli_files : string sourced list;
  mlg_files : string sourced list;
  ml_files : string sourced list;
  mllib_files : string sourced list;
  mlpack_files : string sourced list;
  meta_file : meta_file;

  ml_includes : path sourced list;
  r_includes  : (path * logic_path) sourced list;
  q_includes  : (path * logic_path) sourced list;
  extra_args : string sourced list;
  defs : (string * string) sourced list;
}
and logic_path = string
and path = { path : string; canonical_path : string }
and native_compiler =
| NativeYes
| NativeNo
| NativeOndemand

(* TODO generate with PPX *)
let mk_project project_file makefile native_compiler = {
  project_file;
  makefile;
  native_compiler;
  docroot = None;

  v_files = [];
  mli_files = [];
  mlg_files = [];
  ml_files = [];
  mllib_files = [];
  mlpack_files = [];
  ml_includes = [];
  meta_file = Absent;
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
| ' ' | '\n' | '\r' | '\t' -> buffer buf
| '#' ->
  parse_skip_comment s;
  buffer buf
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
| ' ' | '\n' | '\r' | '\t' -> parse_args buf accu s
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

exception UnableToOpenProjectFile of string

let parse f =
  let c = try open_in f with Sys_error msg -> raise (UnableToOpenProjectFile msg) in
  let buf = Buffer.create 64 in
  let res = parse_args buf [] (Stream.of_channel c) in
  close_in c;
  List.rev res

let parse_native ~warning_fn ~error proj flag =
  if proj.native_compiler <> None then
    (warning_fn "-native-compiler set more than once.");
  let native = match flag with
    | "yes" -> NativeYes
    | "no" -> NativeNo
    | "ondemand" -> NativeOndemand
    | _ -> error ("invalid option \""^flag^"\" passed to -native-compiler")
  in
  { proj with native_compiler = Some native }

let escape_char c =
  match c with
  | '\'' -> "\'"
  | '\n' -> "\\n"
  | '\r' -> "\\r"
  | '\t' -> "\\t"
  | c -> String.make 1 c

let check_filename f =
  let a = ref None in
  let check_char c =
    match c with
    | '\n' | '\r' | '\t' | '\\' | '\'' | '"' | ' ' | '#' | '$' | '%' -> a := Some c
    | _ -> ()
  in
  String.iter check_char f;
  match !a with
  | Some c -> raise (Parsing_error ("Unsupported filename, contains '"
                      ^ (escape_char c) ^ "' : \"" ^ String.escaped f ^ "\""))
  | None -> ()

(* single quotes keep whitespace together and keep it literal. But only
 * unquoted spaces split arguments apart. i.e the string "a'b c'd"
 * produces the list ["ab cd"] *)
let process_extra_args arg =
  let buf = Buffer.create 64 in
  let out_list = ref [] in
  let inside_quotes = ref false in
  let has_leftovers = ref false in
  let process_char c =
    match c with
    | '\'' ->
        inside_quotes := not !inside_quotes;
        has_leftovers := true;
    | ' ' ->
      if !inside_quotes then
        (has_leftovers := true; Buffer.add_char buf ' ')
      else
        if !has_leftovers then
          (has_leftovers := false;
           out_list := buffer buf :: !out_list)
    | c -> has_leftovers := true; Buffer.add_char buf c
  in
  String.iter process_char arg;
  if !has_leftovers then
    out_list := buffer buf :: !out_list;
  List.rev !out_list

let process_cmd_line ~warning_fn orig_dir proj args =
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

  | "-Q" :: d :: lp :: r ->
    aux { proj with q_includes = proj.q_includes @ [sourced (mk_path d,lp)] } r
  | "-I" :: d :: r ->
    aux { proj with ml_includes = proj.ml_includes @ [sourced (mk_path d)] } r
  | "-R" :: d :: lp :: r ->
    aux { proj with r_includes = proj.r_includes @ [sourced (mk_path d,lp)] } r

  | "-native-compiler" :: flag :: r ->
    let proj = parse_native ~warning_fn ~error proj flag in
    aux proj r

  | "-f" :: file :: r ->
    if !parsing_project_file then
      raise (Parsing_error ("Invalid option -f in project file " ^ Option.get proj.project_file));
    let file = CUnix.remove_path_dot (CUnix.correct_path file orig_dir) in
    let () = match proj.project_file with
      | None -> ()
      | Some _ -> warning_fn "Multiple project files are deprecated."
    in
    parsing_project_file := true;
    let r' = try parse file with UnableToOpenProjectFile msg -> error msg in
    let proj = aux { proj with project_file = Some file } r' in
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

  | "-docroot" :: p :: r ->
    if proj.docroot <> None then
      error "Option -docroot given more than once";
    aux { proj with docroot = Some p } r

  | "-generate-meta-for-package" :: m :: r ->
    if proj.meta_file <> Absent then
      error "Option -generate-meta-for-package cannot be repeated";
    aux { proj with meta_file = Generate m } r


  | v :: "=" :: def :: r ->
    aux { proj with defs = proj.defs @ [sourced (v,def)] } r
  | "-arg" :: a :: r ->
    aux { proj with extra_args = proj.extra_args @ List.map sourced (process_extra_args a) } r
  | f :: r ->
      let abs_f = CUnix.correct_path f orig_dir in
      let proj =
        match Filename.extension abs_f with
        | ".v" ->
          check_filename f;
          { proj with v_files = proj.v_files @ [sourced abs_f] }
        | ".ml" ->
          check_filename f;
          { proj with ml_files = proj.ml_files @ [sourced abs_f] }
        | ".ml4" ->
          let msg = Printf.sprintf "camlp5 macro files not supported anymore, please port %s to coqpp" abs_f in
          raise (Parsing_error msg)
        | ".mlg" ->
          check_filename f;
          { proj with mlg_files = proj.mlg_files @ [sourced abs_f] }
        | ".mli" ->
          check_filename f;
          { proj with mli_files = proj.mli_files @ [sourced abs_f] }
        | ".mllib" ->
          check_filename f;
          { proj with mllib_files = proj.mllib_files @ [sourced abs_f] }
        | ".mlpack" ->
          check_filename f;
          { proj with mlpack_files = proj.mlpack_files @ [sourced abs_f] }
        | _ ->
          if CString.is_prefix "META." (Filename.basename abs_f) then
            if proj.meta_file = Absent then
              { proj with meta_file = Present abs_f }
            else
              raise (Parsing_error "only one META.package file can be specified")
          else
            raise (Parsing_error ("Unknown option " ^ f)) in
      aux proj r
 in
  let proj = aux proj args in
  (* Short-circuit -native-compiler options passed via -args *)
  let rec filter_extra proj = function
  | [] -> { proj with extra_args = [] }
  | { thing = "-native-compiler" } :: { thing = flag } :: r ->
    let proj = parse_native ~warning_fn ~error proj flag in
    filter_extra proj r
  | extra :: r ->
    let proj = filter_extra proj r in
    { proj with extra_args = extra :: proj.extra_args }
  in
  filter_extra proj proj.extra_args

 (******************************* API ************************************)

let cmdline_args_to_project ~warning_fn ~curdir args =
  process_cmd_line ~warning_fn curdir (mk_project None None None) args

let read_project_file ~warning_fn f =
  process_cmd_line ~warning_fn (Filename.dirname f)
    (mk_project (Some f) None None) (parse f)

let rec find_project_file ~from ~projfile_name =
  let fname = Filename.concat from projfile_name in
  if Sys.file_exists fname then Some fname
  else
    let newdir = Filename.dirname from in
    if newdir = from then None
    else find_project_file ~from:newdir ~projfile_name

let all_files { v_files; ml_files; mli_files; mlg_files;
                mllib_files; mlpack_files } =
  v_files @ mli_files @ mlg_files @ ml_files @ mllib_files @ mlpack_files

let map_sourced_list f l = List.map (fun x -> f x.thing) l

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

let filter_cmdline l = CList.map_filter
    (function {thing; source=CmdLine} -> Some thing | {source=ProjectFile} -> None)
    l

let forget_source {thing} = thing

(* vim:set ft=ocaml: *)
