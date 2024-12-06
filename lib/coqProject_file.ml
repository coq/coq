(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
(* items from expansion of directories are labelled ProjectFile *)

type 'a sourced = { thing : 'a; source : arg_source }

type meta_file = Absent | Present of string | Generate of string

type 'a project = {
  project_file  : string option;
  makefile : string option;
  native_compiler : native_compiler option;
  docroot : string option;

  files : string sourced list; (* .v, .ml, .mlg, .mli, .mllib, .mlpack files *)
  cmd_line_files : string sourced list;
  meta_file : meta_file;

  ml_includes : path sourced list;
  r_includes  : (path * logic_path) sourced list;
  q_includes  : (path * logic_path) sourced list;
  extra_args : string sourced list;
  defs : (string * string) sourced list;

  extra_data : 'a;
}
and logic_path = string
and path = { path : string; canonical_path : string }
and native_compiler =
| NativeYes
| NativeNo
| NativeOndemand

(* TODO generate with PPX *)
let mk_project project_file makefile native_compiler extra_data = {
  project_file;
  makefile;
  native_compiler;
  docroot = None;

  files = [];
  cmd_line_files = [];
  ml_includes = [];
  meta_file = Absent;
  r_includes = [];
  q_includes = [];
  extra_args = [];
  defs = [];

  extra_data;
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

let rec parse_string buf s = match input_char s with
| ' ' | '\n' | '\r' | '\t' -> buffer buf
| '#' ->
  parse_skip_comment s;
  buffer buf
| c ->
  let () = Buffer.add_char buf c in
  parse_string buf s
| exception End_of_file -> buffer buf

and parse_string2 buf s = match input_char s with
| '"' -> buffer buf
| c ->
  let () = Buffer.add_char buf c in
  parse_string2 buf s
| exception End_of_file -> raise (Parsing_error "unterminated string")

and parse_skip_comment s = match input_char s with
| '\n' -> ()
| _ -> parse_skip_comment s
| exception End_of_file -> ()

and parse_args buf accu s = match input_char s with
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
| exception End_of_file -> accu

exception UnableToOpenProjectFile of string

let parse f =
  let c = try open_in f with Sys_error msg -> raise (UnableToOpenProjectFile msg) in
  let buf = Buffer.create 64 in
  let res = parse_args buf [] c in
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

let expand_paths project =
  let orig_dir = Filename.current_dir_name in
  let orig_dir = if orig_dir = "." then "" else orig_dir in
  let abs_f f = CUnix.correct_path f orig_dir in  (* need a better function name *)
  let rec expand_dir path rv =
    let add_file f =
      if List.mem (Filename.extension f)
               [".v"; ".mli"; ".ml"; ".mlg"; ".mlpack"; ".mllib"] then
        rv := {thing=abs_f f; source=ProjectFile} :: !rv
    in
    if Sys.file_exists path && Sys.is_directory path then
      System.process_directory (fun fname ->
        match fname with
        | FileRegular f -> add_file (if path <> "." then Filename.concat path f else f)
        | FileDir (p,_) -> expand_dir p rv
      ) path
    else
      add_file path
  in
  List.fold_left (fun rv path ->
      let exp = ref [] in
      expand_dir path.thing exp;
      (List.sort (fun a b -> String.compare a.thing b.thing) !exp) @ rv)
    [] project.files

let process_cmd_line ~warning_fn orig_dir parse_extra proj args =
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
    let lp = if String.equal lp "Coq" then "Corelib" else lp in
    aux { proj with q_includes = proj.q_includes @ [sourced (mk_path d,lp)] } r
  | "-I" :: d :: r ->
    aux { proj with ml_includes = proj.ml_includes @ [sourced (mk_path d)] } r
  | "-R" :: d :: lp :: r ->
    let lp = if String.equal lp "Coq" then "Corelib" else lp in
    (* -R Coq ... is only used by Dune in conjunction with the -boot
       option. The above line should be removed once we require an
       updated version of Dune. *)
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
  | f :: r when CString.is_prefix "-" f -> begin match parse_extra f r proj.extra_data with
      | None -> raise (Parsing_error ("Unknown option " ^ f))
      | Some (r,extra_data) -> aux { proj with extra_data } r
    end
  | f :: r ->
      let abs_f = CUnix.correct_path f orig_dir in
      let ext = Filename.extension abs_f in
      let proj =
        match ext with
        | ".v"
        | ".ml"
        | ".mli"
        | ".mlg"
        | ".mllib"
        | ".mlpack" ->
          check_filename f;
          { proj with files = (sourced abs_f) :: proj.files }
        | ".ml4" ->
          let msg = Printf.sprintf "camlp5 macro files not supported anymore, please port %s to coqpp" abs_f in
          raise (Parsing_error msg)
        | _ ->
          if CString.is_prefix "META." (Filename.basename abs_f) then
            if proj.meta_file = Absent then
              { proj with meta_file = Present abs_f }
            else
              raise (Parsing_error "only one META.package file can be specified")
          else if ext = "" && not (CString.is_prefix "-" f) then begin
            check_filename f; (* consider it a directory *)
            { proj with files = (sourced abs_f) :: proj.files }
          end else
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
  let project = filter_extra proj proj.extra_args in
  let cmd_line_files = CList.rev (CList.map_filter
                       (function {thing; source=CmdLine} -> Some {thing; source=CmdLine}
                               | {source=ProjectFile}    -> None)
                     project.files) in
  { project with cmd_line_files; files = expand_paths project }

 (******************************* API ************************************)

let cmdline_args_to_project ~warning_fn ~curdir ~parse_extra extra args =
  process_cmd_line ~warning_fn curdir parse_extra (mk_project None None None extra) args

let read_project_file ~warning_fn f =
  process_cmd_line ~warning_fn (Filename.dirname f) (fun _ _ () -> None)
    (mk_project (Some f) None None ()) (parse f)

let rec find_project_file ~from ~projfile_name =
  let fname = Filename.concat from projfile_name in
  if Sys.file_exists fname then Some fname
  else
    let newdir = Filename.dirname from in
    if newdir = from then None
    else find_project_file ~from:newdir ~projfile_name

let all_files { files } = files

let files_by_suffix files suffixes =
  List.filter (fun file -> List.mem (Filename.extension file.thing) suffixes) files

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

let forget_source {thing} = thing

(* vim:set ft=ocaml: *)
