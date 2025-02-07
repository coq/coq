(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* rocq makefile: automatically create a Makefile for a Rocq development *)

open CoqProject_file
open Printf

let (>) f g = fun x -> g (f x)

let usage_coq_makefile ~ok =
  let out = if ok then stdout else stderr in
  output_string out "Usage summary:\
\n\
\nrocq makefile .... [file.v] ... [file.ml[ig]?] ... [file.ml{lib,pack}]\
\n  ... [-I dir] ... [-R physicalpath logicalpath]\
\n  ... [-Q physicalpath logicalpath] ... [VARIABLE = value]\
\n  ... [-arg opt] ... [-docroot path] [-f file] [-o file]\
\n  ... [-generate-meta-for-package project-name]\
\n  [-h] [--help] [-v] [--version]\
\n";
  output_string out "\
\nFull list of options:\
\n\
\n[file.v]: Rocq file to be compiled\
\n[file.ml[ig]?]: Objective Caml file to be compiled\
\n[file.ml{lib,pack}]: ocamlbuild-style file that describes a Objective Caml\
\n  library/module\
\n[-I dir]: look for Objective Caml dependencies in \"dir\"\
\n[-R physicalpath logicalpath]: look for Rocq dependencies recursively\
\n  starting from \"physicalpath\". The logical path associated to the\
\n  physical path is \"logicalpath\".\
\n[-Q physicalpath logicalpath]: look for Rocq dependencies starting from\
\n  \"physicalpath\". The logical path associated to the physical path\
\n  is \"logicalpath\".\
\n[VARIABLE = value]: Add the variable definition \"VARIABLE=value\"\
\n[-arg opt]: send option \"opt\" to rocq compile\
\n[-docroot path]: Install the documentation in this folder, relative to\
\n  \"user-contrib\".\
\n[-f file]: take the contents of file as arguments\
\n[-o file]: output should go in file file (recommended)\
\n	Output file outside the current directory is forbidden.\
\n[-generate-meta-for-package project-name]: generate META.project-name.\
\n[-h]: print this usage summary\
\n[--help]: equivalent to [-h]\
\n[-v]: print version information\
\n[--version]: equivalent to [-v]\
\n";
  exit (if ok then 0 else 1)

let is_prefix dir1 dir2 =
  let l1 = String.length dir1 in
  let l2 = String.length dir2 in
  let sep = Filename.dir_sep in
  if dir1 = dir2 then true
  else if l1 + String.length sep <= l2 then
    let dir1' = String.sub dir2 0 l1 in
    let sep' = String.sub dir2 l1 (String.length sep) in
    dir1' = dir1 && sep' = sep
  else false

let physical_dir_of_logical_dir ldir =
  let ldir = Bytes.of_string ldir in
  let le = Bytes.length ldir - 1 in
  let pdir =
    if le >= 0 && Bytes.get ldir le = '.' then Bytes.sub ldir 0 (le - 1)
    else Bytes.copy ldir
  in
  for i = 0 to le - 1 do
    if Bytes.get pdir i = '.' then Bytes.set pdir i '/';
  done;
  Bytes.to_string pdir

let read_whole_file s =
  let ic = open_in s in
  let b = Buffer.create (1 lsl 12) in
  try
     while true do
       let s = input_line ic in
       Buffer.add_string b s;
       Buffer.add_char b '\n';
     done;
     assert false;
  with End_of_file ->
    close_in ic;
    Buffer.contents b

(* Use this for quoting contents of variables which never appears as target or
 * pattern. *)
let makefile_quote s =
  let out = Buffer.create 16 in
  Buffer.add_string out "'";
  String.iter
    (fun c ->
      match c with
      | '$' -> Buffer.add_string out "$$"
      | '#' -> Buffer.add_string out "\\#"
      | '\'' -> Buffer.add_string out "'\\''"
      | _ -> Buffer.add_char out c
    )
  s;
  Buffer.add_string out "'";
  Buffer.contents out

let quote s = if String.contains s ' ' || CString.is_empty s then "'" ^ s ^ "'" else s

let generate_makefile oc conf_file local_file local_late_file dep_file args project =
  let env = Boot.Env.init () in
  (* XX coq makefile should ship files on its own dir *)
  let cmf_dir = Boot.Env.tool env "" in
  let makefile_template = Boot.Path.relative cmf_dir "CoqMakefile.in" in
  if not (Boot.Path.exists makefile_template) then
    begin
      let makefile_template = Boot.Path.to_string makefile_template in
      Format.eprintf "Error: cannot find %s" makefile_template;
      exit 1
    end;
  let makefile_template = Boot.Path.to_string makefile_template in
  let s = read_whole_file makefile_template in
  let s = List.fold_left
    (* We use global_substitute to avoid running into backslash issues due to \1 etc. *)
    (fun s (k,v) -> Str.global_substitute (Str.regexp_string k) (fun _ -> v) s) s
    [ "@CONF_FILE@", conf_file;
      "@LOCAL_FILE@", local_file;
      "@LOCAL_LATE_FILE@", local_late_file;
      "@DEP_FILE@", dep_file;
      "@COQ_VERSION@", Coq_config.version;
      "@PROJECT_FILE@", (Option.default "" project.project_file);
      "@COQ_MAKEFILE_INVOCATION@",String.concat " " (List.map quote args);
    ] in
  output_string oc s

let generate_meta_file p =
  try
    match p.meta_file with
    | Absent -> p
    | Generate proj ->
        let cmname = List.map (fun { thing } -> thing)
            (files_by_suffix p.files [".mllib"; ".mlpack"]) in
        let dir, cmname =
          match cmname with
          | [] -> Printf.eprintf "In order to generate a META file one needs an .mlpack or .mllib file\n"; exit 1
          | [x] -> Filename.dirname x, Filename.(basename @@ chop_extension x)
          | _ -> Printf.eprintf "Automatic META generation only works for one .mlpack or .mllib file, since you have more you need to write the META file by hand\n"; exit 1 in
        let f = dir ^ "/META." ^ proj in
        let oc = open_out f in
        let meta : _ format = {|
package "plugin" (
  directory = "."
  requires = "rocq-runtime.plugins.ltac"
  archive(byte) = "%s.cma"
  archive(native) = "%s.cmxa"
  plugin(byte) = "%s.cma"
  plugin(native) = "%s.cmxs"
)
directory = "."
|}
        in
        let meta = Printf.sprintf meta cmname cmname cmname cmname in
        output_string oc meta;
        close_out oc;
        { p with meta_file = Present f }
    | Present f ->
        let ext = Filename.extension f in
        if ext = ".in" then
          let meta_file = Filename.chop_extension f in
          let oc = open_out meta_file in
          (* META generation is just a renaming for now, we lack some metadata *)
          output_string oc (read_whole_file f);
          close_out oc;
          { p with meta_file = Present meta_file }
        else
          p (* already a META.package file *)
  with Sys_error e ->
    Printf.eprintf "Error: %s\n" e;
    exit 1

let section oc s =
  let pad = String.make (76 - String.length s) ' ' in
  let sharps = String.make 79 '#' in
  let spaces = "#" ^ String.make 77 ' ' ^ "#" in
  fprintf oc "\n%s\n" sharps;
  fprintf oc "%s\n" spaces;
  fprintf oc "# %s%s#\n" s pad;
  fprintf oc "%s\n" spaces;
  fprintf oc "%s\n\n" sharps
;;

let generate_conf_includes oc { ml_includes; r_includes; q_includes } =
  section oc "Path directives (-I, -R, -Q).";
  let module S = String in
  let map = map_sourced_list in
  let dash1 opt v = sprintf "-%s %s" opt (quote v) in
  let dash2 opt v1 v2 = sprintf "-%s %s %s" opt (quote v1) (quote v2) in
  fprintf oc "COQMF_OCAMLLIBS = %s\n"
    (S.concat " " (map (fun { path } -> dash1 "I" path) ml_includes));
  fprintf oc "COQMF_SRC_SUBDIRS = %s\n"
    (S.concat " " (map (fun { path } -> quote path) ml_includes));
  fprintf oc "COQMF_COQLIBS = %s %s %s\n"
    (S.concat " " (map (fun { path } -> dash1 "I" path) ml_includes))
    (S.concat " " (map (fun ({ path },l) -> dash2 "Q" path l) q_includes))
    (S.concat " " (map (fun ({ path },l) -> dash2 "R" path l) r_includes));
  fprintf oc "COQMF_COQLIBS_NOML = %s %s\n"
    (S.concat " " (map (fun ({ path },l) -> dash2 "Q" path l) q_includes))
    (S.concat " " (map (fun ({ path },l) -> dash2 "R" path l) r_includes));
  fprintf oc "COQMF_CMDLINE_COQLIBS = %s %s %s\n"
    (S.concat " " (map_cmdline (fun { path } -> dash1 "I" path) ml_includes))
    (S.concat " " (map_cmdline (fun ({ path },l) -> dash2 "Q" path l) q_includes))
    (S.concat " " (map_cmdline (fun ({ path },l) -> dash2 "R" path l) r_includes));
;;

let windrive s =
  if Coq_config.arch_is_win32 && Str.(string_match (regexp "^[a-zA-Z]:") s 0)
  then Str.matched_string s
  else ""
;;

let generate_conf_coq_config oc =
  section oc "Rocq configuration.";
  let env = Boot.Env.init () in
  Boot.Env.print_config ~prefix_var_name:"COQMF_" env oc;
  let coqlib = Boot.Env.(coqlib env |> Path.to_string) in
  (* XXX: FIXME, why does this variable needs the root lib *)
  fprintf oc "COQMF_WINDRIVE=%s\n" (windrive coqlib)
;;

let check_metafile p =
  if files_by_suffix p.files [".mlpack"; ".mllib"] <> [] && p.meta_file = Absent then begin
    eprintf "Warning: it is recommended you provide a META.package-name file\n";
    eprintf "Warning: since you build plugins. See also -generate-meta-for-package.\n";
  end

let write_coqbin oc =
  fprintf oc "%s\n"
    "COQBIN?=\n\
    ifneq (,$(COQBIN))\n\
    # add an ending /\n\
    COQBIN:=$(COQBIN)/\n\
    endif\n\
    COQMKFILE ?= \"$(COQBIN)rocq\" makefile"

let generate_conf_files oc p
=
  let module S = String in
  let fout varname suffix =
    fprintf oc "COQMF_%s := $(filter %%%s, $(COQMF_SOURCES))\n" varname suffix;
  in
  section oc "Project files.";

  let cmdline_vfiles = p.cmd_line_files in
  fprintf oc "COQMF_CMDLINE_VFILES := %s\n" (S.concat " " (map_sourced_list quote cmdline_vfiles));
  let proj_arg = match p.project_file with
    | Some pfile -> Printf.sprintf "-f %s" pfile
    | None -> ""
  in
  fprintf oc "COQMF_SOURCES := $(shell $(COQMKFILE) -sources-of %s $(COQMF_CMDLINE_VFILES))\n" proj_arg;
  fout "VFILES" ".v";
  fout "MLIFILES" ".mli";
  fout "MLFILES" ".ml";
  fout "MLGFILES" ".mlg";
  fout "MLPACKFILES" ".mlpack";
  fout "MLLIBFILES" ".mllib";
  fprintf oc "COQMF_METAFILE = %s\n"  (match p.meta_file with Present x -> x | _ -> "")

let rec all_start_with prefix = function
  | [] -> true
  | [] :: _ -> false
  | (x :: _) :: rest -> x = prefix && all_start_with prefix rest

let rec logic_gcd acc = function
  | [] -> acc
  | [] :: _ -> acc
  | (hd :: tl) :: rest ->
      if all_start_with hd rest
      then logic_gcd (acc @ [hd]) (tl :: List.map List.tl rest)
      else acc

let generate_conf_doc oc { docroot; q_includes; r_includes } =
  let includes = List.map (forget_source > snd) (q_includes @ r_includes) in
  let logpaths = List.map (String.split_on_char '.') includes in
  let gcd = logic_gcd [] logpaths in
  let root =
    match docroot with
    | None ->
      if gcd = [] then
         let destination = "orphan_" ^ (String.concat "_" includes) in
         eprintf "Warning: No common logical root.\n";
         eprintf "Warning: In this case the -docroot option should be given.\n";
         eprintf "Warning: Otherwise the install-doc target is going to install files\n";
         eprintf "Warning: in %s\n" destination;
         destination
      else String.concat Filename.dir_sep gcd
    | Some p -> p in
  Printf.fprintf oc "COQMF_INSTALLCOQDOCROOT = %s\n" (quote root)

let generate_conf_native oc native_compiler =
  section oc "Native compiler.";
  let flag = match native_compiler with
  | None -> ""
  | Some NativeYes -> "yes"
  | Some NativeNo -> "no"
  | Some NativeOndemand -> "ondemand"
  in
  Printf.fprintf oc "COQMF_COQPROJECTNATIVEFLAG = %s\n" flag


let generate_conf_defs oc { defs; extra_args } =
  section oc "Extra variables.";
  List.iter (forget_source > (fun (k,v) -> Printf.fprintf oc "%s = %s\n" k v)) defs;
  Printf.fprintf oc "COQMF_OTHERFLAGS = %s\n"
    (String.concat " " (List.map (forget_source > makefile_quote) extra_args))

let generate_conf oc project args  =
  fprintf oc "# This configuration file was generated by running:\n";
  fprintf oc "# %s\n\n" (String.concat " " (List.map quote args));
  write_coqbin oc;
  generate_conf_files oc project;
  generate_conf_includes oc project;
  generate_conf_coq_config oc;
  generate_conf_native oc project.native_compiler;
  generate_conf_defs oc project;
  generate_conf_doc oc project;
;;

let ensure_root_dir
  ({ ml_includes; r_includes; q_includes; files } as project)
  =
  let exists f = List.exists (forget_source > f) in
  let here = Sys.getcwd () in
  let not_tops = List.for_all (fun s -> s.thing <> Filename.basename s.thing) in
  if exists (fun { canonical_path = x } -> x = here) ml_includes
  || exists (fun ({ canonical_path = x },_) -> is_prefix x here) r_includes
  || exists (fun ({ canonical_path = x },_) -> is_prefix x here) q_includes
  || not_tops files
  then
    project
  else
    let source x = {thing=x; source=CmdLine} in
    let here_path = { path = "."; canonical_path = here } in
    { project with
        ml_includes = source here_path :: ml_includes;
        r_includes = source (here_path, "Top") :: r_includes }
;;

let check_overlapping_include { q_includes; r_includes } =
  let pwd = Sys.getcwd () in
  let aux = function
    | [] -> ()
    | {thing = { path; canonical_path }, _} :: l ->
        if not (is_prefix pwd canonical_path) then
          eprintf "Warning: %s (used in -R or -Q) is not a subdirectory of the current directory\n\n" path;
        List.iter (fun {thing={ path = p; canonical_path = cp }, _} ->
          if is_prefix canonical_path cp  || is_prefix cp canonical_path then
            eprintf "Warning: %s and %s overlap (used in -R or -Q)\n\n"
              path p) l
  in
    aux (q_includes @ r_includes)
;;

let check_native_compiler = function
| None -> ()
| Some flag ->
  match Coq_config.native_compiler, flag with
  | Coq_config.NativeOff, (NativeYes | NativeOndemand) ->
    eprintf "Warning: native compilation is globally deactivated by the configure flag\n"
  | _ -> ()

let chop_prefix p f =
  let len_p = String.length p in
  let len_f = String.length f in
  String.sub f len_p (len_f - len_p)

type extra_opts = {
  only_destination : string option;
  only_sources : bool;
}

let empty_extra = {
  only_destination = None;
  only_sources = false;
}

let parse_extra f r opts = match f, r with
  | "-destination-of", tgt :: r -> Some (r, { opts with only_destination = Some tgt })
  | "-sources-of", r -> Some (r, { opts with only_sources = true })
  | ("-h"|"--help"), _ -> usage_coq_makefile ~ok:true
  | ("-v"|"--version"), _ -> Boot.Usage.version (); exit 0
  | _ -> None

let destination_of { ml_includes; q_includes; r_includes; } file =
  let file_dir = CUnix.canonical_path_name (Filename.dirname file) in
  let includes = q_includes @ r_includes in
  let mk_destination logic canonical_path =
    Filename.concat
      (physical_dir_of_logical_dir logic)
      (chop_prefix canonical_path file_dir) in
  let candidates =
    CList.map_filter (fun {thing={ canonical_path }, logic} ->
      if is_prefix canonical_path file_dir then
        Some(mk_destination logic canonical_path)
      else None) includes
  in
  match candidates with
  | [] ->
     (* BACKWARD COMPATIBILITY: -I into the only logical root *)
     begin match
        r_includes,
        List.find (fun {thing={ canonical_path = p }} -> is_prefix p file_dir)
          ml_includes
     with
        | [{thing={ canonical_path }, logic}], {thing={ canonical_path = p }} ->
            let destination =
              Filename.concat
                (physical_dir_of_logical_dir logic)
                (chop_prefix p file_dir) in
            Printf.printf "%s" (quote destination)
        | _ -> () (* skip *)
        | exception Not_found -> () (* skip *)
     end
  | [s] -> Printf.printf "%s" (quote s)
  | _ -> assert false

let main ~prog args =
  let _fhandle = Feedback.(add_feeder (console_feedback_listener Format.err_formatter)) in

  let { extra_data = { only_destination; only_sources } } as project =
    let warning_fn x = Format.eprintf "%s@\n%!" x in
    try cmdline_args_to_project ~warning_fn ~curdir:Filename.current_dir_name ~parse_extra empty_extra args
    with Parsing_error s -> prerr_endline s; usage_coq_makefile ~ok:false in

  if only_destination <> None then begin
    destination_of project (Option.get only_destination);
    exit 0
  end;

  if only_sources then begin
    let paths = String.concat " " (List.map (fun i -> i.thing) project.files) in
    Printf.printf "%s" paths;
    exit 0
  end;

  if project.makefile = None then
    eprintf "Warning: Omitting -o is deprecated\n\n";
    (* We want to know the name of the Makefile (say m) in order to
     * generate m.conf and include m.local *)

  let conf_file = Option.default "CoqMakefile" project.makefile ^ ".conf" in
  let local_file = Option.default "CoqMakefile" project.makefile ^ ".local" in
  let local_late_file = Option.default "CoqMakefile" project.makefile ^ ".local-late" in
  let dep_file = "." ^ Option.default "CoqMakefile" project.makefile ^ ".d" in

  let project = ensure_root_dir project in

  check_overlapping_include project;

  check_native_compiler project.native_compiler;

  check_metafile project;

  let project = generate_meta_file project in

  let ocm = Option.cata open_out stdout project.makefile in
  generate_makefile ocm conf_file local_file local_late_file dep_file (prog @ args) project;
  close_out ocm;
  let occ = open_out conf_file in
  generate_conf occ project (prog @ args);
  close_out occ;
  exit 0
