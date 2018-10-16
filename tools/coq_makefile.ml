(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Coq_makefile: automatically create a Makefile for a Coq development *)

open CoqProject_file
open Printf

let (>) f g = fun x -> g (f x)

let output_channel = ref stdout
let makefile_name = ref "Makefile"
let make_name = ref ""

let print x = output_string !output_channel x
let printf x = Printf.fprintf !output_channel x

let rec print_list sep = function
  | [ x ] -> print x
  | x :: l -> print x; print sep; print_list sep l
  | [] -> ()

let rec print_prefix_list sep = function
  | x :: l -> print sep; print x; print_prefix_list sep l
  | [] -> ()

let usage_coq_makefile () =
  output_string stderr "Usage summary:\
\n\
\ncoq_makefile .... [file.v] ... [file.ml[i4]?] ... [file.ml{lib,pack}]\
\n  ... [any] ... [-extra[-phony] result dependencies command]\
\n  ... [-I dir] ... [-R physicalpath logicalpath]\
\n  ... [-Q physicalpath logicalpath] ... [VARIABLE = value]\
\n  ...  [-arg opt] ... [-opt|-byte] [-no-install] [-f file] [-o file]\
\n  [-h] [--help]\
\n";
  output_string stderr "\
\nFull list of options:\
\n\
\n[file.v]: Coq file to be compiled\
\n[file.ml[i4]?]: Objective Caml file to be compiled\
\n[file.ml{lib,pack}]: ocamlbuild file that describes a Objective Caml\
\n  library/module\
\n[any] : subdirectory that should be \"made\" and has a Makefile itself\
\n  to do so. Very fragile and discouraged.\
\n[-extra result dependencies command]: add target \"result\" with command\
\n  \"command\" and dependencies \"dependencies\". If \"result\" is not\
\n  generic (do not contains a %), \"result\" is built by _make all_ and\
\n  deleted by _make clean_.\
\n[-extra-phony result dependencies command]: add a PHONY target \"result\"\
\n with command \"command\" and dependencies \"dependencies\". Note that\
\n _-extra-phony foo bar \"\"_ is a regular way to add the target \"bar\" as\
\n as a dependencies of an already defined target \"foo\".\
\n[-I dir]: look for Objective Caml dependencies in \"dir\"\
\n[-R physicalpath logicalpath]: look for Coq dependencies recursively\
\n  starting from \"physicalpath\". The logical path associated to the\
\n  physical path is \"logicalpath\".\
\n[-Q physicalpath logicalpath]: look for Coq dependencies starting from\
\n  \"physicalpath\". The logical path associated to the physical path\
\n  is \"logicalpath\".\
\n[VARIABLE = value]: Add the variable definition \"VARIABLE=value\"\
\n[-byte]: compile with byte-code version of coq\
\n[-opt]: compile with native-code version of coq\
\n[-arg opt]: send option \"opt\" to coqc\
\n[-install opt]: where opt is \"user\" to force install into user directory,\
\n  \"none\" to build a makefile with no install target or\
\n  \"global\" to force install in $COQLIB directory\
\n[-f file]: take the contents of file as arguments\
\n[-o file]: output should go in file file (recommended)\
\n	Output file outside the current directory is forbidden.\
\n[-h]: print this usage summary\
\n[--help]: equivalent to [-h]\n";
  exit 1

let is_genrule r = (* generic rule (like bar%foo: ...) *)
    let genrule = Str.regexp("%") in
      Str.string_match genrule r 0

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

let quote s = if String.contains s ' ' || CString.is_empty s then "'" ^ s ^ "'" else s

let generate_makefile oc conf_file local_file args project =
  let makefile_template =
    let template = "/tools/CoqMakefile.in" in
    Envars.coqlib () ^ template in
  let s = read_whole_file makefile_template in
  let s = List.fold_left
    (* We use global_substitute to avoid running into backslash issues due to \1 etc. *)
    (fun s (k,v) -> Str.global_substitute (Str.regexp_string k) (fun _ -> v) s) s
    [ "@CONF_FILE@", conf_file;
      "@LOCAL_FILE@", local_file;
      "@COQ_VERSION@", Coq_config.version;
      "@PROJECT_FILE@", (Option.default "" project.project_file);
      "@COQ_MAKEFILE_INVOCATION@",String.concat " " (List.map quote args);
    ] in
  output_string oc s
;;

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

let clean_tgts = ["clean"; "cleanall"; "archclean"]

let generate_conf_extra_target oc sps =
  let pr_path { target; dependencies; phony; command } =
    let target = if target = "all" then "custom-all" else target in
    if phony then fprintf oc ".PHONY: %s\n" target;
    if not (is_genrule target) && not phony then begin
      fprintf oc "post-all::\n\t$(MAKE) -f $(SELF) %s\n" target;
      if not phony then
        fprintf oc "clean::\n\trm -f %s\n" target;
    end;
    fprintf oc "%s %s %s\n\t%s\n\n"
       target
       (if List.mem target clean_tgts then ":: " else ": ")
       dependencies
       command
  in
    if sps <> [] then
      section oc "Extra targets. (-extra and -extra-phony, DEPRECATED)";
    List.iter (forget_source > pr_path) sps

let generate_conf_subdirs oc sds =
  if sds <> [] then section oc "Subdirectories. (DEPRECATED)";
  let iter f = List.iter (forget_source > f) in
  iter (fprintf oc ".PHONY:%s\n") sds;
  iter (fprintf oc "post-all::\n\tcd \"%s\" && $(MAKE) all\n") sds;
  iter (fprintf oc "clean::\n\tcd \"%s\" && $(MAKE) clean\n") sds;
  iter (fprintf oc "archclean::\n\tcd \"%s\" && $(MAKE) archclean\n") sds;
  iter (fprintf oc "install-extra::\n\tcd \"%s\" && $(MAKE) install\n") sds
   

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
  section oc "Coq configuration.";
  let src_dirs = Coq_config.all_src_dirs in
  Envars.print_config ~prefix_var_name:"COQMF_" oc src_dirs;
  fprintf oc "COQMF_WINDRIVE=%s\n" (windrive Coq_config.coqlib)
;;

let generate_conf_files oc
  { v_files; mli_files; ml4_files; ml_files; mllib_files; mlpack_files; }
=
  let module S = String in
  let map = map_sourced_list in
  section oc "Project files.";
  fprintf oc "COQMF_VFILES = %s\n"      (S.concat " " (map quote v_files));
  fprintf oc "COQMF_MLIFILES = %s\n"    (S.concat " " (map quote mli_files));
  fprintf oc "COQMF_MLFILES = %s\n"     (S.concat " " (map quote ml_files));
  fprintf oc "COQMF_ML4FILES = %s\n"    (S.concat " " (map quote ml4_files));
  fprintf oc "COQMF_MLPACKFILES = %s\n" (S.concat " " (map quote mlpack_files));
  fprintf oc "COQMF_MLLIBFILES = %s\n"  (S.concat " " (map quote mllib_files));
  let cmdline_vfiles = filter_cmdline v_files in
  fprintf oc "COQMF_CMDLINE_VFILES = %s\n" (S.concat " " (List.map quote cmdline_vfiles));
;;

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

let generate_conf_doc oc { defs; q_includes; r_includes } =
  let includes = List.map (forget_source > snd) (q_includes @ r_includes) in
  let logpaths = List.map (CString.split '.') includes in
  let gcd = logic_gcd [] logpaths in
  let root =
    if gcd = [] then
      if not (List.exists (fun x -> fst x.thing = "INSTALLDEFAULTROOT") defs) then begin
         let destination = "orphan_" ^ (String.concat "_" includes) in
         eprintf "Warning: no common logical root\n";
         eprintf "Warning: in such case INSTALLDEFAULTROOT must be defined\n";
         eprintf "Warning: the install-doc target is going to install files\n";
         eprintf "Warning: in %s\n" destination;
         destination
      end else "$(INSTALLDEFAULTROOT)"
    else String.concat "/" gcd in
  Printf.fprintf oc "COQMF_INSTALLCOQDOCROOT = %s\n" (quote root)

let generate_conf_defs oc { defs; extra_args } =
  section oc "Extra variables.";
  List.iter (forget_source > (fun (k,v) -> Printf.fprintf oc "%s = %s\n" k v)) defs;
  Printf.fprintf oc "COQMF_OTHERFLAGS = %s\n"
    (String.concat " " (List.map forget_source extra_args))

let generate_conf oc project args  =
  fprintf oc "# This configuration file was generated by running:\n";
  fprintf oc "# %s\n\n" (String.concat " " (List.map quote args));
  generate_conf_files oc project;
  generate_conf_includes oc project;
  generate_conf_coq_config oc;
  generate_conf_defs oc project;
  generate_conf_doc oc project;
  generate_conf_extra_target oc project.extra_targets;
  generate_conf_subdirs oc project.subdirs;
;;

let ensure_root_dir
  ({ ml_includes; r_includes; q_includes;
     v_files; ml_files; mli_files; ml4_files;
     mllib_files; mlpack_files } as project)
  =
  let exists f = List.exists (forget_source > f) in
  let here = Sys.getcwd () in
  let not_tops = List.for_all (fun s -> s.thing <> Filename.basename s.thing) in
  if exists (fun { canonical_path = x } -> x = here) ml_includes
  || exists (fun ({ canonical_path = x },_) -> is_prefix x here) r_includes
  || exists (fun ({ canonical_path = x },_) -> is_prefix x here) q_includes
  || (not_tops v_files &&
      not_tops mli_files && not_tops ml4_files && not_tops ml_files &&
      not_tops mllib_files && not_tops mlpack_files)
  then
    project
  else
    let source x = {thing=x; source=CmdLine} in
    let here_path = { path = "."; canonical_path = here } in
    { project with
        ml_includes = source here_path :: ml_includes;
        r_includes = source (here_path, "Top") :: r_includes }
;;

let warn_install_at_root_directory 
  ({ q_includes; r_includes; } as project)
=
  let open CList in
  let inc_top_p =
    map_filter
      (fun {thing=({ path } ,ldir)} -> if ldir = "" then Some path else None)
      (r_includes @ q_includes) in
  let files = all_files project in
  let bad = filter (fun f -> mem (Filename.dirname f.thing) inc_top_p) files in
  if bad <> [] then begin
    eprintf "Warning: No file should be installed at the root of Coq's library.\n";
    eprintf "Warning: No logical path (-R, -Q) applies to these files:\n";
    List.iter (fun x -> eprintf "Warning:  %s\n" x.thing) bad;
    eprintf "\n";
  end
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

let chop_prefix p f =
  let len_p = String.length p in
  let len_f = String.length f in
  String.sub f len_p (len_f - len_p)

let clean_path p =
  Str.global_replace (Str.regexp_string "//") "/" p

let destination_of { ml_includes; q_includes; r_includes; } file =
  let file_dir = CUnix.canonical_path_name (Filename.dirname file) in
  let includes = q_includes @ r_includes in
  let mk_destination logic canonical_path =
    clean_path (physical_dir_of_logical_dir logic ^ "/" ^
                chop_prefix canonical_path file_dir ^ "/") in
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
              clean_path (physical_dir_of_logical_dir logic ^ "/" ^
                          chop_prefix p file_dir ^ "/") in
            Printf.printf "%s" (quote destination)
        | _ -> () (* skip *)
        | exception Not_found -> () (* skip *)
     end
  | [s] -> Printf.printf "%s" (quote s)
  | _ -> assert false

let share_prefix s1 s2 =
  let s1 = CString.split '.' s1 in
  let s2 = CString.split '.' s2 in
  match s1, s2 with
  | x :: _ , y :: _ -> x = y
  | _ -> false

let _ =
  let _fhandle = Feedback.(add_feeder (console_feedback_listener Format.err_formatter)) in
  let prog, args =
    let args = Array.to_list Sys.argv in
    let prog = List.hd args in
    prog, List.tl args in

  let only_destination, args = match args with
    | "-destination-of" :: tgt :: rest -> Some tgt, rest
    | _ -> None, args in

  let project = 
    try cmdline_args_to_project ~curdir:Filename.current_dir_name args
    with Parsing_error s -> prerr_endline s; usage_coq_makefile () in

  if only_destination <> None then begin
    destination_of project (Option.get only_destination);
    exit 0
  end;

  if project.makefile = None then
    eprintf "Warning: Omitting -o is deprecated\n\n";
    (* We want to know the name of the Makefile (say m) in order to
     * generate m.conf and include m.local *)

  let conf_file = Option.default "CoqMakefile" project.makefile ^ ".conf" in
  let local_file = Option.default "CoqMakefile" project.makefile ^ ".local" in

  if project.extra_targets <> [] then begin
    eprintf "Warning: -extra and -extra-phony are deprecated.\n";
    eprintf "Warning: Write the extra targets in %s.\n\n" local_file;
  end;

  if project.subdirs <> [] then begin
    eprintf "Warning: Subdirectories are deprecated.\n";
    eprintf "Warning: Use double colon rules in %s.\n\n" local_file;
  end;

  let project = ensure_root_dir project in
  
  if project.install_kind <> (Some CoqProject_file.NoInstall) then begin
    warn_install_at_root_directory project;
  end;

  check_overlapping_include project;

  Envars.set_coqlib ~fail:(fun x -> Printf.eprintf "Error: %s\n" x; exit 1);
  
  let ocm = Option.cata open_out stdout project.makefile in
  generate_makefile ocm conf_file local_file (prog :: args) project;
  close_out ocm;
  let occ = open_out conf_file in
  generate_conf occ project (prog :: args);
  close_out occ;
  exit 0

