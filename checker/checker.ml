(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open System
open Names
open Check
open Environ

let () = at_exit flush_all

let fatal_error info anomaly =
  flush_all (); Format.eprintf "@[Fatal Error: @[%a@]@]@\n%!" Pp.pp_with info; flush_all ();
  exit (if anomaly then 129 else 1)

let coq_root = Id.of_string "Coq"
let parse_dir s =
  let len = String.length s in
  let rec decoupe_dirs dirs n =
    if n>=len then dirs else
    let pos =
      try
	String.index_from s n '.'
      with Not_found -> len
    in
    let dir = String.sub s n (pos-n) in
      decoupe_dirs (dir::dirs) (pos+1)
  in
    decoupe_dirs [] 0
let dirpath_of_string s =
  match parse_dir s with
      [] -> Check.default_root_prefix
    | dir -> DirPath.make (List.map Id.of_string dir)
let path_of_string s =
  if Filename.check_suffix s ".vo" then PhysicalFile s
  else match parse_dir s with
      [] -> invalid_arg "path_of_string"
    | l::dir -> LogicalFile {dirpath=dir; basename=l}

let ( / ) = Filename.concat

let get_version_date () =
  try
    let ch = open_in (Envars.coqlib () / "revision") in
    let ver = input_line ch in
    let rev = input_line ch in
    let () = close_in ch in
    (ver,rev)
  with _ -> (Coq_config.version,Coq_config.date)

let print_header () =
  let (ver,rev) = (get_version_date ()) in
  Printf.printf "Welcome to Chicken %s (%s)\n" ver rev;
  flush stdout

(* Adding files to Coq loadpath *)

let add_path ~unix_path:dir ~coq_root:coq_dirpath =
  if exists_dir dir then
    begin
      Check.add_load_path (dir,coq_dirpath)
    end
  else
    Feedback.msg_warning (str "Cannot open " ++ str dir)

let convert_string d =
  try Id.of_string d
  with CErrors.UserError _ ->
    Flags.if_verbose Feedback.msg_warning
      (str "Directory " ++ str d ++ str " cannot be used as a Coq identifier (skipped)");
    raise Exit

let add_rec_path ~unix_path ~coq_root =
  if exists_dir unix_path then
    let dirs = all_subdirs ~unix_path in
    let prefix = DirPath.repr coq_root in
    let convert_dirs (lp, cp) =
      try
        let path = List.rev_map convert_string cp @ prefix in
        Some (lp, Names.DirPath.make path)
      with Exit -> None
    in
    let dirs = List.map_filter convert_dirs dirs in
    List.iter Check.add_load_path dirs;
    Check.add_load_path (unix_path, coq_root)
  else
    Feedback.msg_warning (str "Cannot open " ++ str unix_path)

(* By the option -include -I or -R of the command line *)
let includes = ref []
let push_include (s, alias) = includes := (s,alias) :: !includes

let set_default_include d =
  push_include (d, Check.default_root_prefix)
let set_include d p =
  let p = dirpath_of_string p in
  push_include (d,p)

(* Initializes the LoadPath *)
let init_load_path () =
  let coqlib = Envars.coqlib () in
  let user_contrib = coqlib/"user-contrib" in
  let xdg_dirs = Envars.xdg_dirs in
  let coqpath = Envars.coqpath in
  let plugins = coqlib/"plugins" in
  (* NOTE: These directories are searched from last to first *)
  (* first standard library *)
  add_rec_path ~unix_path:(coqlib/"theories") ~coq_root:(Names.DirPath.make[coq_root]);
  (* then plugins *)
  add_rec_path ~unix_path:plugins ~coq_root:(Names.DirPath.make [coq_root]);
  (* then user-contrib *)
  if Sys.file_exists user_contrib then
    add_rec_path ~unix_path:user_contrib ~coq_root:Check.default_root_prefix;
  (* then directories in XDG_DATA_DIRS and XDG_DATA_HOME *)
  List.iter (fun s -> add_rec_path ~unix_path:s ~coq_root:Check.default_root_prefix)
    (xdg_dirs ~warn:(fun x -> Feedback.msg_warning (str x)));
  (* then directories in COQPATH *)
  List.iter (fun s -> add_rec_path ~unix_path:s ~coq_root:Check.default_root_prefix) coqpath;
  (* then current directory *)
  add_path ~unix_path:"." ~coq_root:Check.default_root_prefix;
  (* additional loadpath, given with -I -include -R options *)
  List.iter
    (fun (unix_path, coq_root) -> add_rec_path ~unix_path ~coq_root)
    (List.rev !includes);
  includes := []


let set_debug () = Flags.debug := true

let impredicative_set = ref Declarations.PredicativeSet
let set_impredicative_set () = impredicative_set := Declarations.ImpredicativeSet

let indices_matter = ref false

let make_senv () =
  let senv = Safe_typing.empty_environment in
  let senv = Safe_typing.set_engagement !impredicative_set senv in
  let senv = Safe_typing.set_indices_matter !indices_matter senv in
  let senv = Safe_typing.set_VM false senv in
  let senv = Safe_typing.set_allow_sprop true senv in (* be smarter later *)
  Safe_typing.set_native_compiler false senv

let admit_list = ref ([] : object_file list)
let add_admit s =
  admit_list := path_of_string s :: !admit_list

let norec_list = ref ([] : object_file list)
let add_norec s =
  norec_list := path_of_string s :: !norec_list

let compile_list = ref ([] : object_file list)
let add_compile s =
  compile_list := path_of_string s :: !compile_list

(*s Parsing of the command line.
    We no longer use [Arg.parse], in order to use share [Usage.print_usage]
    between coqtop and coqc. *)

let compile_files senv =
  Check.recheck_library senv
    ~norec:(List.rev !norec_list)
    ~admit:(List.rev !admit_list)
    ~check:(List.rev !compile_list)

let version () =
  Printf.printf "The Coq Proof Checker, version %s (%s)\n"
    Coq_config.version Coq_config.date;
  Printf.printf "compiled on %s\n" Coq_config.compile_date;
  exit 0

(* print the usage of coqtop (or coqc) on channel co *)

let print_usage_channel co command =
  output_string co command;
  output_string co "coqchk options are:\n";
  output_string co
"  -Q dir coqdir          map physical dir to logical coqdir\
\n  -R dir coqdir          synonymous for -Q\
\n\
\n\
\n  -admit module          load module and dependencies without checking\
\n  -norec module          check module but admit dependencies without checking\
\n\
\n  -coqlib dir            set coqchk's standard library location\
\n  -where                 print coqchk's standard library location and exit\
\n  -v                     print coqchk version and exit\
\n  -o, --output-context   print the list of assumptions\
\n  -m, --memory           print the maximum heap size\
\n  -silent                disable trace of constants being checked\
\n\
\n  -impredicative-set     set sort Set impredicative\
\n\
\n  -h, --help             print this list of options\
\n"

(* print the usage on standard error *)

let print_usage = print_usage_channel stderr

let print_usage_coqtop () =
  print_usage "Usage: coqchk <options> modules\n\n"

let usage () =
  print_usage_coqtop ();
  flush stderr;
  exit 1

open Type_errors

let anomaly_string () = str "Anomaly: "
let report () = strbrk (". Please report at " ^ Coq_config.wwwbugtracker ^ ".")

let guill s = str "\"" ++ str s ++ str "\""

let where = function
| None -> mt ()
| Some s ->
  if !Flags.debug then  (str"in " ++ str s ++ str":" ++ spc ()) else (mt ())

let explain_exn = function
  | Stream.Failure ->
      hov 0 (anomaly_string () ++ str "uncaught Stream.Failure.")
  | Stream.Error txt ->
      hov 0 (str "Syntax error: " ++ str txt)
  | Sys_error msg ->
      hov 0 (anomaly_string () ++ str "uncaught exception Sys_error " ++ guill msg ++ report() )
  | UserError(s,pps) ->
      hov 1 (str "User error: " ++ where s ++ pps)
  | Out_of_memory ->
      hov 0 (str "Out of memory")
  | Stack_overflow ->
      hov 0 (str "Stack overflow")
  | Match_failure(filename,pos1,pos2) ->
      hov 1 (anomaly_string () ++ str "Match failure in file " ++
	     guill filename ++ str " at line " ++ int pos1 ++
	     str " character " ++ int pos2 ++ report ())
  | Not_found ->
      hov 0 (anomaly_string () ++ str "uncaught exception Not_found" ++ report ())
  | Failure s ->
      hov 0 (str "Failure: " ++ str s ++ report ())
  | Invalid_argument s ->
      hov 0 (anomaly_string () ++ str "uncaught exception Invalid_argument " ++ guill s ++ report ())
  | Sys.Break ->
    hov 0 (fnl () ++ str "User interrupt.")
  | Univ.UniverseInconsistency i ->
    let msg =
      if !Flags.debug then
        str "." ++ spc() ++
          Univ.explain_universe_inconsistency Univ.Level.pr i
      else
        mt() in
      hov 0 (str "Error: Universe inconsistency" ++ msg ++ str ".")
  | TypeError(ctx,te) ->
      hov 0 (str "Type error: " ++
      (match te with
      | UnboundRel i -> str"UnboundRel " ++ int i
      | UnboundVar v -> str"UnboundVar" ++ str(Names.Id.to_string v)
      | NotAType _ -> str"NotAType"
      | BadAssumption _ -> str"BadAssumption"
      | ReferenceVariables _ -> str"ReferenceVariables"
      | ElimArity _ -> str"ElimArity"
      | CaseNotInductive _ -> str"CaseNotInductive"
      | WrongCaseInfo _ -> str"WrongCaseInfo"
      | NumberBranches _ -> str"NumberBranches"
      | IllFormedBranch _ -> str"IllFormedBranch"
      | Generalization _ -> str"Generalization"
      | ActualType _ -> str"ActualType"
      | IncorrectPrimitive _ -> str"IncorrectPrimitive"
      | CantApplyBadType ((n,a,b),{uj_val = hd; uj_type = hdty},args) ->
        let pp_arg i judge =
          hv 1 (str"arg " ++ int (i+1) ++ str"= " ++
                Constr.debug_print judge.uj_val ++
                str ",type= " ++ Constr.debug_print judge.uj_type) ++ fnl ()
        in
        Feedback.msg_notice (str"====== ill-typed term ====" ++ fnl () ++
                       hov 2 (str"application head= " ++ Constr.debug_print hd) ++ fnl () ++
                       hov 2 (str"head type= " ++ Constr.debug_print hdty) ++ fnl () ++
                       str"arguments:" ++ fnl () ++ hv 1 (prvecti pp_arg args));
        Feedback.msg_notice (str"====== type error ====@" ++ fnl () ++
                             Constr.debug_print b ++ fnl () ++
                             str"is not convertible with" ++ fnl () ++
                             Constr.debug_print a ++ fnl ());
        Feedback.msg_notice (str"====== universes ====" ++ fnl () ++
                             (UGraph.pr_universes Univ.Level.pr
                                (ctx.Environ.env_stratification.Environ.env_universes)));
        str "CantApplyBadType at argument " ++ int n
      | CantApplyNonFunctional _ -> str"CantApplyNonFunctional"
      | IllFormedRecBody _ -> str"IllFormedRecBody"
      | IllTypedRecBody _ -> str"IllTypedRecBody"
      | UnsatisfiedConstraints _ -> str"UnsatisfiedConstraints"
      | DisallowedSProp -> str"DisallowedSProp"
      | BadRelevance -> str"BadRelevance"
      | UndeclaredUniverse _ -> str"UndeclaredUniverse"))

  | InductiveError e ->
      hov 0 (str "Error related to inductive types")
(*      let ctx = Check.get_env() in
      hov 0
        (str "Error:" ++ spc () ++ Himsg.explain_inductive_error ctx e)*)

  | CheckInductive.InductiveMismatch (mind,field) ->
    hov 0 (MutInd.print mind ++ str ": field " ++ str field ++ str " is incorrect.")

  | Assert_failure (s,b,e) ->
      hov 0 (anomaly_string () ++ str "assert failure" ++ spc () ++
	       (if s = "" then mt ()
		else
		  (str "(file \"" ++ str s ++ str "\", line " ++ int b ++
		   str ", characters " ++ int e ++ str "-" ++
		   int (e+6) ++ str ")")) ++
	       report ())
  | e -> CErrors.print e (* for anomalies and other uncaught exceptions *)

let deprecated flag =
  Feedback.msg_warning (str "Deprecated flag " ++ quote (str flag))

let parse_args argv =
  let rec parse = function
    | [] -> ()
    | "-impredicative-set" :: rem ->
      set_impredicative_set (); parse rem

    | "-indices-matter" :: rem ->
      indices_matter:=true; parse rem

    | "-coqlib" :: s :: rem ->
      if not (exists_dir s) then 
	fatal_error (str "Directory '" ++ str s ++ str "' does not exist") false;
      Envars.set_user_coqlib s;
      parse rem

    | ("-I"|"-include") :: d :: "-as" :: p :: rem -> deprecated "-I"; set_include d p; parse rem
    | ("-I"|"-include") :: d :: "-as" :: [] -> usage ()
    | ("-I"|"-include") :: d :: rem -> deprecated "-I"; set_default_include d; parse rem
    | ("-I"|"-include") :: []       -> usage ()

    | "-Q" :: d :: p :: rem -> set_include d p;parse rem
    | "-Q" :: ([] | [_]) -> usage ()

    | "-R" :: d :: p :: rem -> set_include d p;parse rem
    | "-R" :: ([] | [_]) -> usage ()

    | "-debug" :: rem -> set_debug (); parse rem

    | "-where" :: _ ->
      Envars.set_coqlib ~fail:(fun x -> CErrors.user_err Pp.(str x));
      print_endline (Envars.coqlib ());
      exit 0

    | ("-?"|"-h"|"-H"|"-help"|"--help") :: _ -> usage ()

    | ("-v"|"--version") :: _ -> version ()
    | ("-m" | "--memory") :: rem -> Check_stat.memory_stat := true; parse rem
    | ("-o" | "--output-context") :: rem ->
        Check_stat.output_context := true; parse rem

    | "-admit" :: s :: rem -> add_admit s; parse rem
    | "-admit" :: [] -> usage ()

    | "-norec" :: s :: rem -> add_norec s; parse rem
    | "-norec" :: [] -> usage ()

    | "-silent" :: rem ->
        Flags.quiet := true; parse rem

    | s :: _ when s<>"" && s.[0]='-' ->
        fatal_error (str "Unknown option " ++ str s) false
    | s :: rem ->  add_compile s; parse rem
  in
  parse (List.tl (Array.to_list argv))


(* XXX: At some point we need to either port the checker to use the
   feedback system or to remove its use completely. *)
let init_with_argv argv =
  Sys.catch_break false; (* Ctrl-C is fatal during the initialisation *)
  let _fhandle = Feedback.(add_feeder (console_feedback_listener Format.err_formatter)) in
  try
    parse_args argv;
    CWarnings.set_flags ("+"^Typeops.warn_bad_relevance_name);
    if !Flags.debug then Printexc.record_backtrace true;
    Envars.set_coqlib ~fail:(fun x -> CErrors.user_err Pp.(str x));
    Flags.if_verbose print_header ();
    init_load_path ();
    make_senv ()
  with e ->
    fatal_error (str "Error during initialization :" ++ (explain_exn e)) (is_anomaly e)

let init() = init_with_argv Sys.argv

let run senv =
  try
    let senv = compile_files senv in
    flush_all(); senv
  with e ->
    if !Flags.debug then Printexc.print_backtrace stderr;
    fatal_error (explain_exn e) (is_anomaly e)

let start () =
  let senv = init() in
  let senv = run senv in
  Check_stat.stats (Safe_typing.env_of_safe_env senv);
  exit 0
