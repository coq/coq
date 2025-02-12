(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
open Environ

let () = at_exit flush_all

let fatal_error info anomaly =
  flush_all (); Format.eprintf "@[Fatal Error: @[%a@]@]@\n%!" Pp.pp_with info; flush_all ();
  exit (if anomaly then 129 else 1)

let rocq_root = Id.of_string "Corelib"
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
  | [] -> CheckLibrary.default_root_prefix
  | dir -> DirPath.make (List.map Id.of_string dir)
let path_of_string s =
  if Filename.check_suffix s ".vo" then CheckLibrary.PhysicalFile s
  else match parse_dir s with
    | [] -> invalid_arg "path_of_string"
    | l::dir -> CheckLibrary.LogicalFile {dirpath=dir; basename=l}

let get_version () =
  try
    let env = Boot.Env.init () in
    let revision = Boot.Env.(Path.to_string (revision env)) in
    let ch = open_in revision in
    let ver = input_line ch in
    let rev = input_line ch in
    let () = close_in ch in
    Printf.sprintf "%s (%s)" ver rev
  with Sys_error _ | End_of_file -> Coq_config.version

let print_header () =
  Printf.printf "Welcome to Chicken %s\n%!" (get_version ())

(* Adding files to Rocq loadpath *)

let add_path ~unix_path:dir ~rocq_root:rocq_dirpath =
  if exists_dir dir then
    begin
      CheckLibrary.add_load_path (dir,rocq_dirpath)
    end
  else
    Feedback.msg_warning (str "Cannot open " ++ str dir)

let convert_string d =
  try Id.of_string d
  with CErrors.UserError _ ->
    Flags.if_verbose Feedback.msg_warning
      (str "Directory " ++ str d ++ str " cannot be used as a Rocq identifier (skipped)");
    raise_notrace Exit

let add_rec_path ~unix_path ~rocq_root =
  if exists_dir unix_path then
    let dirs = all_subdirs ~unix_path in
    let prefix = DirPath.repr rocq_root in
    let convert_dirs (lp, cp) =
      try
        let path = List.rev_map convert_string cp @ prefix in
        Some (lp, Names.DirPath.make path)
      with Exit -> None
    in
    let dirs = List.map_filter convert_dirs dirs in
    List.iter CheckLibrary.add_load_path dirs;
    CheckLibrary.add_load_path (unix_path, rocq_root)
  else
    Feedback.msg_warning (str "Cannot open " ++ str unix_path)

(* By the option -R/-Q of the command line *)
let includes = ref []
let push_include (s, alias) = includes := (s,alias) :: !includes

let set_include d p =
  let p = if String.equal p "Coq" then "Corelib" else p in
  let p = dirpath_of_string p in
  push_include (d,p)

(* Initializes the LoadPath *)
let init_load_path () =
  let rocqenv = Boot.Env.init () in
  (* the to_string casting won't be necessary once Boot handles
     include paths *)
  let plugins = Boot.Env.plugins rocqenv |> Boot.Path.to_string in
  let theories = Boot.Env.stdlib rocqenv |> Boot.Path.to_string in
  let user_contrib = Boot.Env.user_contrib rocqenv |> Boot.Path.to_string in
  let xdg_dirs = Envars.xdg_dirs in
  let rocqpath = Envars.coqpath in
  (* NOTE: These directories are searched from last to first *)
  (* first standard library *)
  add_rec_path ~unix_path:theories ~rocq_root:(Names.DirPath.make[rocq_root]);
  (* then plugins *)
  add_rec_path ~unix_path:plugins ~rocq_root:(Names.DirPath.make [rocq_root]);
  (* then user-contrib *)
  if Sys.file_exists user_contrib then
    add_rec_path ~unix_path:user_contrib ~rocq_root:CheckLibrary.default_root_prefix;
  (* then directories in XDG_DATA_DIRS and XDG_DATA_HOME *)
  List.iter (fun s -> add_rec_path ~unix_path:s ~rocq_root:CheckLibrary.default_root_prefix)
    (xdg_dirs ~warn:(fun x -> Feedback.msg_warning (str x)));
  (* then directories in ROCQPATH *)
  List.iter (fun s -> add_rec_path ~unix_path:s ~rocq_root:CheckLibrary.default_root_prefix) (rocqpath());
  (* then current directory *)
  add_path ~unix_path:"." ~rocq_root:CheckLibrary.default_root_prefix

let init_load_path () : unit =
  NewProfile.profile "init_load_path"
    init_load_path
    ()

let impredicative_set = ref false
let set_impredicative_set () = impredicative_set := true

let boot = ref false
let set_boot () = boot := true

let indices_matter = ref false

let enable_vm = ref false

let make_senv () =
  let senv = Safe_typing.empty_environment in
  let senv = Safe_typing.set_impredicative_set !impredicative_set senv in
  let senv = Safe_typing.set_indices_matter !indices_matter senv in
  let senv = Safe_typing.set_VM !enable_vm senv in
  let senv = Safe_typing.set_allow_sprop true senv in (* be smarter later *)
  Safe_typing.set_native_compiler false senv

let admit_list = ref ([] : CheckLibrary.object_file list)
let add_admit s =
  admit_list := path_of_string s :: !admit_list

let norec_list = ref ([] : CheckLibrary.object_file list)
let add_norec s =
  norec_list := path_of_string s :: !norec_list

let compile_list = ref ([] : CheckLibrary.object_file list)
let add_compile s =
  compile_list := path_of_string s :: !compile_list

(*s Parsing of the command line.
    We no longer use [Arg.parse], in order to use share [Usage.print_usage]
    between coqtop and coqc. *)

let compile_files senv =
  CheckLibrary.recheck_library senv
    ~norec:(List.rev !norec_list)
    ~admit:(List.rev !admit_list)
    ~check:(List.rev !compile_list)

let version () =
  Printf.printf "The Rocq Proof Checker, version %s\n" Coq_config.version;
  exit 0

(* print the usage of coqtop (or coqc) on channel co *)

let print_usage_channel co command =
  output_string co command;
  output_string co "coqchk options are:\n";
  output_string co
"\
\n  -Q dir coqdir               map physical dir to logical coqdir\
\n  -R dir coqdir               synonymous for -Q\
\n  -coqlib dir                 set coqchk's standard library location\
\n  -boot                       don't initialize the library paths automatically\
\n\
\n  -admit module               load module and dependencies without checking\
\n  -norec module               check module but admit dependencies without checking\
\n\
\n  -d (d1,..,dn)               enable specified debug messages\
\n  -debug                      enable all debug messages\
\n  -profile file               output profiling info to file\
\n  -where                      print coqchk's standard library location and exit\
\n  -v, --version               print coqchk version and exit\
\n  -o, --output-context        print the list of assumptions\
\n  -m, --memory                print the maximum heap size\
\n  -silent                     disable trace of constants being checked\
\n\
\n  -impredicative-set          set sort Set impredicative\
\n  -indices-matter             levels of indices (and nonuniform parameters)\
\n                              contribute to the level of inductives\
\n  -bytecode-compiler (yes|no) enable the vm_compute reduction machine (default is no)\
\n\
\n  -h, --help                  print this list of options\
\n"

(* print the usage on standard error *)

let print_usage = print_usage_channel stderr

let print_usage_rocqtop () =
  print_usage "Usage: coqchk <options> modules\n\n"

let usage exitcode =
  print_usage_rocqtop ();
  flush stderr;
  exit exitcode

open Type_errors

let anomaly_string () = str "Anomaly: "
let report () = strbrk (". Please report at " ^ Coq_config.wwwbugtracker ^ ".")

let guill s = str "\"" ++ str s ++ str "\""

let explain_exn = function
  | Sys_error msg ->
      hov 0 (anomaly_string () ++ str "uncaught exception Sys_error " ++ guill msg ++ report() )
  | UserError pps ->
      hov 1 (str "User error: " ++ pps)
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
  | UGraph.UniverseInconsistency i ->
    let msg =
      if CDebug.(get_flag misc) then
        str "." ++ spc() ++
          UGraph.explain_universe_inconsistency Sorts.QVar.raw_pr Univ.Level.raw_pr i
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
      | CaseOnPrivateInd _ -> str"CaseOnPrivateInd"
      | WrongCaseInfo _ -> str"WrongCaseInfo"
      | NumberBranches _ -> str"NumberBranches"
      | IllFormedBranch _ -> str"IllFormedBranch"
      | IllFormedCaseParams -> str "IllFormedCaseParams"
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
                             (UGraph.pr_universes Univ.Level.raw_pr
                                (UGraph.repr (Environ.universes ctx))));
        str "CantApplyBadType at argument " ++ int n
      | CantApplyNonFunctional _ -> str"CantApplyNonFunctional"
      | IllFormedRecBody _ -> str"IllFormedRecBody"
      | IllTypedRecBody _ -> str"IllTypedRecBody"
      | UnsatisfiedQConstraints _ -> str"UnsatisfiedQConstraints"
      | UnsatisfiedConstraints _ -> str"UnsatisfiedConstraints"
      | DisallowedSProp -> str"DisallowedSProp"
      | BadBinderRelevance _ -> str"BadBinderRelevance"
      | BadCaseRelevance _ -> str"BadCaseRelevance"
      | BadInvert -> str"BadInvert"
      | UndeclaredQualities _ -> str"UndeclaredQualities"
      | UndeclaredUniverses _ -> str"UndeclaredUniverse"
      | BadVariance _ -> str "BadVariance"
      | UndeclaredUsedVariables _ -> str "UndeclaredUsedVariables"
      ))

  | InductiveError (env,e) ->
      hov 0 (str "Error related to inductive types")
(*      let ctx = Check.get_env() in
      hov 0
        (str "Error:" ++ spc () ++ Himsg.explain_inductive_error ctx e)*)

  | CheckInductive.InductiveMismatch (mind,field) ->
    hov 0 (MutInd.print mind ++ str ": field " ++ str field ++ str " is incorrect.")

  | Mod_checking.BadConstant (cst, why) ->
    hov 0 (Constant.print cst ++ spc() ++ why)

  | Assert_failure (s,b,e) ->
      hov 0 (anomaly_string () ++ str "assert failure" ++ spc () ++
               (if s = "" then mt ()
                else
                  (str "(file \"" ++ str s ++ str "\", line " ++ int b ++
                   str ", characters " ++ int e ++ str "-" ++
                   int (e+6) ++ str ")")) ++
               report ())
  | e -> CErrors.print e (* for anomalies and other uncaught exceptions *)

let profile = ref None

let parse_args argv =
  let rec parse = function
    | [] -> ()
    | "-impredicative-set" :: rem ->
      set_impredicative_set (); parse rem

    | "-indices-matter" :: rem ->
      indices_matter:=true; parse rem

    | "-bytecode-compiler" :: "yes" :: rem ->
      enable_vm := true; parse rem
    | "-bytecode-compiler" :: "no" :: rem ->
      enable_vm := false; parse rem

    | "-coqlib" :: s :: rem ->
      if not (exists_dir s) then
        fatal_error (str "Directory '" ++ str s ++ str "' does not exist") false;
      Boot.Env.set_coqlib s;
      parse rem

    | "-boot" :: rem ->
      set_boot ();
      parse rem

    | ("-Q"|"-R") :: d :: p :: rem -> set_include d p;parse rem
    | ("-Q"|"-R") :: ([] | [_]) -> usage 1

    | "-d" :: s :: rem ->
      CDebug.set_flags s;
      parse rem
    | "-debug" :: rem -> CDebug.set_debug_all true; parse rem

    | "-profile" :: s :: rem ->
      profile := Some s;
      parse rem

    | "-profile" :: [] -> usage 1

    | "-where" :: _ ->
      let env = Boot.Env.init () in
      let rocqlib = Boot.Env.coqlib env |> Boot.Path.to_string in
      print_endline rocqlib;
      exit 0

    | ("-?"|"-h"|"-H"|"-help"|"--help") :: _ -> usage 0

    | ("-v"|"--version") :: _ -> version ()
    | ("-m" | "--memory") :: rem -> Check_stat.memory_stat := true; parse rem
    | ("-o" | "--output-context") :: rem ->
        Check_stat.output_context := true; parse rem

    | "-admit" :: s :: rem -> add_admit s; parse rem
    | "-admit" :: [] -> usage 1

    | "-norec" :: s :: rem -> add_norec s; parse rem
    | "-norec" :: [] -> usage 1

    | "-silent" :: rem ->
        Flags.quiet := true; parse rem

    | s :: _ when s<>"" && s.[0]='-' ->
        fatal_error (str "Unknown option " ++ str s) false
    | s :: rem ->  add_compile s; parse rem
  in
  parse (List.tl (Array.to_list argv))

let init_profile ~file =
  let ch = open_out file in
  let fname = Filename.basename file in
  NewProfile.init { output = Format.formatter_of_out_channel ch; fname; };
  at_exit (fun () ->
      NewProfile.finish ();
      close_out ch)

(* XXX: At some point we need to either port the checker to use the
   feedback system or to remove its use completely. *)
let init_with_argv argv =
  let _fhandle = Feedback.(add_feeder (console_feedback_listener Format.err_formatter)) in
  try
    parse_args argv;
    Option.iter (fun file -> init_profile ~file) !profile;
    if CDebug.(get_flag misc) then Printexc.record_backtrace true;
    Flags.if_verbose print_header ();
    if not !boot then init_load_path ();
    (* additional loadpath, given with -R/-Q options *)
    NewProfile.profile "add_load_paths" (fun () ->
        List.iter
          (fun (unix_path, rocq_root) -> add_rec_path ~unix_path ~rocq_root)
          (List.rev !includes))
      ();
    includes := [];
    make_senv ()
  with e ->
    fatal_error (str "Error during initialization :" ++ (explain_exn e)) (is_anomaly e)

let init() = init_with_argv Sys.argv

let run senv =
  try
    let senv = compile_files senv in
    flush_all(); senv
  with e ->
    if CDebug.(get_flag misc) then Printexc.print_backtrace stderr;
    fatal_error (explain_exn e) (is_anomaly e)

let main () =
  let senv = init() in
  let senv, opac = run senv in
  Check_stat.stats (Safe_typing.env_of_safe_env senv) opac;
  exit 0
