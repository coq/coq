(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Compat
open Pp
open Util
open System
open Flags
open Names
open Term
open Check

let coq_root = id_of_string "Coq"
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
      [] -> invalid_arg "dirpath_of_string"
    | dir -> make_dirpath (List.map id_of_string dir)
let path_of_string s =
  match parse_dir s with
      [] -> invalid_arg "dirpath_of_string"
    | l::dir -> {dirpath=dir; basename=l}

let (/) = Filename.concat

let get_version_date () =
  try
    let coqlib = Envars.coqlib () in
    let ch = open_in (Filename.concat coqlib "revision") in
    let ver = input_line ch in
    let rev = input_line ch in
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
    msg_warning (str ("Cannot open " ^ dir))

let convert_string d =
  try id_of_string d
  with _ ->
    if_verbose warning
      ("Directory "^d^" cannot be used as a Coq identifier (skipped)");
    flush_all ();
    failwith "caught"

let add_rec_path ~unix_path:dir ~coq_root:coq_dirpath =
  if exists_dir dir then
    let dirs = all_subdirs dir in
    let prefix = repr_dirpath coq_dirpath in
    let convert_dirs (lp,cp) =
      (lp,make_dirpath (List.map convert_string (List.rev cp)@prefix)) in
    let dirs = map_succeed convert_dirs dirs in
    List.iter Check.add_load_path dirs;
    Check.add_load_path (dir,coq_dirpath)
  else
    msg_warning (str ("Cannot open " ^ dir))

(* By the option -include -I or -R of the command line *)
let includes = ref []
let push_include (s, alias) = includes := (s,alias,false) :: !includes
let push_rec_include (s, alias) = includes := (s,alias,true) :: !includes

let set_default_include d =
  push_include (d, Check.default_root_prefix)
let set_default_rec_include d =
  let p = Check.default_root_prefix in
  push_rec_include (d, p)
let set_include d p =
  let p = dirpath_of_string p in
  push_include (d,p)
let set_rec_include d p =
  let p = dirpath_of_string p in
  push_rec_include(d,p)

(* Initializes the LoadPath *)
let init_load_path () =
  let coqlib = Envars.coqlib () in
  let user_contrib = coqlib/"user-contrib" in
  let plugins = coqlib/"plugins" in
  (* first user-contrib *)
  if Sys.file_exists user_contrib then
    add_rec_path user_contrib Check.default_root_prefix;
  (* then plugins *)
  add_rec_path plugins (Names.make_dirpath [coq_root]);
  (* then standard library *)
(*  List.iter
    (fun (s,alias) ->
      add_rec_path (coqlib/s) ([alias; coq_root]))
    theories_dirs_map;*)
  add_rec_path (coqlib/"theories") (Names.make_dirpath[coq_root]);
  (* then current directory *)
  add_path "." Check.default_root_prefix;
  (* additional loadpath, given with -I -include -R options *)
  List.iter
    (fun (s,alias,reci) ->
      if reci then add_rec_path s alias else add_path s alias)
    (List.rev !includes);
  includes := []


let set_debug () = Flags.debug := true

let engagement = ref None
let set_engagement c = engagement := Some c
let engage () =
  match !engagement with Some c -> Safe_typing.set_engagement c | None -> ()


let admit_list = ref ([] : section_path list)
let add_admit s =
  admit_list := path_of_string s :: !admit_list

let norec_list = ref ([] : section_path list)
let add_norec s =
  norec_list := path_of_string s :: !norec_list

let compile_list = ref ([] : section_path list)
let add_compile s =
  compile_list := path_of_string s :: !compile_list

(*s Parsing of the command line.
    We no longer use [Arg.parse], in order to use share [Usage.print_usage]
    between coqtop and coqc. *)

let compile_files () =
  Check.recheck_library
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
  output_string co "Coq options are:\n";
  output_string co
"  -I dir -as coqdir      map physical dir to logical coqdir\
\n  -I dir                 map directory dir to the empty logical path\
\n  -include dir           (idem)\
\n  -R dir -as coqdir      recursively map physical dir to logical coqdir\
\n  -R dir coqdir          (idem)\
\n\
\n  -admit module          load module and dependencies without checking\
\n  -norec module          check module but admit dependencies without checking\
\n\
\n  -where                 print Coq's standard library location and exit\
\n  -v                     print Coq version and exit\
\n  -boot                  boot mode\
\n  -o, --output-context   print the list of assumptions\
\n  -m, --memoty           print the maximum heap size\
\n  -silent                disable trace of constants being checked\
\n\
\n  -impredicative-set     set sort Set impredicative\
\n\
\n  -h, --help             print this list of options\
\n"

(* print the usage on standard error *)

let print_usage = print_usage_channel stderr

let print_usage_coqtop () =
  print_usage "Usage: coqchk <options>\n\n"

let usage () =
  print_usage_coqtop ();
  flush stderr;
  exit 1

let warning s = msg_warning (str s)

open Type_errors

let anomaly_string () = str "Anomaly: "
let report () = (str "." ++ spc () ++ str "Please report.")

let print_loc loc =
  if loc = dummy_loc then
    (str"<unknown>")
  else
    let loc = unloc loc in
    (int (fst loc) ++ str"-" ++ int (snd loc))
let guill s = "\""^s^"\""

let where s =
  if !Flags.debug then  (str"in " ++ str s ++ str":" ++ spc ()) else (mt ())

let rec explain_exn = function
  | Stream.Failure ->
      hov 0 (anomaly_string () ++ str "uncaught Stream.Failure.")
  | Stream.Error txt ->
      hov 0 (str "Syntax error: " ++ str txt)
  | Token.Error txt ->
      hov 0 (str "Syntax error: " ++ str txt)
  | Sys_error msg ->
      hov 0 (anomaly_string () ++ str "uncaught exception Sys_error " ++ str (guill msg) ++ report() )
  | UserError(s,pps) ->
      hov 1 (str "User error: " ++ where s ++ pps)
  | Out_of_memory ->
      hov 0 (str "Out of memory")
  | Stack_overflow ->
      hov 0 (str "Stack overflow")
  | Anomaly (s,pps) ->
      hov 1 (anomaly_string () ++ where s ++ pps ++ report ())
  | Match_failure(filename,pos1,pos2) ->
      hov 1 (anomaly_string () ++ str "Match failure in file " ++
	     str (guill filename) ++ str " at line " ++ int pos1 ++
	     str " character " ++ int pos2 ++ report ())
  | Not_found ->
      hov 0 (anomaly_string () ++ str "uncaught exception Not_found" ++ report ())
  | Failure s ->
      hov 0 (str "Failure: " ++ str s ++ report ())
  | Invalid_argument s ->
      hov 0 (anomaly_string () ++ str "uncaught exception Invalid_argument " ++ str (guill s) ++ report ())
  | Sys.Break ->
      hov 0 (fnl () ++ str "User interrupt.")
  | Univ.UniverseInconsistency (o,u,v) ->
      let msg =
	if !Flags.debug (*!Constrextern.print_universes*) then
	  spc() ++ str "(cannot enforce" ++ spc() ++ (*Univ.pr_uni u ++*) spc() ++
          str (match o with Univ.Lt -> "<" | Univ.Le -> "<=" | Univ.Eq -> "=")
	  ++ spc() ++ (*Univ.pr_uni v ++*) str")"
	else
	  mt() in
      hov 0 (str "Error: Universe inconsistency" ++ msg ++ str ".")
  | TypeError(ctx,te) ->
(*      hov 0 (str "Error:" ++ spc () ++ Himsg.explain_type_error ctx *)
      (*      te)*)
      hov 0 (str "Type error")

  | Indtypes.InductiveError e ->
      hov 0 (str "Error related to inductive types")
(*      let ctx = Check.get_env() in
      hov 0
        (str "Error:" ++ spc () ++ Himsg.explain_inductive_error ctx e)*)
  | Loc.Exc_located (loc,exc) ->
      hov 0 ((if loc = dummy_loc then (mt ())
               else (str"At location " ++ print_loc loc ++ str":" ++ fnl ()))
               ++ explain_exn exc)
  | Assert_failure (s,b,e) ->
      hov 0 (anomaly_string () ++ str "assert failure" ++ spc () ++
	       (if s = "" then mt ()
		else
		  (str ("(file \"" ^ s ^ "\", line ") ++ int b ++
		   str ", characters " ++ int e ++ str "-" ++
		   int (e+6) ++ str ")")) ++
	       report ())
  | reraise ->
      hov 0 (anomaly_string () ++ str "Uncaught exception " ++
	       str (Printexc.to_string reraise)++report())

let parse_args argv =
  let rec parse = function
    | [] -> ()
   | "-impredicative-set" :: rem ->
       set_engagement Declarations.ImpredicativeSet; parse rem

    | ("-I"|"-include") :: d :: "-as" :: p :: rem -> set_include d p; parse rem
    | ("-I"|"-include") :: d :: "-as" :: [] -> usage ()
    | ("-I"|"-include") :: d :: rem -> set_default_include d; parse rem
    | ("-I"|"-include") :: []       -> usage ()

    | "-R" :: d :: "-as" :: p :: rem -> set_rec_include d p;parse rem
    | "-R" :: d :: "-as" :: [] -> usage ()
    | "-R" :: d :: p :: rem -> set_rec_include d p;parse rem
    | "-R" :: ([] | [_]) -> usage ()

    | "-debug" :: rem -> set_debug (); parse rem

    | "-where" :: _ ->
        print_endline (Envars.coqlib ()); exit 0

    | ("-?"|"-h"|"-H"|"-help"|"--help") :: _ -> usage ()

    | ("-v"|"--version") :: _ -> version ()
    | "-boot" :: rem -> boot := true; parse rem
    | ("-m" | "--memory") :: rem -> Check_stat.memory_stat := true; parse rem
    | ("-o" | "--output-context") :: rem ->
        Check_stat.output_context := true; parse rem

    | "-no-hash-consing" :: rem -> Flags.hash_cons_proofs := false; parse rem

    | "-admit" :: s :: rem -> add_admit s; parse rem
    | "-admit" :: [] -> usage ()

    | "-norec" :: s :: rem -> add_norec s; parse rem
    | "-norec" :: [] -> usage ()

    | "-silent" :: rem ->
        Flags.make_silent true; parse rem

    | s :: _ when s<>"" && s.[0]='-' ->
        msgnl (str "Unknown option " ++ str s); exit 1
    | s :: rem ->  add_compile s; parse rem
  in
  try
    parse (List.tl (Array.to_list argv))
  with
    | UserError(_,s) as e -> begin
	try
	  Stream.empty s; exit 1
	with Stream.Failure ->
	  msgnl (explain_exn e); exit 1
      end
    | e -> begin msgnl (explain_exn e); exit 1 end


(* To prevent from doing the initialization twice *)
let initialized = ref false

let init_with_argv argv =
  if not !initialized then begin
    initialized := true;
    Sys.catch_break false; (* Ctrl-C is fatal during the initialisation *)
    try
      parse_args argv;
      if_verbose print_header ();
      init_load_path ();
      engage ();
    with e ->
      flush_all();
      message "Error during initialization :";
      msgnl (explain_exn e);
      exit 1
  end

let init() = init_with_argv Sys.argv

let run () =
  try
    compile_files ();
    flush_all()
  with e ->
    (Pp.ppnl(explain_exn e);
    flush_all();
    exit 1)

let start () = init(); run(); Check_stat.stats(); exit 0
