(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let fatal_error exn =
  Topfmt.(in_phase ~phase:ParsingCommandLine print_err_exn exn);
  let exit_code = if (CErrors.is_anomaly exn) then 129 else 1 in
  exit exit_code

let error_wrong_arg msg =
  prerr_endline msg; exit 1

let error_missing_arg s =
  prerr_endline ("Error: extra argument expected after option "^s^".");
  prerr_endline "See -help for the syntax of supported options.";
  exit 1

let error_debug () =
  prerr_endline "Error: The -debug option has been removed.";
  prerr_endline "Use the -d option for enabling debug output.";
  prerr_endline "For an OCaml backtrace use -bt instead.";
  prerr_endline "See -help for the syntax of supported options.";
  exit 1

(******************************************************************************)

type native_compiler = Coq_config.native_compiler =
  NativeOff | NativeOn of { ondemand : bool }

type top = TopLogical of Names.DirPath.t | TopPhysical of string

type option_command =
  | OptionSet of string option
  | OptionUnset
  | OptionAppend of string

type require_injection = { lib: string; prefix: string option; export: Lib.export_flag option; allow_failure: bool }

type injection_command =
  | OptionInjection of (Goptions.option_name * option_command)
  | RequireInjection of require_injection
  | WarnNoNative of string
  | WarnNativeDeprecated

type coqargs_logic_config = {
  impredicative_set : bool;
  indices_matter    : bool;
  type_in_type      : bool;
  rewrite_rules     : bool;
  toplevel_name     : top;
}

type time_config = ToFeedback | ToFile of string

type coqargs_config = {
  logic       : coqargs_logic_config;
  rcfile      : string option;
  coqlib      : string option;
  enable_VM   : bool;
  native_compiler : native_compiler;
  native_output_dir : CUnix.physical_path;
  native_include_dirs : CUnix.physical_path list;
  output_directory : CUnix.physical_path option;
  time : time_config option;
  test_mode : bool;
  profile : string option;
  print_emacs : bool;
}

type coqargs_pre = {
  boot        : bool;
  load_init   : bool;
  load_rcfile : bool;

  ml_includes : string list;
  vo_includes : Loadpath.vo_path list;

  load_vernacular_list : (string * bool) list;
  injections  : injection_command list;
}

type coqargs_query =
  | PrintWhere | PrintConfig
  | PrintVersion | PrintMachineReadableVersion
  | PrintHelp of Boot.Usage.specific_usage

type coqargs_main =
  | Queries of coqargs_query list
  | Run

type coqargs_post = {
  memory_stat : bool;
}

type t = {
  config : coqargs_config;
  pre : coqargs_pre;
  main : coqargs_main;
  post : coqargs_post;
}

let default_toplevel = Names.(DirPath.make [Id.of_string "Top"])

let default_native = Coq_config.native_compiler

let default_logic_config = {
  impredicative_set = false;
  indices_matter = false;
  type_in_type = false;
  rewrite_rules = false;
  toplevel_name = TopLogical default_toplevel;
}

let default_config = {
  logic        = default_logic_config;
  rcfile       = None;
  coqlib       = None;
  enable_VM    = true;
  native_compiler = default_native;
  native_output_dir = ".coq-native";
  native_include_dirs = [];
  output_directory = None;
  time = None;
  test_mode = false;
  profile = None;
  print_emacs  = false;

  (* Quiet / verbosity options should be here *)
}

let default_pre = {
  boot         = false;
  load_init    = true;
  load_rcfile  = true;
  ml_includes  = [];
  vo_includes  = [];
  load_vernacular_list = [];
  injections   = [];
}

let default_queries = []

let default_post = {
  memory_stat  = false;
}

let default = {
  config = default_config;
  pre    = default_pre;
  main   = Run;
  post   = default_post;
}

(******************************************************************************)
(* Functional arguments                                                       *)
(******************************************************************************)
let add_ml_include opts s =
  { opts with pre = { opts.pre with ml_includes = s :: opts.pre.ml_includes }}

let add_vo_include opts unix_path rocq_path implicit =
  let open Loadpath in
  let rocq_path = Libnames.dirpath_of_string rocq_path in
  { opts with pre = { opts.pre with vo_includes = {
        unix_path; coq_path = rocq_path; has_ml = false; implicit; recursive = true } :: opts.pre.vo_includes }}

let add_vo_require opts d ?(allow_failure=false) p export =
  { opts with pre = { opts.pre with injections = RequireInjection {lib=d; prefix=p; export; allow_failure} :: opts.pre.injections }}

let add_load_vernacular opts verb s =
    { opts with pre = { opts.pre with load_vernacular_list = (CUnix.make_suffix s ".v",verb) :: opts.pre.load_vernacular_list }}

let add_set_option opts opt_name value =
  { opts with pre = { opts.pre with injections = OptionInjection (opt_name, value) :: opts.pre.injections }}

let add_set_debug opts flags =
  add_set_option opts ["Debug"] (OptionAppend flags)

(** Options for proof general *)
let set_emacs opts =
  let opts = add_set_option opts Printer.print_goal_tag_opt_name (OptionSet None) in
  { opts with config = { opts.config with print_emacs = true }}

let set_logic f oval =
  { oval with config = { oval.config with logic = f oval.config.logic }}

let set_query opts q =
  { opts with main = match opts.main with
  | Run -> Queries (default_queries@[q])
  | Queries queries -> Queries (queries@[q])
  }

(******************************************************************************)
(* Parsing helpers                                                            *)
(******************************************************************************)
let get_bool ~opt = function
  | "yes" | "on" -> true
  | "no" | "off" -> false
  | _ ->
    error_wrong_arg ("Error: yes/no expected after option "^opt^".")

let get_int ~opt n =
  try int_of_string n
  with Failure _ ->
    error_wrong_arg ("Error: integer expected after option "^opt^".")
let get_int_opt ~opt n =
  if n = "" then None
  else Some (get_int ~opt n)

let get_float ~opt n =
  try float_of_string n
  with Failure _ ->
    error_wrong_arg ("Error: float expected after option "^opt^".")

let interp_set_option opt v old =
  let open Goptions in
  let opt = String.concat " " opt in
  match old with
  | BoolValue _ -> BoolValue (get_bool ~opt v)
  | IntValue _ -> IntValue (get_int_opt ~opt v)
  | StringValue _ -> StringValue v
  | StringOptValue _ -> StringOptValue (Some v)

let set_option = let open Goptions in function
  | opt, OptionUnset -> unset_option_value_gen ~locality:OptLocal opt
  | opt, OptionSet None -> set_bool_option_value_gen ~locality:OptLocal opt true
  | opt, OptionSet (Some v) -> set_option_value ~locality:OptLocal (interp_set_option opt) opt v
  | opt, OptionAppend v -> set_string_option_append_value_gen ~locality:OptLocal opt v

let to_opt_key = Str.(split (regexp " +"))

let parse_option_set opt =
  match String.index_opt opt '=' with
  | None -> to_opt_key opt, None
  | Some eqi ->
    let len = String.length opt in
    let v = String.sub opt (eqi+1) (len - eqi - 1) in
    to_opt_key (String.sub opt 0 eqi), Some v

let get_native_compiler s =
  (* We use two boolean flags because the four states make sense, even if
     only three are accessible to the user at the moment. The selection of the
     produced artifact(s) (`.vo`, `.coq-native`, ...) should be done by
     a separate flag, and the "ondemand" value removed. Once this is done, use
     [get_bool] here. *)
  let n = match s with
    | ("yes" | "on") -> NativeOn {ondemand=false}
    | "ondemand" -> NativeOn {ondemand=true}
    | ("no" | "off") -> NativeOff
    | _ ->
      error_wrong_arg ("Error: (yes|no|ondemand) expected after option -native-compiler.")
  in
  if n = NativeOff then n, []
  else if Coq_config.native_compiler = NativeOff then
    NativeOff, [WarnNativeDeprecated; WarnNoNative s]
  else n, [WarnNativeDeprecated]

(* Main parsing routine *)
(*s Parsing of the command line *)

let parse_args ~usage ~init arglist : t * string list =
  let args = ref arglist in
  let extras = ref [] in
  let rec parse oval = match !args with
  | [] ->
    (oval, List.rev !extras)
  | opt :: rem ->
    args := rem;
    let next () = match !args with
      | x::rem -> args := rem; x
      | [] -> error_missing_arg opt
    in
    let noval = begin match opt with

    (* Complex options with many args *)
    |"-I"|"-include" -> add_ml_include oval (next())
    |"-Q" ->
      let d = next () in
      let p = next () in
      let p = if String.equal p "Coq" then "Stdlib" else p in
      add_vo_include oval d p false
    |"-R" ->
      let d = next () in
      let p = next () in
      let p = if String.equal p "Coq" then "Stdlib" else p in
      add_vo_include oval d p true

    (* Options with one arg *)
    |"-coqlib" ->
      { oval with config = { oval.config with coqlib = Some (next ())
      }}

    |"-compat" ->
      let arg = String.split_on_char '.' (next ()) in
      let rocq_name = match arg with "8" :: _ -> "Coq" | _ -> "Rocq" in
      (* remove the above and replace by "Rocq" once theories/Compat/Coq820.v is removed *)
      let xy = String.concat "" (rocq_name :: arg) in
      add_vo_require oval xy ~allow_failure:true (Some "Stdlib") (Some Lib.Import)

    |"-exclude-dir" ->
      System.exclude_directory (next ()); oval

    |"-init-file" ->
      { oval with config = { oval.config with rcfile = Some (next ()); }}

    |"-load-vernac-source"|"-l" ->
      add_load_vernacular oval false (next ())

    |"-load-vernac-source-verbose"|"-lv" ->
      add_load_vernacular oval true (next ())

    |"-mangle-names" ->
      let oval = add_set_option oval ["Mangle"; "Names"] (OptionSet None) in
      add_set_option oval ["Mangle"; "Names"; "Prefix"] (OptionSet(Some(next ())))

    |"-profile-ltac-cutoff" ->
      let oval = add_set_option oval ["Ltac"; "Profiling"] (OptionSet None) in
      add_set_option oval ["Ltac"; "Profiling"; "Cutoff"] (OptionSet (Some (next ())))

    |"-load-vernac-object"|"-require" ->
      add_vo_require oval (next ()) None None

    |"-require-import" | "-ri" -> add_vo_require oval (next ()) None (Some Lib.Import)

    |"-require-export" | "-re" -> add_vo_require oval (next ()) None (Some Lib.Export)

    |"-require-from"|"-rfrom" ->
      let from = next () in add_vo_require oval (next ()) (Some from) None

    |"-compat-from" ->
      let from = next () in add_vo_require oval (next ()) ~allow_failure:true (Some from) (Some Lib.Import)

    |"-require-import-from" | "-rifrom" ->
      let from = next () in add_vo_require oval (next ()) (Some from) (Some Lib.Import)

    |"-require-export-from" | "-refrom" ->
      let from = next () in add_vo_require oval (next ()) (Some from) (Some Lib.Export)

    |"-top" ->
      let topname = Libnames.dirpath_of_string (next ()) in
      if Names.DirPath.is_empty topname then
        CErrors.user_err Pp.(str "Need a non empty toplevel module name.");
      { oval with config = { oval.config with logic = { oval.config.logic with toplevel_name = TopLogical topname }}}

    |"-topfile" ->
      { oval with config = { oval.config with logic = { oval.config.logic with toplevel_name = TopPhysical (next()) }}}

    |"-w" | "-W" ->
      let w = next () in
      if w = "none" then add_set_option oval ["Warnings"] (OptionSet(Some w))
      else add_set_option oval ["Warnings"] (OptionAppend w)

    |"-bytecode-compiler" ->
      { oval with config = { oval.config with enable_VM = get_bool ~opt (next ()) }}

    |"-native-compiler" ->
      let native_compiler, warn = get_native_compiler (next ()) in
      { oval with config = { oval.config with native_compiler };
                  pre = { oval.pre with injections = warn @ oval.pre.injections }}

    | "-set" ->
      let opt, v = parse_option_set @@ next() in
      add_set_option oval opt (OptionSet v)

    | "-unset" ->
      add_set_option oval (to_opt_key @@ next ()) OptionUnset

    |"-native-output-dir" ->
      let native_output_dir = next () in
      { oval with config = { oval.config with native_output_dir } }

    |"-output-dir" | "-output-directory" ->
      let dir = next () in
      let dir = if Filename.is_relative dir then Filename.concat (Sys.getcwd ()) dir else dir in
      { oval with config = { oval.config with output_directory = Some dir } }

    |"-nI" ->
      let include_dir = next () in
      { oval with config = {oval.config with native_include_dirs = include_dir :: oval.config.native_include_dirs } }

    (* Options with zero arg *)
    |"-test-mode" -> { oval with config = { oval.config with test_mode = true } }
    |"-beautify" -> Flags.beautify := true; Flags.record_comments := true; oval
    |"-config"|"--config" -> set_query oval PrintConfig

    |"-bt" -> add_set_debug oval "backtrace"
    (* -debug is deprecated *)
    |"-debug" -> error_debug ()
    |"-d" | "-D" -> add_set_debug oval (next())

    (* -xml-debug implies -debug. TODO don't be imperative here. *)
    |"-xml-debug" -> Flags.xml_debug := true; add_set_debug oval "all"

    |"-diffs" ->
      add_set_option oval Proof_diffs.opt_name @@ OptionSet (Some (next ()))
    |"-emacs" -> set_emacs oval
    |"-impredicative-set" ->
      set_logic (fun o -> { o with impredicative_set = true }) oval
    |"-allow-sprop" ->
      add_set_option oval Vernacentries.allow_sprop_opt_name (OptionSet None)
    |"-disallow-sprop" ->
      add_set_option oval Vernacentries.allow_sprop_opt_name OptionUnset
    |"-allow-rewrite-rules" -> set_logic (fun o -> { o with rewrite_rules = true }) oval
    |"-indices-matter" -> set_logic (fun o -> { o with indices_matter = true }) oval
    |"-m"|"--memory" -> { oval with post = { memory_stat = true }}
    |"-noinit"|"-nois" -> { oval with pre = { oval.pre with load_init = false }}
    |"-boot" -> { oval with pre = { oval.pre with boot = true }}
    |"-profile-ltac" -> add_set_option oval ["Ltac"; "Profiling"] (OptionSet None)
    |"-q" -> { oval with pre = { oval.pre with load_rcfile = false; }}
    |"-quiet"|"-silent" ->
      Flags.quiet := true;
      Flags.make_warn false;
      oval
    |"-time" -> { oval with config = { oval.config with time = Some ToFeedback }}
    |"-time-file" -> { oval with config = { oval.config with time = Some (ToFile (next())) }}
    | "-profile" -> { oval with config = { oval.config with profile = Some (next()) } }
    |"-type-in-type" -> set_logic (fun o -> { o with type_in_type = true }) oval
    |"-unicode" -> add_vo_require oval "Utf8_core" None (Some Lib.Import)
    |"-where" -> set_query oval PrintWhere
    |"-h"|"-H"|"-?"|"-help"|"--help" -> set_query oval (PrintHelp usage)
    |"-v"|"--version" -> set_query oval PrintVersion
    |"-print-version"|"--print-version" -> set_query oval PrintMachineReadableVersion

    (* Unknown option *)
    | s ->
      extras := s :: !extras;
      oval
    end in
    parse noval
  in
  try
    parse init
  with any -> fatal_error any

(* We need to reverse a few lists *)
let parse_args ~usage ~init args =
  let opts, extra = parse_args ~usage ~init args in
  let opts =
    { opts with
      pre = { opts.pre with
              ml_includes = List.rev opts.pre.ml_includes
            ; vo_includes = List.rev opts.pre.vo_includes
            ; load_vernacular_list = List.rev opts.pre.load_vernacular_list
            ; injections = List.rev opts.pre.injections
            }
    } in
  opts, extra

(******************************************************************************)
(* Startup LoadPath and Modules                                               *)
(******************************************************************************)

(* prelude_data == From Coq Require Import Prelude. *)
let prelude_data = RequireInjection { lib = "Prelude"; prefix = Some "Stdlib"; export = Some Lib.Import; allow_failure = false }

let injection_commands opts =
  if opts.pre.load_init then prelude_data :: opts.pre.injections else opts.pre.injections

let dirpath_of_file f =
  let ldir0 =
    try
      let lp = Loadpath.find_load_path (Filename.dirname f) in
      Loadpath.logical lp
    with Not_found -> Libnames.default_root_prefix
  in
  let f = try Filename.chop_extension (Filename.basename f) with Invalid_argument _ -> f in
  let id = Names.Id.of_string f in
  let ldir = Libnames.add_dirpath_suffix ldir0 id in
  ldir

let dirpath_of_top = function
  | TopPhysical f -> dirpath_of_file f
  | TopLogical dp -> dp
