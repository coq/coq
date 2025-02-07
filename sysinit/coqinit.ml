(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** GC tweaking *)

(** Work around a broken Gc.set function in released OCaml versions between
    4.08.0 and 4.11.1 inclusive. *)
let gc_set : Gc.control -> unit =
  let open Gc in
  let fixed_set control =
    let { custom_major_ratio; custom_minor_ratio; custom_minor_max_size; _ } = control in
    let control =
      {
        control with
        custom_major_ratio = custom_major_ratio lsr 1;
        custom_minor_ratio = custom_minor_ratio lsr 1;
        custom_minor_max_size = custom_minor_max_size lsr 1;
      }
    in
    Gc.set control
  in
  (* the fix has been backported to all of these branches, so any
     version after these will be fixed. *)
  match Coq_config.caml_version_nums with
  | [4;11;1]
  | [4;11;0]
  | [4;10;2]
  | [4;10;1]
  | [4;10;0]
  | [4;09;1]
  | [4;09;0]
  | [4;08;1]
  | [4;08;0] ->
    fixed_set
  | _ -> Gc.set

(** Rocq is a heavy user of persistent data structures and symbolic ASTs, so the
    minor heap is heavily solicited. Unfortunately, the default size is far too
    small, so we enlarge it a lot (128 times larger).

    To better handle huge memory consumers, we also augment the default major
    heap increment and the GC pressure coefficient.
*)

let set_gc_policy () =
  gc_set { (Gc.get ()) with
           Gc.minor_heap_size = 32*1024*1024 (* 32Mwords x 8 bytes/word = 256Mb *)
         ; Gc.space_overhead = 120
         }

let set_gc_best_fit () =
  gc_set { (Gc.get ()) with
           Gc.allocation_policy = 2      (* best-fit *)
         ; Gc.space_overhead = 200
         }

let init_gc () =
  try
    (* OCAMLRUNPARAM environment variable is set.
     * In that case, we let ocamlrun to use the values provided by the user.
     *)
    ignore (Sys.getenv "OCAMLRUNPARAM")

  with Not_found ->
    (* OCAMLRUNPARAM environment variable is not set.
     * In this case, we put in place our preferred configuration.
     *)
    set_gc_policy ();
    if Coq_config.caml_version_nums >= [4;10;0] then set_gc_best_fit () else ()

let init_ocaml () =
  init_gc ();
  (* Get error message (and backtrace if enabled) on Ctrl-C instead of just exiting the process *)
  Sys.catch_break true

let init_coqlib opts = match opts.Coqargs.config.Coqargs.coqlib with
  | None -> ()
  | Some s ->
    Boot.Env.set_coqlib s

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
  | Coqargs.TopPhysical f -> dirpath_of_file f
  | TopLogical dp -> Libnames.dirpath_of_string dp

let parse_arguments ~parse_extra ?(initial_args=Coqargs.default) args =
  let opts, extras = Coqargs.parse_args ~init:initial_args args in
  let customopts, extras = parse_extra opts extras in
  if not (CList.is_empty extras) then begin
    prerr_endline ("Don't know what to do with "^String.concat " " extras);
    prerr_endline "See -help for the list of supported options";
    exit 1
    end;
  opts, customopts

let print_memory_stat () =
  let open Pp in
  (* -m|--memory from the command-line *)
  Feedback.msg_notice
    (str "total heap size = " ++ int (CObj.heap_size_kb ()) ++ str " kbytes" ++ fnl ());
  (* operf-macro interface:
     https://github.com/OCamlPro/operf-macro *)
  try
    let fn = Sys.getenv "OCAML_GC_STATS" in
    let oc = open_out fn in
    Gc.print_stat oc;
    close_out oc
  with exn when CErrors.noncritical exn -> ()

let to_vo_path (x:Coqargs.vo_path) : Loadpath.vo_path = {
  implicit = x.implicit;
  unix_path = x.unix_path;
  coq_path = Libnames.dirpath_of_string x.rocq_path;
  recursive = true;
  }

let init_load_paths opts =
  let open Coqargs in
  let boot_ml_path, boot_vo_path =
    if opts.pre.boot then [],[]
    else
      let coqenv = Boot.Env.init () in
      Coqloadpath.init_load_path ~coqenv
  in
  let ml_path = opts.pre.ml_includes @ boot_ml_path in
  List.iter Mltop.add_ml_dir (List.rev ml_path);
  List.iter Loadpath.add_vo_path boot_vo_path;
  let env_ocamlpath =
    try [Sys.getenv "OCAMLPATH"]
    with Not_found -> []
  in
  let env_ocamlpath = ml_path @ env_ocamlpath in
  let ocamlpathsep = if Sys.unix then ":" else ";" in
  let env_ocamlpath = String.concat ocamlpathsep env_ocamlpath in
  Findlib.init ~env_ocamlpath ()

let init_profile ~file =
  let ch = open_out file in
  let fname = Filename.basename file in
  NewProfile.init { output = Format.formatter_of_out_channel ch; fname; };
  at_exit (fun () ->
      NewProfile.finish ();
      close_out ch)

let init_runtime ~usage opts =
  let open Coqargs in
  Vernacextend.static_linking_done ();
  Option.iter (fun file -> init_profile ~file) opts.config.profile;
  Lib.init ();
  init_coqlib opts;
  if opts.post.memory_stat then at_exit print_memory_stat;

  (* excluded directories *)
  List.iter System.exclude_directory opts.config.exclude_dirs;

  (* Paths for loading stuff *)
  init_load_paths opts;

  match opts.Coqargs.main with
  | Coqargs.Queries q -> List.iter (Boot.Env.print_query (Some usage)) q; exit 0
  | Coqargs.Run -> ()

let init_document opts =
  let open Coqargs in

  (* this isn't in init_load_paths because processes (typically
     vscoqtop) are allowed to have states with differing vo paths (but
     not with differing -boot or ml paths) *)
  List.iter (fun x -> Loadpath.add_vo_path @@ to_vo_path x) opts.pre.vo_includes;

  (* Kernel configuration *)
  Global.set_impredicative_set opts.config.logic.impredicative_set;
  Global.set_indices_matter opts.config.logic.indices_matter;
  Global.set_check_universes (not opts.config.logic.type_in_type);
  Global.set_VM opts.config.enable_VM;
  Global.set_native_compiler (match opts.config.native_compiler with NativeOff -> false | NativeOn _ -> true);
  Global.set_rewrite_rules_allowed opts.config.logic.rewrite_rules;

  (* XXX these flags should probably be in the summary *)
  (* Native output dir *)
  Nativelib.output_dir := opts.config.native_output_dir;
  Nativelib.include_dirs := opts.config.native_include_dirs;

  (* Default output dir *)
  Flags.output_directory := opts.config.output_directory;

  (* Test mode *)
  Flags.test_mode := opts.config.test_mode;

  (* beautify *)
  if opts.config.beautify then begin
    Flags.beautify := true;
    Flags.record_comments := true;
  end;

  if opts.config.quiet then begin
    Flags.quiet := true;
    Flags.make_warn false;
  end;

  ()

let warn_require_not_found =
  CWarnings.create ~name:"compatibility-module-not-found"
    ~category:CWarnings.CoreCategories.filesystem
    Pp.(fun (prefix, lib) ->
        strbrk "Did not find compatibility module " ++ Libnames.pr_qualid lib ++
        pr_opt (fun prefix -> str "with prefix " ++ Libnames.pr_qualid prefix)
          prefix ++ str ".")

let require_file ~intern ~prefix ~lib ~export ~allow_failure =
  let mp = Libnames.qualid_of_string lib in
  let mfrom = Option.map Libnames.qualid_of_string prefix in
  let exp = Option.map (function
      | Coqargs.Import -> Vernacexpr.Import, None
      | Coqargs.Export -> Vernacexpr.Export, None)
      export
  in
  try
    Flags.silently (Vernacentries.vernac_require ~intern mfrom exp) [mp,Vernacexpr.ImportAll]
  with (Synterp.UnmappedLibrary _ | Synterp.NotFoundLibrary _) when allow_failure ->
    warn_require_not_found (mfrom, mp)

let warn_no_native_compiler =
  CWarnings.create_in Nativeconv.w_native_disabled
    Pp.(fun s -> strbrk "Native compiler is disabled," ++
                   strbrk " -native-compiler " ++ strbrk s ++
                   strbrk " option ignored.")

let warn_deprecated_native_compiler =
  CWarnings.create ~name:"deprecated-native-compiler-option" ~category:Deprecation.Version.v8_14
         (fun () ->
          Pp.strbrk "The native-compiler option is deprecated. To compile native \
          files ahead of time, use the coqnative binary instead.")

let interp_set_option (type a) opt (v:string) (k:a Goptions.option_kind) : a =
  let opt = String.concat " " opt in
  match k with
  | BoolKind -> (Coqargs.get_bool ~opt v)
  | IntKind -> (Coqargs.get_int_opt ~opt v)
  | StringKind -> v
  | StringOptKind -> Some v

let interp_set_option opt =
  { Goptions.check_and_cast = (fun v k -> interp_set_option opt v k ) }

let set_option (opt,v) =
  let open Goptions in
  match (v:Coqargs.option_command) with
  | OptionUnset -> unset_option_value_gen ~locality:OptLocal opt
  | OptionSet None -> set_bool_option_value_gen ~locality:OptLocal opt true
  | OptionSet (Some v) -> set_option_value ~locality:OptLocal (interp_set_option opt) opt v

let handle_injection ~intern = let open Coqargs in function
  | RequireInjection {lib;prefix;export;allow_failure} ->
    require_file ~intern ~lib ~prefix ~export ~allow_failure
  | OptionInjection o -> set_option o
  | WarnNoNative s -> warn_no_native_compiler s
  | WarnNativeDeprecated -> warn_deprecated_native_compiler ()

let start_library ~intern ~top injections =
  Flags.verbosely Declaremods.start_library top;
  CWarnings.override_unknown_warning[@ocaml.warning "-3"] := true;
  List.iter (handle_injection ~intern) injections;
  CWarnings.override_unknown_warning[@ocaml.warning "-3"] := false
