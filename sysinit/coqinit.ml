(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

(** Coq is a heavy user of persistent data structures and symbolic ASTs, so the
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
  CProfile.init_profile ();
  init_gc ();
  Sys.catch_break false (* Ctrl-C is fatal during the initialisation *)

let init_coqlib opts = match opts.Coqargs.config.Coqargs.coqlib with
  | None -> ()
  | Some s ->
    Boot.Env.set_coqlib s

let print_query opts = let open Coqargs in function
  | PrintVersion -> Boot.Usage.version ()
  | PrintMachineReadableVersion -> Boot.Usage.machine_readable_version ()
  | PrintWhere ->
    let env = Boot.Env.init () in
    let coqlib = Boot.Env.coqlib env |> Boot.Path.to_string in
    print_endline coqlib
  | PrintHelp h -> Boot.Usage.print_usage stderr h
  | PrintConfig ->
    let () = init_coqlib opts in
    Envars.print_config stdout

let parse_arguments ~parse_extra ~usage ?(initial_args=Coqargs.default) () =
  let opts, extras =
    Coqargs.parse_args ~usage ~init:initial_args
      (List.tl (Array.to_list Sys.argv)) in
  let customopts, extras = parse_extra extras in
  if not (CList.is_empty extras) then begin
    prerr_endline ("Don't know what to do with "^String.concat " " extras);
    prerr_endline "See -help for the list of supported options";
    exit 1
    end;
  match opts.Coqargs.main with
  | Coqargs.Queries q -> List.iter (print_query opts) q; exit 0
  | Coqargs.Run -> opts, customopts

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
  with _ -> ()

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
  List.iter Loadpath.add_vo_path opts.pre.vo_includes;
  let env_ocamlpath =
    try [Sys.getenv "OCAMLPATH"]
    with Not_found -> []
  in
  let env_ocamlpath = ml_path @ env_ocamlpath in
  let ocamlpathsep = if Sys.unix then ":" else ";" in
  let env_ocamlpath = String.concat ocamlpathsep env_ocamlpath in
  Findlib.init ~env_ocamlpath ()

let init_runtime opts =
  let open Coqargs in
  Lib.init ();
  init_coqlib opts;
  if opts.post.memory_stat then at_exit print_memory_stat;
  Mltop.init_known_plugins ();

  (* Configuration *)
  Global.set_impredicative_set opts.config.logic.impredicative_set;
  Global.set_indices_matter opts.config.logic.indices_matter;
  Global.set_check_universes (not opts.config.logic.type_in_type);
  Global.set_VM opts.config.enable_VM;
  Flags.set_native_compiler (match opts.config.native_compiler with NativeOff -> false | NativeOn _ -> true);
  Global.set_native_compiler (match opts.config.native_compiler with NativeOff -> false | NativeOn _ -> true);

  (* Native output dir *)
  Nativelib.output_dir := opts.config.native_output_dir;
  Nativelib.include_dirs := opts.config.native_include_dirs;

  (* Paths for loading stuff *)
  init_load_paths opts;

  injection_commands opts

let require_file (dir, from, exp) =
  let mp = Libnames.qualid_of_string dir in
  let mfrom = Option.map Libnames.qualid_of_string from in
  let exp = Option.map (fun e -> e, None) exp in
  Flags.silently (Vernacentries.vernac_require mfrom exp) [mp,Vernacexpr.ImportAll]

let warn_no_native_compiler =
  CWarnings.create ~name:"native-compiler-disabled" ~category:"native-compiler"
    Pp.(fun s -> strbrk "Native compiler is disabled," ++
                   strbrk " -native-compiler " ++ strbrk s ++
                   strbrk " option ignored.")

let warn_deprecated_native_compiler =
  CWarnings.create ~name:"deprecated-native-compiler-option" ~category:"deprecated"
         (fun () ->
          Pp.strbrk "The native-compiler option is deprecated. To compile native \
          files ahead of time, use the coqnative binary instead.")

let handle_injection = let open Coqargs in function
  | RequireInjection r -> require_file r
  | OptionInjection o -> set_option o
  | WarnNoNative s -> warn_no_native_compiler s
  | WarnNativeDeprecated -> warn_deprecated_native_compiler ()

let start_library ~top injections =
  Flags.verbosely Declaremods.start_library top;
  List.iter handle_injection injections
