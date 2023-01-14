(************************************************************************)
(* This file is licensed under The MIT License                          *)
(* See LICENSE for more information                                     *)
(************************************************************************)

let coqdep_files ~dir files ~cctx () =
  let files = List.map (Filename.concat dir) files in
  let open Coqdeplib in
  let args = List.concat [cctx; files] |> Args.parse (Args.make ())  in
  let make_separator_hack = false in
  let state = Common.init ~make_separator_hack args in
  List.iter Common.treat_file_command_line files;
  let deps = Common.compute_deps state in
  deps

let strip_quotes str =
  if not (String.contains str ' ') && Str.string_match (Str.regexp "\"\\(.*\\)\"") str 0
  then
    Str.matched_group 1 str
  else
    str

let vfile_header ~dir ?(name="coq-prog-args") vfile =
  let sf = Printf.sprintf in
  let vfile = Filename.concat dir vfile in
  let inc = open_in vfile in
  let line =
    try input_line inc
    with End_of_file -> Format.eprintf "error parsing header: %s@\n%!" vfile; ""
  in
  close_in inc;
  let explode s = List.init (String.length s) (String.get s) in
  let split s =
    let rec split_space acc word = function
      | [] -> List.rev (List.rev word :: acc)
      | ' ' :: xs -> split_space (List.rev word :: acc) [] xs
      | '"' :: xs -> find_quote acc ('"' :: word) xs
      | x :: xs -> split_space acc (x :: word) xs
    and find_quote acc word = function
      | [] -> List.rev (List.rev word :: acc)
      | '"' :: xs -> split_space acc ('"' :: word) xs
      | x :: xs -> find_quote acc (x :: word) xs
    in
    split_space [] [] s
  in
  if Str.string_match (Str.regexp (sf ".*%s: (\\([^)]*\\)).*" name)) line 0 then
    (* These arguments are surrounded by quotes so we need to unquote them *)
    Str.matched_group 1 line
    (* Turn into a list of chars *)
    |> explode
    (* Split via spaces but not between quotes *)
    |> split
    (* Map list of list of chars to list of strings *)
    |> List.map (fun x -> String.of_seq (List.to_seq x))

    |> List.map strip_quotes
  else []

exception UnsupportedCoqCompat of string

let rec extra_deps s =
  let compat_file version = match version with
    | "8.11" -> "../theories/Compat/Coq811.vo"
    | "8.12" -> "../theories/Compat/Coq812.vo"
    | "8.13" -> "../theories/Compat/Coq813.vo"
    | "8.14" -> "../theories/Compat/Coq814.vo"
    | "8.15" -> "../theories/Compat/Coq815.vo"
    | "8.16" -> "../theories/Compat/Coq816.vo"
    | "8.17" -> "../theories/Compat/Coq817.vo"
    | "8.18" -> "../theories/Compat/Coq818.vo"
    | v -> raise (UnsupportedCoqCompat v)
  in
  match s with
  | "-compat" :: version :: s -> [compat_file version] @ extra_deps s
  | _ :: s -> extra_deps s
  | [] -> []

let rec coqchk_filter = function
  (* Arguments that coqchk understands *)
  | "-R" :: dir :: name :: l -> "-R" :: dir :: name :: coqchk_filter l
  | "-Q" :: dir :: name :: l -> "-Q" :: dir :: name :: coqchk_filter l
  | "-impredicative-set" :: l -> "-impredicative-set" :: coqchk_filter l
  | "-indices-matter" :: l -> "-indices-matter" :: coqchk_filter l
  | "-boot" :: l -> "-boot" :: coqchk_filter l
  | _ :: l -> coqchk_filter l
  | [] -> []

let rec coqdep_filter = function
  (* Arguments that coqdep understands *)
  | "-R" :: dir :: name :: l -> "-R" :: dir :: name :: coqdep_filter l
  | "-Q" :: dir :: name :: l -> "-Q" :: dir :: name :: coqdep_filter l
  | "-I" :: dir :: l -> "-I" :: dir :: coqdep_filter l
  | "-boot" :: l -> "-boot" :: coqdep_filter l
  | _ :: l -> coqdep_filter l
  | [] -> []

module Compilation = struct
  module Output = struct
    (* The type of output - dictates which logs we will diff *)
    type t =
    | None
    | MainJob
    | MainJobWithExit
    | MainJobModTime

    let to_string = function
      | None -> "None"
      | MainJob -> "MainJob"
      | MainJobWithExit -> "MainJobWithExit"
      | MainJobModTime -> "MainJob"
  end

  module Kind = struct
    type t =
    | Vo
    | Vos
    | Vok
    | Vio
    | Vio2vo
    | Coqtop
    | Coqchk
    | Native

    let to_string = function
      | Vo -> "vo"
      | Vos -> "vos"
      | Vok -> "vok"
      | Vio -> "vio"
      | Vio2vo -> "vio2vo"
      | Coqtop -> "coqtop"
      | Coqchk -> "coqchk"
      | Native -> "native"
  end
end

(** alias rule used for running single tests *)
let alias_vfile_test ~out ~targets ~alias_kind vfile =
  let filename = Filename.chop_extension vfile in
  let name = match alias_kind with
    | `Alias_normal -> filename
    | `Alias_vo -> filename ^ ".vo"
    | `Alias_vok -> filename ^ ".vok"
    | `Alias_vos -> filename ^ ".vos"
    | `Alias_vio -> filename ^ ".vio"
    | `Alias_coqchk -> filename ^ ".coqchk"
    | `Alias_native -> filename ^ ".native"
  in
  Dune.Alias.pp out Dune.Alias.{name; deps = targets}

let extra_alias_for_test ~out ~run ~extension ~wrapper vfile =
  let alias = Some (Filename.chop_extension vfile ^ extension) in
  let hash = String.concat " " run |> Digest.string |> Digest.to_hex in
  let vfile_replay = Filename.chop_extension vfile ^ wrapper ^ hash ^ Filename.extension vfile in
  let run = List.rev run |> List.tl |> List.rev |> fun x -> x @ [vfile_replay] in
  let () = Dune.Rules.copy ~out ?alias vfile vfile_replay in
  run, alias

let replay_vfile_test ~out ?envs ~run ?exit_codes vfile =
  let run, alias = extra_alias_for_test ~out ~run ~extension:".replay" ~wrapper:"__replay_" vfile in
  Dune.Rules.run ~out ?envs ~run ?exit_codes ~alias ()

let debug_vfile_test ~out ?envs ~deps ~run vfile =
  let run, alias = extra_alias_for_test ~out ~run ~extension:".debug" ~wrapper:"__debug_" vfile in
  let envs = match envs with
    | None -> ["OCAMLRUNPARAM", "b"]
    | Some envs -> (("OCAMLRUNPARAM", "b") :: envs)
  in
  Dune.Rules.run ~out ~envs ~deps ~run ~alias ()

(** coqc rule no vo target, log *)
let coqc_log_rule ~out ~envs ~exit_codes ~args ~deps ?(log_ext=".log") vfile : unit=
  let run = "%{bin:coqc}" :: args @ [vfile]  in
  let log_file = vfile ^ log_ext in
  let targets = [log_file] in
  Dune.Rules.run ~out ~envs ~run ~exit_codes ~deps ~targets ~log_file ();
  Dune.Alias.pp out Dune.Alias.{name = "vo"; deps = targets};
  alias_vfile_test ~out ~targets ~alias_kind:`Alias_normal vfile;
  alias_vfile_test ~out ~targets ~alias_kind:`Alias_vo vfile;
  replay_vfile_test ~out ~envs ~run ~exit_codes vfile;
  debug_vfile_test ~out ~envs ~deps ~run vfile

(** coqc rule no vo target, log with exit code *)
let coqc_log_rule_with_exit ~out ~envs ~exit_codes ~args ~deps ?(log_ext=".log") vfile : unit =
  let with_exit = "%{project_root}/test-suite/tools/with-exit.sh" in
  let run = with_exit :: "%{bin:coqc}" :: args @ [vfile]  in
  let log_file = vfile ^ log_ext in
  let targets = [log_file] in
  Dune.Rules.run ~out ~envs ~run ~exit_codes ~deps ~targets ~log_file ();
  Dune.Alias.pp out Dune.Alias.{name = "vo"; deps = targets};
  alias_vfile_test ~out ~targets ~alias_kind:`Alias_normal vfile;
  alias_vfile_test ~out ~targets ~alias_kind:`Alias_vo vfile;
  replay_vfile_test ~out ~envs ~run ~exit_codes vfile;
  debug_vfile_test ~out ~envs ~deps ~run vfile

(** coqc rule vo and log targets *)
let coqc_vo_log_rule ~out ~envs ~exit_codes ~args ~deps ?(log_ext=".log") vfile : unit =
  let filename = Filename.chop_extension vfile in
  let vofile = filename ^ ".vo" in
  let log_file = vfile ^ log_ext in
  let globfile = filename ^ ".glob" in
  let run = "%{bin:coqc}" :: args @ [vfile] in
  let targets = [vofile; globfile; log_file] in
  Dune.Rules.run ~out ~envs ~run ~exit_codes ~deps ~targets ~log_file ();
  Dune.Alias.pp out Dune.Alias.{name = "vo"; deps = targets};
  alias_vfile_test ~out ~targets ~alias_kind:`Alias_normal vfile;
  alias_vfile_test ~out ~targets ~alias_kind:`Alias_vo vfile;
  replay_vfile_test ~out ~envs ~run ~exit_codes vfile;
  debug_vfile_test ~out ~envs ~deps ~run vfile

(* TODO: works but vos needed for stdlib *)
let coqc_vos_log_rule ~out ~envs ~exit_codes ~args ~deps ?(log_ext="os.log") vfile : unit =
  let vosify deps = deps
    |> List.filter_map (Filename.chop_suffix_opt ~suffix:".vo")
    |> List.map (fun x -> x ^ ".vos")
  in
  let deps = deps @ vosify deps in
  let log_file = vfile ^ log_ext in
  let vos_file = vfile ^ "os" in
  let targets = [vos_file; log_file] in
  let run = "%{bin:coqc}" :: args @ ["-vos"; vfile] in
  Dune.Rules.run ~out ~envs ~run ~exit_codes ~deps ~targets ~log_file ();
  Dune.Alias.pp out Dune.Alias.{name = "vos"; deps = targets};
  alias_vfile_test ~out ~targets ~alias_kind:`Alias_normal vfile;
  alias_vfile_test ~out ~targets ~alias_kind:`Alias_vos vfile;
  replay_vfile_test ~out ~envs ~run ~exit_codes vfile;
  debug_vfile_test ~out ~envs ~deps ~run vfile

(* TODO: works but vos needed for stdlib *)
let coqc_vok_log_rule ~out ~envs ~exit_codes ~args ~deps ?(log_ext="ok.log") vfile : unit =
  let vosify deps = deps
    |> List.filter_map (Filename.chop_suffix_opt ~suffix:".vo")
    |> List.map (fun x -> x ^ ".vos")
  in
  let deps = vosify deps in
  let log_file = vfile ^ log_ext in
  let vok_file = vfile ^ "ok" in
  let targets = [vok_file; log_file] in
  let run = "%{bin:coqc}" :: args @ ["-vok"; vfile] in
  Dune.Rules.run ~out ~envs ~run ~exit_codes ~deps ~targets ~log_file ();
  Dune.Alias.pp out Dune.Alias.{name = "vok"; deps = targets};
  alias_vfile_test ~out ~targets ~alias_kind:`Alias_normal vfile;
  alias_vfile_test ~out ~targets ~alias_kind:`Alias_vok vfile;
  replay_vfile_test ~out ~envs ~run ~exit_codes vfile;
  debug_vfile_test ~out ~envs ~deps ~run vfile

let coqchk_log_rule ~out ~envs ~exit_codes ~chk_args ~deps ?(log_ext=".chk.log") vfile : unit =
  let vofile = vfile ^ "o" in
  let log_file = vfile ^ log_ext in
  let targets = [log_file] in
  let deps = vofile :: deps in
  let run = ["%{bin:coqchk}"; "-silent"; "-o"] @ chk_args @ ["-norec"; vofile] in
  Dune.Rules.run ~out ~envs ~run ~exit_codes ~deps ~targets ~log_file ();
  Dune.Alias.pp out Dune.Alias.{name = "chk"; deps = targets};
  alias_vfile_test ~out ~targets ~alias_kind:`Alias_normal vfile;
  alias_vfile_test ~out ~targets ~alias_kind:`Alias_coqchk vofile;
  replay_vfile_test ~out ~envs ~run ~exit_codes vofile;
  debug_vfile_test ~out ~envs ~deps ~run vofile

(* TODO: coqnative works but cmxs needed for stdlib *)
let coqnative_log_rule ~out ~envs ~exit_codes ~args ~deps ?(log_ext=".cmxs.log") vfile : unit =
  (* We need to also require .cmxs files for each .vo file *)
  let cmxsify deps = deps
    |> List.filter_map (Filename.chop_suffix_opt ~suffix:".vo")
    |> List.map (fun x -> x ^ ".cmxs")
  in
  let vofile = vfile ^ "o" in
  let cmxsfile = Filename.chop_extension vfile ^ ".cmxs" in
  let log_file = vfile ^ log_ext in
  let targets = [cmxsfile; log_file] in
  let deps = vofile :: deps @ cmxsify deps in
  let run = "%{bin:coqnative}" :: args @ [vofile] in
  Dune.Rules.run ~out ~envs ~run ~exit_codes ~deps ~targets ~log_file ();
  Dune.Alias.pp out Dune.Alias.{name = "native"; deps = targets};
  alias_vfile_test ~out ~targets ~alias_kind:`Alias_normal vfile;
  alias_vfile_test ~out ~targets ~alias_kind:`Alias_native vfile;
  replay_vfile_test ~out ~envs ~run ~exit_codes vfile;
  debug_vfile_test ~out ~envs ~deps ~run vfile

let coqc_vio_log_rule ~out ~envs ~exit_codes ~args ~deps ?(log_ext="io.log") vfile : unit =
  let vio_file = vfile ^ "io" in
  let log_file = vfile ^ log_ext in
  let targets = [vio_file; log_file] in
  let run = "%{bin:coqc}" :: args @ ["-vio"; vfile] in
  Dune.Rules.run ~out ~envs ~run ~exit_codes ~deps ~targets ~log_file ();
  Dune.Alias.pp out Dune.Alias.{name = "vio"; deps = targets};
  alias_vfile_test ~out ~targets ~alias_kind:`Alias_normal vfile;
  alias_vfile_test ~out ~targets ~alias_kind:`Alias_vio vfile;
  replay_vfile_test ~out ~envs ~run ~exit_codes vfile;
  debug_vfile_test ~out ~envs ~deps ~run vfile

let coqc_vio2vo_log_rule ~out ~envs ~exit_codes ~args ~deps ?(log_ext="io2vo.log") vfile : unit =
  let vofile = vfile ^ "o" in
  let log_file = vfile ^ log_ext in
  let viofile = vfile ^ "io" in
  let targets = [vofile; log_file] in
  let deps = viofile :: deps in
  let run = "%{bin:coqc}" :: args @ ["-vio2vo"; viofile] in
  Dune.Rules.run ~out ~envs ~run ~exit_codes ~deps ~targets ~log_file ();
  Dune.Alias.pp out Dune.Alias.{name = "vo"; deps = targets};
  alias_vfile_test ~out ~targets ~alias_kind:`Alias_normal vfile;
  alias_vfile_test ~out ~targets ~alias_kind:`Alias_vo vfile;
  replay_vfile_test ~out ~envs ~run ~exit_codes vfile;
  debug_vfile_test ~out ~envs ~deps ~run vfile

let coqtop_log_rule ~out ~envs ~exit_codes ~args ~deps ?(log_ext=".log") vfile : unit =
  let log_file = vfile ^ log_ext in
  let targets = [log_file] in
  let run = "%{bin:coqtop}" :: args in
  Dune.Rules.run ~out ~envs ~run ~exit_codes ~deps ~targets ~log_file ~in_file:vfile ();
  Dune.Alias.pp out Dune.Alias.{name = "coqtop"; deps = targets};
  alias_vfile_test ~out ~targets ~alias_kind:`Alias_normal vfile;
  replay_vfile_test ~out ~envs ~run ~exit_codes vfile;
  debug_vfile_test ~out ~envs ~deps ~run vfile

(* Preprocessing for output log *)
let log_preprocess_rule ~out ?(ext=".log") ~script vfile : unit =
  let log_file = vfile ^ ext in
  let log_pre_file = vfile ^ ext ^ ".pre" in
  let targets = [log_file] in
  let deps = [log_pre_file] in
  let run = [script; log_pre_file] in
  Dune.Rules.run ~out ~run ~deps ~targets ~log_file ~in_file:vfile ()

let diff_rule ~out ?(out_ext=".out") ?(log_ext=".log") vfile =
  let log = Filename.remove_extension vfile ^ out_ext in
  Dune.Rules.diff ~out log (vfile ^ log_ext);
  (* If we could provide multiple aliases to the diff rule, we wouldn't need two *)
  Dune.Rules.diff ~out log (vfile ^ log_ext)
    ~alias:(Some (Filename.chop_extension vfile))

(* Rule for copying csdp cache *)
let csdp_cache_rule ~out ~lvl ?copy_csdp_cache () =
  match copy_csdp_cache with
  | None -> ()
  | Some copy_csdp_cache ->
    let copy_csdp_cache = Filename.concat lvl copy_csdp_cache in
    (* Add rule for copying .csdp.cache *)
    let action =
      let open Dune.Action in
      Progn [
        No_infer (Copy (copy_csdp_cache, ".csdp.cache"));
        Run ["chmod"; "+w"; ".csdp.cache"];
      ]
    in
    let rule = Dune.Rule.{
      targets = [];
      deps = ["(universe)"; copy_csdp_cache];
      action ;
      alias = Some "csdp-cache";
    } in
    Dune.Rule.pp out rule

let error_unsupported_build_rule ~vfile (success, output, kind) () =
  let open Compilation in
  Printf.eprintf
    "*** Error generating rule for %s\n\
     Combination of arguments:\n\
      + success = %b\n\
      + output = %s\n\
      + kind = %s\n\
     Has chosen a build rule that is not supported.\n"
    vfile success (Output.to_string output) (Kind.to_string kind);
  exit 1

let generate_build_rule ~out ~envs ~exit_codes ~args ~deps ~chk_args ~success ~output ~kind vfile =
  let open Compilation in
  (* Override normal vo kind depending on args *)
  let kind =
    match kind with
    | Kind.Vo ->
      if List.mem "-vio2vo" args then Kind.Vio2vo
      else if List.mem "-vio" args then Kind.Vio
      else if List.mem "-vos" args then Kind.Vos
      else if List.mem "-vok" args then Kind.Vok
      else Kind.Vo
    | kind -> kind
  in
  match success, output, kind with
  (* vio *)
  | true, Output.None, Kind.Vio ->
    coqc_vio_log_rule ~out ~envs ~exit_codes ~args ~deps vfile
  | true, Output.MainJob, Kind.Vio ->
    coqc_vio_log_rule ~out ~envs ~exit_codes ~args ~deps ~log_ext:".log.pre" vfile;
    log_preprocess_rule ~out ~script:"../tools/amend-output-log.sh" vfile;
    diff_rule ~out vfile;
    ()
  (* vio2vo *)
  | true, Output.None, Kind.Vio2vo ->
    coqc_vio2vo_log_rule ~out ~envs ~exit_codes ~args ~deps vfile;
    ()
  (* vos *)
  | true, Output.None, Kind.Vos ->
    coqc_vos_log_rule ~out ~envs ~exit_codes ~args ~deps vfile
  | true, Output.MainJob, Kind.Vos ->
    coqc_vos_log_rule ~out ~envs ~exit_codes ~args ~deps ~log_ext:".log.pre" vfile;
    log_preprocess_rule ~out ~script:"../tools/amend-output-log.sh" vfile;
    diff_rule ~out vfile;
    ()
  (* vok *)
  | true, Output.None, Kind.Vok ->
    coqc_vok_log_rule ~out ~envs ~exit_codes ~args ~deps vfile
  (* vo *)
  | true, Output.None, Kind.Vo ->
    coqc_vo_log_rule ~out ~envs ~exit_codes ~args ~deps vfile;
    ()
  (* failing vo *)
  | false, Output.None, Kind.Vo ->
    coqc_log_rule ~out ~envs ~exit_codes ~args ~deps vfile
  (* output rule *)
  | true, Output.MainJob, Kind.Vo ->
    coqc_vo_log_rule ~out ~envs ~exit_codes ~args ~deps ~log_ext:".log.pre" vfile;
    log_preprocess_rule ~out ~script:"../tools/amend-output-log.sh" vfile;
    diff_rule ~out vfile;
    ()
  (* output rule with exit code *)
  | false, Output.MainJobWithExit, Kind.Vo ->
    coqc_log_rule_with_exit ~out ~envs ~exit_codes ~args ~deps ~log_ext:".log.pre" vfile;
    log_preprocess_rule ~out ~script:"../tools/amend-output-log.sh" vfile;
    diff_rule ~out vfile;
    ()
  (* coqc output rule modulo time *)
  | true, Output.MainJobModTime, Kind.Vo ->
    coqc_vo_log_rule ~out ~envs ~exit_codes ~args ~deps ~log_ext:".log.pre" vfile;
    log_preprocess_rule ~out ~script:"../tools/modulo-time-output-log.sh" vfile;
    diff_rule ~out vfile;
    ()
  (* failing output rule *)
  | false, Output.MainJob, Kind.Vo ->
    coqc_log_rule ~out ~envs ~exit_codes ~args ~deps ~log_ext:".log.pre" vfile;
    log_preprocess_rule ~out ~script:"../tools/amend-output-log.sh" vfile;
    diff_rule ~out vfile;
    ()
  (* coqtop rule *)
  | true, Output.None, Kind.Coqtop ->
    coqtop_log_rule ~out ~envs ~exit_codes ~args ~deps vfile;
    ()
  (* coqtop output rule *)
  | true, Output.MainJob, Kind.Coqtop ->
    coqtop_log_rule ~out ~envs ~exit_codes ~args ~deps ~log_ext:".log.pre" vfile;
    log_preprocess_rule ~out ~script:"../tools/coqtop-output-log.sh" vfile;
    diff_rule ~out vfile;
    ()
  (* vok ouptput rule *)
  | true, Output.MainJob, Kind.Vok ->
    coqc_vok_log_rule ~out ~envs ~exit_codes ~args ~deps ~log_ext:".log.pre" vfile;
    log_preprocess_rule ~out ~script:"../tools/amend-output-log.sh" vfile;
    diff_rule ~out vfile;
    ()
  (* coqchk rule *)
  | true, Output.None, Kind.Coqchk ->
    coqchk_log_rule ~out ~envs ~exit_codes ~chk_args ~deps vfile;
    ()
  (* checking output of coqchk *)
  | true, Output.MainJob, Kind.Coqchk ->
    coqchk_log_rule ~out ~envs ~exit_codes ~chk_args ~deps ~log_ext:".chk.log.pre" vfile;
    log_preprocess_rule ~out ~script:"../tools/amend-output-log.sh" ~ext:".chk.log" vfile;
    diff_rule ~out ~log_ext:".chk.log" vfile;
    ()
  (* coqnative *)
  | true, Output.None, Kind.Native ->
    coqnative_log_rule ~out ~envs ~exit_codes ~args ~deps vfile;
    ()
  (* coqnative output rule *)
  | true, Output.MainJob, Kind.Native ->
    coqnative_log_rule ~out ~envs ~exit_codes ~args ~deps ~log_ext:".log.pre" vfile;
    log_preprocess_rule ~out ~script:"../tools/amend-output-log.sh" vfile;
    diff_rule ~out vfile;
    ()
  (* If we don't support the build rule, we exit with an error *)
  | arguments -> error_unsupported_build_rule ~vfile arguments ()

let generate_rule ~out ~cctx ~dir ~lvl ~args ~base_deps ~deps ~envs ~exit_codes ~output ~kind
  vfile_dep_info =
  let open Coqdeplib in
  let open Dep_info in
  let vfile_long = vfile_dep_info.Dep_info.name ^ ".v" in
  let vfile =
    let regex = Str.regexp (Str.quote @@ dir ^ "/") in
    Str.global_replace regex "" vfile_long
  in
  (* Adjust paths to META *)
  let vfile_deps =
    let f =
      function
      | Dep.Other s ->
        (* Printf.printf "vfile: %s META: %s\n" vfile s; *)
        Dep.Other (Str.replace_first (Str.regexp ".*/lib/coq-core") "../../install/default/lib/coq-core" s)
      | d -> d
    in
    List.map f vfile_dep_info.deps
  in
  (* Dependencies are the .vo files given by coqdep and the original .v file *)
  let vfile_deps = vfile_long :: List.filter_map (
    function
    | Dep.Require s -> Some (s ^ ".vo")
    | _ -> None) vfile_deps in
  (* parse the header of the .v file for extra arguments *)
  let args = vfile_header ~dir vfile @ args in
  (* lvl adjustment done here *)
  let deps =
    deps lvl @ (base_deps @ extra_deps args @ vfile_deps
    |> List.map (fun x -> lvl ^ "/" ^ x))
  in
  let args = cctx @ args in
  let chk_args = coqchk_filter args in
  let success =
    match exit_codes with
    | [] -> true
    | l -> List.exists (fun x -> 0 = x) l
  in
  generate_build_rule ~out ~envs ~exit_codes ~args ~chk_args ~deps ~success
    ~output ~kind vfile

let check_dir ~out ~cctx ?(ignore=[]) ?copy_csdp_cache
  ?(args=[]) ?(base_deps=[]) ?(deps=(fun _ -> [])) ?(envs=[]) ?(exit_codes=[])
  ?(output=Compilation.Output.None) ?(kind=Compilation.Kind.Vo) ~dir () =
  (* Scan for all .v files in directory ignoring as necessary *)
  let vfiles = Dir.scan_files_by_ext ~ext:".v" ~ignore dir in
  (* Run coqdep to get deps *)
  let coq_deps = coqdep_files ~cctx:(coqdep_filter @@ cctx ".") ~dir vfiles () in
  (* The lvl can be computed from the dir *)
  let lvl = Dir.back_to_root dir in
  (* If the csdp cache copy is set then we add the special alias as a dep *)
  let deps = match copy_csdp_cache with None -> deps | Some _ ->
    (fun lvl -> "(alias csdp-cache)" :: deps lvl) in
  Dune.Rules.in_subdir out dir
    ~f:(fun out () ->
      List.iter (generate_rule ~cctx:(cctx lvl) ~lvl ~args ~base_deps ~deps
        ~output ~kind ~envs ~exit_codes ~out ~dir) coq_deps;
      csdp_cache_rule ~out ~lvl ?copy_csdp_cache ()
    )
