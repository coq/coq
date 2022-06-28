open! Coq_dune

(* Coqnative overhead is more than 33% in build time :( :( *)

(* in a 16-core system:

- coqnative:

real	2m29,860s
user	19m44,997s
sys	2m19,618s

real	2m30,940s
user	20m6,945s
sys	2m22,057s

- coqc -native-compiler on

real	2m30,567s
user	14m17,062s
sys	1m47,661s

real	2m29,008s
user	14m15,293s
sys	1m48,194s

 *)

(* let native_mode = Coq_module.Rule_type.CoqNative *)
let native_mode = Coq_module.Rule_type.Coqc

let native = match Coq_config.native_compiler with
  | Coq_config.NativeOff -> Coq_module.Rule_type.Disabled
  | Coq_config.NativeOn _ -> native_mode

(** arguments are [gen_rules theory_name dir flags] *)
let parse_args () =
  let tname = String.split_on_char '.' Sys.argv.(1) in
  let base_dir = Sys.argv.(2) in
  let _backtrace = [Arg.A "-d"; Arg.A "backtrace"] in
  let default = false, false, Coq_module.Rule_type.Regular { native }, [] in
  let split, async, rule, user_flags = if Array.length Sys.argv > 3 then
      match Sys.argv.(3) with
      | "-vio" -> false, false, Coq_module.Rule_type.Quick, Arg.[A "-vio"]
      | "-async" -> false, true, Coq_module.Rule_type.Regular { native }, Arg.[A "-async-proofs"; A "on"]
      | "-split" -> true, false, Coq_module.Rule_type.Regular { native }, []
      (* Dune will sometimes pass this option as "" *)
      | "" -> default
      | opt -> raise (Invalid_argument ("unrecognized option: " ^ opt))
    else
      default
  in
  tname, base_dir, async, rule, user_flags, split

let ppr fmt = List.iter (Dune_file.Rule.pp fmt)
let ppi fmt = List.iter (Dune_file.Install.pp fmt)

let main () =

  let tname, base_dir, async, rule, user_flags, split = parse_args () in
  let root_lvl = List.length (String.split_on_char '/' base_dir) in

  let boot = if tname = ["Coq"]
    then Coq_rules.Boot_type.Stdlib
    else Coq_rules.Boot_type.Regular (Some (Path.(adjust ~lvl:root_lvl (make "theories"))))
  in

  (* Rule generation *)
  Unix.chdir base_dir;
  let dir_info = Dir_info.scan ~prefix:[] "." in
  let package = base_dir in
  let cctx = Coq_rules.Context.make ~root_lvl ~tname ~user_flags ~rule ~boot ~dir_info ~async ~package ~split in
  let vo_rules = Coq_rules.vo_rules ~dir_info ~cctx in
  let install_rules = Coq_rules.install_rules ~dir_info ~cctx in

  (* Rule printing *)
  let fmt = Format.std_formatter in

  List.iter (Dune_file.Subdir.pp ppr fmt) vo_rules;
  List.iter (Dune_file.Subdir.pp ppi fmt) install_rules;

  (* Rules for vio2vo *)
  begin
    match rule with
    | Coq_module.Rule_type.Quick ->
      let vio2vo_rules = Coq_rules.vio2vo_rules ~dir_info ~cctx in
      List.iter (Dune_file.Subdir.pp ppr fmt) vio2vo_rules
    | Coq_module.Rule_type.Regular _ -> ()
  end;

  (* Rules for coqnative (not always setup for now, need to think about this) *)
  begin
    match native_mode with
    (* cmxs files are already generated in coqc *)
    | Coq_module.Rule_type.Disabled
    | Coq_module.Rule_type.Coqc -> ()
    | Coq_module.Rule_type.CoqNative ->
      let coqnative_rules = Coq_rules.coqnative_rules ~dir_info ~cctx in
      List.iter (Dune_file.Subdir.pp ppr fmt) coqnative_rules
  end;

  Format.pp_print_flush fmt ();
  ()

let () =
  Printexc.record_backtrace true;
  try main ()
  with exn ->
    let bt = Printexc.get_backtrace () in
    let exn = Printexc.to_string exn in
    Format.eprintf "[gen_rules] Fatal error: %s@\n%s@\n%!" exn bt;
    exit 1
