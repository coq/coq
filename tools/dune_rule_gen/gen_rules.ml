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
type args = {
  tname : string list;
  base_dir : string;
  async : bool;
  rule : Coq_module.Rule_type.t;
  split : bool;
  user_flags : Arg.t list;
  dependencies : string list;
}

let parse_args () : args =
  match Array.to_list Sys.argv with
  | _ :: tname :: base_dir :: args ->
    let tname = String.split_on_char '.' tname in
    let _backtrace = [Arg.A "-d"; Arg.A "backtrace"] in
    let default = { base_dir; tname; async = false; split = false; rule = Coq_module.Rule_type.Regular { native }; user_flags = []; dependencies = [] } in
    let rec parse a = function
      | [] -> a
      | "-async" :: rest -> parse { a with async = true; user_flags = Arg.[A "-async-proofs"; A "on"] } rest
      | "-split" :: rest -> parse { a with split = true } rest
      | "-dep" :: d :: rest -> parse { a with dependencies = d :: a.dependencies } rest
      (* Dune will sometimes pass this option as "" *)
      | "" :: rest -> parse a rest
      | unknown :: _ -> raise (Invalid_argument unknown)
    in
      parse default args
  | _ -> raise (Invalid_argument "usage: gen_rules theory_name directory")

let ppr fmt = List.iter (Dune_file.Rule.pp fmt)
let ppi fmt = List.iter (Dune_file.Install.pp fmt)

let main () =

  let { tname; base_dir; async; rule; user_flags; split; dependencies } = parse_args () in
  let root_lvl = List.length (String.split_on_char '/' base_dir) in

  let init =
    let directory = Path.make "theories" in
    Coq_rules.Theory.{ directory; dirname = ["Corelib"]; implicit = true; deps = [] }
  in

  (* usually the else case here is Ltac2, but other libraries could be
     handled as well *)
  let boot, implicit = if tname = ["Corelib"]
    then Coq_rules.Boot_type.Corelib, true
    else Coq_rules.Boot_type.Regular init, false
  in

  (* Rule generation *)
  let dir_info = Dir_info.scan ~prefix:[] base_dir in
  let directory = Path.make base_dir in
  let theory = Coq_rules.Theory.{ directory; dirname = tname; implicit; deps = dependencies } in
  let cctx = Coq_rules.Context.make ~root_lvl ~theory ~user_flags ~rule ~boot ~dir_info ~async ~split in
  let vo_rules = Coq_rules.vo_rules ~dir_info ~cctx in
  let install_rules = Coq_rules.install_rules ~dir_info ~cctx in

  (* Rule printing *)
  let fmt = Format.std_formatter in

  List.iter (Dune_file.Subdir.pp ppr fmt) vo_rules;
  List.iter (Dune_file.Subdir.pp ppi fmt) install_rules;

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

let pr_feedback (fb : Feedback.feedback) =
  match fb.contents with
  | Message (_,_,_,msg) -> Format.eprintf "%a" Pp.pp_with msg
  | _ -> () [@@warning "-4"]

let () =
  Printexc.record_backtrace true;
  let _ : int = Feedback.add_feeder pr_feedback in
  try main ()
  with exn ->
    Format.eprintf "[gen_rules] Fatal error:@ @[<2>%a@]@\n%!" Pp.pp_with (CErrors.print exn);
    exit 1
