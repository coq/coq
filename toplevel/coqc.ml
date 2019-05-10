(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let outputstate opts =
  Option.iter (fun ostate_file ->
    let fname = CUnix.make_suffix ostate_file ".coq" in
    States.extern_state fname) opts.Coqcargs.outputstate

let coqc_init _copts ~opts =
  Flags.quiet := true;
  System.trust_file_cache := true;
  Coqtop.init_color opts.Coqargs.config;
  if not opts.Coqargs.config.Coqargs.glob_opt then Dumpglob.dump_to_dotglob ()

let coqc_main copts ~opts =
  Topfmt.(in_phase ~phase:CompilationPhase)
    Ccompile.compile_files opts copts;

  (* Careful this will modify the load-path and state so after this
     point some stuff may not be safe anymore. *)
  Topfmt.(in_phase ~phase:CompilationPhase)
    Ccompile.do_vio opts copts;

  (* Allow the user to output an arbitrary state *)
  outputstate copts;

  flush_all();

  if opts.Coqargs.post.Coqargs.output_context then begin
    let sigma, env = let e = Global.env () in Evd.from_env e, e in
    Feedback.msg_notice Pp.(Flags.(with_option raw_print (Prettyp.print_full_pure_context env) sigma) ++ fnl ())
  end;
  CProfile.print_profile ()

let coqc_run copts ~opts () =
  let _feeder = Feedback.add_feeder Coqloop.coqloop_feed in
  try
    coqc_main ~opts copts;
    exit 0
  with exn ->
    flush_all();
    Topfmt.print_err_exn exn;
    flush_all();
    let exit_code = if (CErrors.is_anomaly exn) then 129 else 1 in
    exit exit_code

let custom_coqc = Coqtop.{
  parse_extra = (fun ~opts extras -> Coqcargs.parse extras, []);
  help = Usage.print_usage_coqc;
  init = coqc_init;
  run = coqc_run;
  opts = Coqargs.default;
}

let main () =
  Coqtop.start_coq custom_coqc
