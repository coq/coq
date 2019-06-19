(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let set_noninteractive_mode () =
  Flags.quiet := true;
  System.trust_file_cache := true

let outputstate opts =
  Option.iter (fun ostate_file ->
    let fname = CUnix.make_suffix ostate_file ".coq" in
    States.extern_state fname) opts.Coqcargs.outputstate

let coqc_main () =
  (* Careful because init_toplevel will call Summary.init_summaries,
     thus options such as `quiet` have to be set after the main
     initialisation is run. *)
  let coqc_init ~opts args =
    set_noninteractive_mode ();
    let opts, args = Coqtop.(coqtop_toplevel.init) ~opts args in
    opts, args
  in
  let opts, extras =
    Topfmt.(in_phase ~phase:Initialization)
      Coqtop.(init_toplevel ~help:Usage.print_usage_coqc ~init:Coqargs.default coqc_init) List.(tl (Array.to_list Sys.argv)) in

  let copts = Coqcargs.parse extras in

  if not opts.Coqargs.glob_opt then Dumpglob.dump_to_dotglob ();

  Topfmt.(in_phase ~phase:CompilationPhase)
    Ccompile.compile_files opts copts;

  (* Careful this will modify the load-path and state so after this
     point some stuff may not be safe anymore. *)
  Topfmt.(in_phase ~phase:CompilationPhase)
    Ccompile.do_vio opts copts;

  (* Allow the user to output an arbitrary state *)
  outputstate copts;

  flush_all();

  if opts.Coqargs.output_context then begin
    let sigma, env = let e = Global.env () in Evd.from_env e, e in
    Feedback.msg_notice Pp.(Flags.(with_option raw_print (Prettyp.print_full_pure_context env) sigma) ++ fnl ())
  end;
  CProfile.print_profile ()

let main () =
  let _feeder = Feedback.add_feeder Coqloop.coqloop_feed in
  try
    coqc_main ();
    exit 0
  with exn ->
    flush_all();
    Topfmt.print_err_exn exn;
    flush_all();
    let exit_code = if (CErrors.is_anomaly exn) then 129 else 1 in
    exit exit_code
