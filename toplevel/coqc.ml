(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let coqc_init ((_,color_mode),_) injections ~opts =
  Flags.quiet := true;
  System.trust_file_cache := true;
  Coqtop.init_color (if opts.Coqargs.config.Coqargs.print_emacs then `EMACS else color_mode);
  DebugHook.Intf.(set
    { read_cmd = Coqtop.ltac_debug_parse
    ; submit_answer = Coqtop.ltac_debug_answer
    ; isTerminal = true
    });
  injections

let coqc_specific_usage = Boot.Usage.{
  executable_name = "coqc";
  extra_args = "file...";
  extra_options = "\n\
coqc specific options:\
\n  -o f.vo                use f.vo as the output file name\
\n  -verbose               compile and output the input file\
\n  -noglob                do not dump globalizations\
\n  -dump-glob f           dump globalizations in file f (to be used by coqdoc)\
\n  -schedule-vio2vo j f1..fn   run up to j instances of Coq to turn each fi.vio\
\n                         into fi.vo\
\n  -schedule-vio-checking j f1..fn   run up to j instances of Coq to check all\
\n                         proofs in each fi.vio\
\n  -vos                   process statements but ignore opaque proofs, and produce a .vos file\
\n  -vok                   process the file by loading .vos instead of .vo files for\
\n                         dependencies, and produce an empty .vok file on success\
\n  -vio                   process statements and suspend opaque proofs, and produce a .vio file\
\n\
\nUndocumented:\
\n  -quick                 (deprecated) alias for -vio\
\n  -vio2vo                [see manual]\
\n  -check-vio-tasks       [see manual]\
\n"
}

let coqc_main ((copts,_),stm_opts) injections ~opts =
  Topfmt.(in_phase ~phase:CompilationPhase)
    Ccompile.compile_file opts stm_opts copts injections;

  (* Careful this will modify the load-path and state so after this
     point some stuff may not be safe anymore. *)
  Topfmt.(in_phase ~phase:CompilationPhase)
    Ccompile.do_vio opts copts injections;

  flush_all();

  if copts.Coqcargs.output_context then begin
    let sigma, env = let e = Global.env () in Evd.from_env e, e in
    Feedback.msg_notice Pp.(Flags.(with_option raw_print (Prettyp.print_full_pure_context env) sigma) ++ fnl ())
  end;
  CProfile.print_profile ()

let coqc_run copts ~opts injections =
  let _feeder = Feedback.add_feeder Coqloop.coqloop_feed in
  try
    coqc_main ~opts copts injections;
    exit 0
  with exn ->
    flush_all();
    Topfmt.print_err_exn exn;
    flush_all();
    let exit_code = if (CErrors.is_anomaly exn) then 129 else 1 in
    exit exit_code

let custom_coqc : ((Coqcargs.t * Coqtop.color) * Stm.AsyncOpts.stm_opt, 'b) Coqtop.custom_toplevel
 = Coqtop.{
  parse_extra = (fun extras ->
    let color_mode, extras = Coqtop.parse_extra_colors extras in
    let stm_opts, extras = Stmargs.parse_args ~init:Stm.AsyncOpts.default_opts extras in
    let coqc_opts = Coqcargs.parse extras in
    ((coqc_opts, color_mode), stm_opts), []);
  usage = coqc_specific_usage;
  init_extra = coqc_init;
  run = coqc_run;
  initial_args = Coqargs.default;
}

let main () =
  Coqtop.start_coq custom_coqc
