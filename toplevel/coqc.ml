(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
  Colors.init_color color_mode;
  DebugHook.Intf.(set
    { read_cmd = Coqtop.ltac_debug_parse
    ; submit_answer = Coqtop.ltac_debug_answer
    ; isTerminal = true
    });
  injections

let coqc_specific_usage = Boot.Usage.{
  executable_name = "rocq compile";
  extra_args = "file...";
  extra_options = "\n\
rocq compile specific options:\
\n  -o f.vo                use f.vo as the output file name\
\n  -verbose               compile and output the input file\
\n  -noglob                do not dump globalizations\
\n  -dump-glob f           dump globalizations in file f (to be used by coqdoc)\
\n  -vos                   process statements but ignore opaque proofs, and produce a .vos file\
\n  -vok                   process the file by loading .vos instead of .vo files for\
\n                         dependencies, and produce an empty .vok file on success\
\n"
}

let coqc_main ((copts,_),stm_opts) injections ~opts =
  Topfmt.(in_phase ~phase:CompilationPhase)
    Ccompile.compile_file opts stm_opts copts injections;

  flush_all();

  if copts.Coqcargs.output_context then begin
    let sigma, env = let e = Global.env () in Evd.from_env e, e in
    let access = Library.indirect_accessor[@@warning "-3"] in
    Feedback.msg_notice Pp.(Flags.(with_option raw_print (fun () ->
        Prettyp.print_full_pure_context access env sigma) ()) ++ fnl ())
  end;
  ()

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

let fix_stm_opts opts stm_opts = match opts.Coqcargs.compilation_mode with
  | BuildVos ->
    (* We need to disable error resiliency, otherwise some errors
       will be ignored in batch mode. c.f. #6707

       This is not necessary in the vo case as it fully checks the
       document anyways. *)
    let open Stm.AsyncOpts in
    { stm_opts with
      async_proofs_mode = APon;
      async_proofs_n_workers = 0;
      async_proofs_cmd_error_resilience = false;
      async_proofs_tac_error_resilience = FNone;
    }
  | BuildVo | BuildVok -> stm_opts

let custom_coqc : ((Coqcargs.t * Colors.color) * Stm.AsyncOpts.stm_opt, 'b) Coqtop.custom_toplevel
 = Coqtop.{
  parse_extra = (fun opts extras ->
    let color_mode, extras = Colors.parse_extra_colors ~emacs:opts.config.print_emacs extras in
    let stm_opts, extras = Stmargs.parse_args opts extras in
    let coqc_opts = Coqcargs.parse extras in
    let stm_opts = fix_stm_opts coqc_opts stm_opts in
    ((coqc_opts, color_mode), stm_opts), []);
  usage = coqc_specific_usage;
  init_extra = coqc_init;
  run = coqc_run;
  initial_args = Coqargs.default;
}

let main args =
  let () = Memtrace_init.init () in
  Coqtop.start_coq custom_coqc args
