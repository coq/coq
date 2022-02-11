(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let worker_parse_extra extra_args =
  let stm_opts, extra_args = Stmargs.parse_args ~init:Stm.AsyncOpts.default_opts extra_args in
  ((),stm_opts), extra_args

let worker_init init ((),stm_opts)  injections ~opts : Vernac.State.t =
  Flags.quiet := true;
  init ();
  Coqtop.init_toploop opts stm_opts injections

let worker_specific_usage name = Boot.Usage.{
  executable_name = name;
  extra_args = "";
  extra_options = ("\n" ^ name ^ " specific options:\
\n  --xml_format=Ppcmds    serialize pretty printing messages using the std_ppcmds format\n");
}

let start ~init ~loop name =
  let open Coqtop in
  let custom = {
    parse_extra = worker_parse_extra;
    usage = worker_specific_usage name;
    initial_args = Coqargs.default;
    init_extra = worker_init init;
    run = (fun ((),_) ~opts:_ (_state : Vernac.State.t) ->
      (* the state is not used since the worker will receive one from master *)
      loop ());
  } in
  start_coq custom
