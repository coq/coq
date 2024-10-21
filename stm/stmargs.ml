(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let fatal_error exn =
  Topfmt.(in_phase ~phase:ParsingCommandLine print_err_exn exn);
  let exit_code = if (CErrors.is_anomaly exn) then 129 else 1 in
  exit exit_code

let set_worker_id opt s =
  assert (s <> "master");
  Flags.async_proofs_worker_id := s

let get_host_port opt s =
  match String.split_on_char ':' s with
  | [host; portr; portw] ->
    Some (Spawned.Socket(host, int_of_string portr, int_of_string portw))
  | ["stdfds"] -> Some Spawned.AnonPipe
  | _ ->
    Coqargs.error_wrong_arg ("Error: host:portr:portw or stdfds expected after option "^opt)

let get_error_resilience opt = function
  | "on" | "all" | "yes" -> Stm.AsyncOpts.FAll
  | "off" | "no" -> Stm.AsyncOpts.FNone
  | s -> Stm.AsyncOpts.FOnly (String.split_on_char ',' s)

let get_priority opt s =
  try CoqworkmgrApi.priority_of_string s
  with Invalid_argument _ ->
    Coqargs.error_wrong_arg ("Error: low/high expected after "^opt)

let get_async_proofs_mode opt = let open Stm.AsyncOpts in function
  | "no" | "off" -> APoff
  | "yes" | "on" -> APon
  | "lazy" -> APonLazy
  | _ ->
    Coqargs.error_wrong_arg ("Error: on/off/lazy expected after "^opt)

let get_cache opt = function
  | "force" -> Some Stm.AsyncOpts.Force
  | _ ->
    Coqargs.error_wrong_arg ("Error: force expected after "^opt)

let spawn_args (opts:Coqargs.t) =
  (* Coqargs whose effect is not in the summary and matters for workers:

     Flags.output_directory
     Flags.test_mode
     native output dir, native includes

     Coqargs whose effect is used before the summary is installed and matter for workers:

     -I, -boot

     and we force -q -noinit otherwise the worker will try to require the
     rcfile and prelude before receiving the summary

     AFAICT that's all *)
  let output_dir = match opts.config.output_directory with
    | None -> []
    | Some dir -> ["-output-directory";dir]
  in
  let test_mode = if opts.config.test_mode then ["-test-mode"] else [] in
  let native_output = ["-native-output-dir"; opts.config.native_output_dir] in
  let native_include ni = ["-nI";ni] in
  let native_includes = CList.concat_map native_include opts.config.native_include_dirs in
  let ml_include i = ["-I"; i] in
  let ml_includes = CList.concat_map ml_include opts.pre.ml_includes in
  let boot = if opts.pre.boot then ["-boot"] else [] in
  List.concat [
    output_dir;
    test_mode;
    native_output;
    native_includes;
    ml_includes;
    boot;
    ["-q"; "-noinit"]
  ]


let parse_args opts arglist : Stm.AsyncOpts.stm_opt * string list =
  let init = Stm.AsyncOpts.default_opts ~spawn_args:(spawn_args opts) in
  let args = ref arglist in
  let extras = ref [] in
  let rec parse oval = match !args with
  | [] ->
    (oval, List.rev !extras)
  | opt :: rem ->
    args := rem;
    let next () = match !args with
      | x::rem -> args := rem; x
      | [] -> Coqargs.error_missing_arg opt
    in
    let noval = begin match opt with

    |"-async-proofs" ->
      { oval with
        Stm.AsyncOpts.async_proofs_mode = get_async_proofs_mode opt (next())
      }
    |"-async-proofs-j" ->
      { oval with
        Stm.AsyncOpts.async_proofs_n_workers = (Coqargs.get_int ~opt (next ()))
      }
    |"-async-proofs-cache" ->
      { oval with
        Stm.AsyncOpts.async_proofs_cache = get_cache opt (next ())
      }

    |"-async-proofs-tac-j" ->
      let j = Coqargs.get_int ~opt (next ()) in
      if j < 0 then begin
        Coqargs.error_wrong_arg ("Error: -async-proofs-tac-j only accepts values greater than or equal to 0")
      end;
      { oval with
        Stm.AsyncOpts.async_proofs_n_tacworkers = j
      }

    |"-async-proofs-worker-priority" ->
      { oval with
        Stm.AsyncOpts.async_proofs_worker_priority = get_priority opt (next ())
      }

    |"-async-proofs-private-flags" ->
      { oval with
        Stm.AsyncOpts.async_proofs_private_flags = Some (next ());
      }

    |"-async-proofs-tactic-error-resilience" ->
      { oval with
        Stm.AsyncOpts.async_proofs_tac_error_resilience = get_error_resilience opt (next ())
      }

    |"-async-proofs-command-error-resilience" ->
      { oval with
        Stm.AsyncOpts.async_proofs_cmd_error_resilience = Coqargs.get_bool ~opt (next ())
      }

    |"-async-proofs-delegation-threshold" ->
      { oval with
        Stm.AsyncOpts.async_proofs_delegation_threshold = Coqargs.get_float ~opt (next ())
      }

    |"-worker-id" -> set_worker_id opt (next ()); oval

    |"-main-channel" ->
      let ch = next () in
      Spawned.main_channel := get_host_port opt ch;
      { oval with spawn_args = opt :: ch :: oval.spawn_args }

    |"-control-channel" ->
      let ch = next () in
      Spawned.control_channel := get_host_port opt ch;
      { oval with spawn_args = opt :: ch :: oval.spawn_args }

    (* Options with zero arg *)
    |"-async-queries-always-delegate"
    |"-async-proofs-always-delegate"
    |"-async-proofs-never-reopen-branch" ->
      { oval with
        Stm.AsyncOpts.async_proofs_never_reopen_branch = true;
        spawn_args = opt :: oval.spawn_args;
      }
    |"-stm-debug" -> Stm.stm_debug := true; { oval with spawn_args = opt :: oval.spawn_args }
    (* Unknown option *)
    | s ->
      extras := s :: !extras;
      oval
    end in
    parse noval
  in
  try
    parse init
  with any -> fatal_error any

let usage = "\
\n  -stm-debug             STM debug mode (will trace every transaction)\
"
