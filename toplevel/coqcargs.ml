(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type compilation_mode = BuildVo | BuildVos | BuildVok

type t =
  { compilation_mode : compilation_mode

  ; compile_file: (string * bool) option  (* bool is verbosity  *)
  ; compilation_output_name : string option

  ; echo : bool

  ; glob_out    : Dumpglob.glob_output

  ; output_context : bool
  }

let default =
  { compilation_mode = BuildVo

  ; compile_file = None
  ; compilation_output_name = None

  ; echo = false

  ; glob_out = Dumpglob.MultFiles

  ; output_context = false
  }

let depr opt =
  Feedback.msg_warning Pp.(seq[str "Option "; str opt; str " is a noop and deprecated"])

(* XXX Remove this duplication with Coqargs *)
let fatal_error exn =
  Topfmt.(in_phase ~phase:ParsingCommandLine print_err_exn exn);
  let exit_code = if (CErrors.is_anomaly exn) then 129 else 1 in
  exit exit_code

let error_missing_arg s =
  prerr_endline ("Error: extra argument expected after option "^s);
  prerr_endline "See -help for the syntax of supported options";
  exit 1

let arg_error msg = CErrors.user_err msg

let is_dash_argument s = String.length s > 0 && s.[0] = '-'

let add_compile ?echo copts s =
  if is_dash_argument s then
    arg_error Pp.(str "Unknown option " ++ str s);
  (* make the file name explicit; needed not to break up Rocq loadpath stuff. *)
  let echo = Option.default copts.echo echo in
  let s =
    let open Filename in
    if is_implicit s
    then concat current_dir_name s
    else s
  in
  { copts with compile_file = Some (s,echo) }

let add_compile ?echo copts v_file =
  match copts.compile_file with
  | Some (first,_) ->
    arg_error Pp.(str "More than one file to compile: " ++ str first ++ spc() ++
                  str "and " ++ str v_file)
  | None ->
    add_compile ?echo copts v_file

let parse arglist : t =
  let echo = ref false in
  let args = ref arglist in
  let extras = ref [] in
  let rec parse (oval : t) = match !args with
    | [] ->
      (oval, List.rev !extras)
    | opt :: rem ->
      args := rem;
      let next () = match !args with
        | x::rem -> args := rem; x
        | [] -> error_missing_arg opt
      in
      let noval : t = begin match opt with
        (* Deprecated options *)
        | "-opt"
        | "-byte" as opt ->
          depr opt;
          oval
        | "-image" as opt ->
          depr opt;
          let _ = next () in
          oval

        (* Non deprecated options *)
        | "-output-context" ->
          { oval with output_context = true }
        (* Verbose == echo mode *)
        | "-verbose" ->
          echo := true;
          oval
        (* Output filename *)
        | "-o" ->
          { oval with compilation_output_name = Some (next ()) }
        |"-vos" ->
          Flags.load_vos_libraries := true;
          { oval with compilation_mode = BuildVos }
        |"-vok" ->
          Flags.load_vos_libraries := true;
          { oval with compilation_mode = BuildVok }

        (* Glob options *)
        |"-no-glob" | "-noglob" ->
          { oval with glob_out = Dumpglob.NoGlob }

        |"-dump-glob" ->
          let file = next () in
          { oval with glob_out = Dumpglob.File file }

        (* Rest *)
        | s ->
          extras := s :: !extras;
          oval
      end in
      parse noval
  in
  try
    let opts, extra = parse default in
    let args = List.fold_left add_compile opts extra in
    args
  with any -> fatal_error any
