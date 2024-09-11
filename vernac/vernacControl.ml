(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Partially interpreted control flags.

    [ControlTime {duration}] means "Time" where the
    partial interpretation has already take [duration].

    In [ControlRedirect], [truncate] tells whether we should truncate
    the file before printing (ie [false] if not the first phase).
    Alternatively we could do [ControlRedirect of out_channel],
    but that risks leaking open channels.

    [ControlFail {st}] means "Fail" where the partial interpretation
    did not fail and produced state [st].

    [ControlSucceed {st}] means "Succeed" where the partial
    interpretation succeeded and produced state [st].
*)
type 'state control_entry =
  | ControlTime of { duration: System.duration }
  | ControlInstructions of { instructions: System.instruction_count }
  | ControlRedirect of { fname : string; truncate : bool}
  | ControlTimeout of { remaining : float }
  | ControlFail of { st : 'state }
  | ControlSucceed of { st : 'state }

type 'state control_entries = 'state control_entry list

let check_timeout_f n =
  if n <= 0. then CErrors.user_err Pp.(str "Timeout must be > 0.")

let with_measure measure add fmt flag init f =
  let result = measure f () in
  let result = match result with
    | Ok (v,d) -> Ok (v, add init d)
    | Error (e,d) -> Error (e, add init d)
  in
  begin match result with
  | Ok (v,result) -> Some (flag result, v)
  | Error (e,_) ->
    Feedback.msg_notice @@ fmt result;
    Exninfo.iraise e
  end

let with_timeout ~timeout:n f =
  check_timeout_f n;
  let start = Unix.gettimeofday () in
  begin match Control.timeout n f () with
  | None -> Exninfo.iraise (Exninfo.capture CErrors.Timeout)
  | Some v ->
    let stop = Unix.gettimeofday () in
    let remaining = n -. (stop -. start) in
    if remaining <= 0. then Exninfo.iraise (Exninfo.capture CErrors.Timeout)
    else Some (ControlTimeout { remaining }, v)
  end

let real_error_loc ~cmdloc ~eloc =
  if Loc.finer eloc cmdloc then eloc
  else cmdloc

(* Restoring the state is the caller's responsibility *)
let with_fail f : (Loc.t option * Pp.t, 'a) result =
  try
    let x = f () in
    Error x
  with
  (* Fail Timeout is a common pattern so we need to support it. *)
  | e ->
    (* The error has to be printed in the failing state *)
    let _, info as exn = Exninfo.capture e in
    if CErrors.is_anomaly e && e != CErrors.Timeout then Exninfo.iraise exn;
    Ok (Loc.get_loc info, CErrors.iprint exn)

type ('st0,'st) with_local_state = { with_local_state : 'a. 'st0 -> (unit -> 'a) -> 'st * 'a }

let trivial_state = { with_local_state = fun () f -> (), f () }

let with_fail ~loc ~with_local_state st0 f =
  let transient_st, res = with_local_state.with_local_state st0 (fun () -> with_fail f) in
  match res with
  | Error v ->
    Some (ControlFail { st = transient_st }, v)
  | Ok (eloc, msg) ->
    let loc = if !Flags.test_mode then real_error_loc ~cmdloc:loc ~eloc else None in
    if not !Flags.quiet || !Flags.test_mode
    then Feedback.msg_notice ?loc Pp.(str "The command has indeed failed with message:" ++ fnl () ++ msg);
    None

let with_succeed ~with_local_state st0 f =
  let transient_st, v = with_local_state.with_local_state st0 f in
  Some (ControlSucceed { st = transient_st }, v)

let under_one_control ~loc ~with_local_state control f =
  match control with
  | ControlTime { duration } ->
    with_measure System.measure_duration System.duration_add System.fmt_transaction_result
      (fun duration -> ControlTime {duration})
      duration
      f
  | ControlInstructions {instructions} ->
    with_measure System.count_instructions System.instruction_count_add System.fmt_instructions_result
      (fun instructions -> ControlInstructions {instructions})
      instructions
      f
  | ControlRedirect { fname; truncate } ->
    let v = Topfmt.with_output_to_file ~truncate fname f () in
    Some (ControlRedirect {fname; truncate=false}, v)
  | ControlTimeout {remaining} -> with_timeout ~timeout:remaining f
  | ControlFail {st} -> with_fail ~loc ~with_local_state st f
  | ControlSucceed {st} -> with_succeed ~with_local_state st f

let rec under_control ~loc ~with_local_state controls ~noop f =
  match controls with
  | [] -> [], f ()
  | control :: rest ->
    let f () = under_control ~loc ~with_local_state rest ~noop f in
    match under_one_control ~loc ~with_local_state control f with
    | Some (control, (rest,v)) -> control :: rest, v
    | None -> [], noop

let ignore_state = { with_local_state = fun _ f -> (), f () }

let rec after_last_phase ~loc = function
  | [] -> false
  | control :: rest ->
    (* don't match on [control] before processing [rest]: correctly handle eg [Fail Fail]. *)
    let rest () = after_last_phase ~loc rest in
    match under_one_control ~loc ~with_local_state:ignore_state control rest with
    | None -> true
    | Some (control,noop) ->
      match control with
      | ControlTime {duration} ->
        Feedback.msg_notice @@ System.fmt_transaction_result (Ok ((),duration));
        noop
      | ControlInstructions {instructions} ->
        Feedback.msg_notice @@ System.fmt_instructions_result (Ok ((),instructions));
        noop
      | ControlRedirect _ -> noop
      | ControlTimeout _ -> noop
      | ControlFail _ -> CErrors.user_err Pp.(str "The command has not failed!")
      | ControlSucceed _ -> true

(** A global default timeout, controlled by option "Set Default Timeout n".
    Use "Unset Default Timeout" to deactivate it. *)

let default_timeout = ref None

let check_timeout n =
  if n <= 0 then CErrors.user_err Pp.(str "Timeout must be > 0.")

let () = let open Goptions in
  declare_int_option
    { optstage = Summary.Stage.Synterp;
      optdepr  = None;
      optkey   = ["Default";"Timeout"];
      optread  = (fun () -> !default_timeout);
      optwrite = (fun n -> Option.iter check_timeout n; default_timeout := n) }

let has_timeout ctrl = ctrl |> List.exists (function
    | Vernacexpr.ControlTimeout _ -> true
    | _ -> false)

let add_default_timeout control =
  match !default_timeout with
  | None -> control
  | Some n ->
    if has_timeout control then control
    else Vernacexpr.ControlTimeout n :: control

let from_syntax_one : Vernacexpr.control_flag -> unit control_entry = function
  | ControlTime -> ControlTime { duration = System.empty_duration }
  | ControlInstructions -> ControlInstructions { instructions = Ok 0L }
  | ControlRedirect s -> ControlRedirect { fname = s; truncate = true }
  | ControlTimeout timeout ->
    (* don't check_timeout here as the error won't be caught by surrounding Fail *)
    ControlTimeout { remaining = float_of_int timeout }
  | ControlFail -> ControlFail { st = () }
  | ControlSucceed -> ControlSucceed { st = () }

let from_syntax control = List.map from_syntax_one (add_default_timeout control)
