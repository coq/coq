(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type 'e profile_state_gen = {
  events : 'e;
  sums : NewProfile.sums;
  counters : NewProfile.Counters.t;
}

type profile_state = NewProfile.MiniJson.t list list profile_state_gen

let empty_profstate = {
  events = [];
  sums = NewProfile.empty_sums;
  counters = NewProfile.Counters.zero;
}

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
  | ControlProfile of { to_file : string option; profstate : profile_state }
  | ControlRedirect of { fname : string; truncate : bool}
  | ControlTimeout of { remaining : float }
  | ControlAllocLimit of { remaining : Control.kilowords; allocated : Control.kilowords }
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

let measure_profile f () =
  let start_cnt = NewProfile.Counters.get() in
  let events, sums, v = NewProfile.with_profiling (fun () ->
      try Ok (f ())
      with e -> Error (Exninfo.capture e))
  in
  let counters = NewProfile.Counters.(get() - start_cnt) in
  let prof = { events=events; sums; counters } in
  match v with
  | Ok v -> Ok (v,prof)
  | Error e -> Error (e, prof)

let add_profile a b = {
  events = if CList.is_empty b.events then a.events else b.events :: a.events;
  sums = NewProfile.sums_union a.sums b.sums;
  counters = NewProfile.Counters.(a.counters + b.counters);
}

let fmt_profiling counters (sums:NewProfile.sums) =
  let open Pp in
  let sums = CString.Map.bindings sums in
  let sums = List.sort (fun (_,(t1,_)) (_,(t2,_)) -> Float.compare t2 t1) sums in
  let longest = List.fold_left (fun longest (name,_) -> max longest (String.length name)) 0 sums in
  let pr_one (name,(time,cnt)) =
    hov 1
      (str name ++ str ":" ++ brk (1 + longest - String.length name, 0) ++
       str (Format.asprintf "%a" NewProfile.pptime time) ++
       pr_comma () ++ int cnt ++ str " calls")
  in
  v 0 (
  NewProfile.Counters.print counters ++ spc() ++ spc() ++
  prlist_with_sep spc pr_one sums)

(* Output comma and newline separated events given as a list of nonempty lists.
   The last event is not followed by a comma. *)
let rec output_events fmt = function
  | [] -> ()
  | [[last]] -> Format.fprintf fmt "%a\n" NewProfile.MiniJson.pr last
  | [] :: rest -> assert false
  | (current :: next) :: rest ->
    Format.fprintf fmt "%a,\n" NewProfile.MiniJson.pr current;
    match next with
    | [] -> output_events fmt rest
    | _::_ -> output_events fmt (next :: rest)

let fmt_profile to_file v =
  let {events;sums;counters} = match v with
    | Ok (_,x) -> x
    | Error (_,x) -> x
  in
  to_file |> Option.iter (fun to_file ->
      let to_file = System.get_output_path (to_file ^ ".json") in
      let f = open_out to_file in
      let fmt = Format.formatter_of_out_channel f in
      NewProfile.format_header fmt;
      output_events fmt events;
      NewProfile.format_footer fmt;
      close_out f
    );
  fmt_profiling counters sums

(* do not reuse Control.Timeout: once we hit the timeout handler the
   exn becomes a regular, noncritical error *)
exception CmdTimeout

let () = CErrors.register_handler (function
  | CmdTimeout -> Some Pp.(str "Timeout!")
  | _ -> None)

let with_timeout ~timeout:n f =
  check_timeout_f n;
  let start = Unix.gettimeofday () in
  begin match Control.timeout n f () with
  | Error info -> Exninfo.iraise (CmdTimeout, info)
  | Ok v ->
    let stop = Unix.gettimeofday () in
    let remaining = n -. (stop -. start) in
    if remaining <= 0. then raise CmdTimeout
    else Some (ControlTimeout { remaining }, v)
  end

exception AllocLimit

let () = CErrors.register_handler @@ function
  | AllocLimit -> Some Pp.(str "Allocation limit exceeded.")
  | _ -> None

let with_alloc_limit ~limit ~allocated f =
  let () = if limit.Control.kilowords <= 0L then
      CErrors.user_err Pp.(str "Alloc limit must be > 0.")
  in
  if not Memprof_coq.is_real_memprof then CWarnings.warn_no_memprof ();
  match Control.alloc_limit limit f () with
  | Error info -> Exninfo.iraise (AllocLimit,info)
  | Ok (v, {kilowords=alloc}) ->
    let remaining = Int64.sub limit.kilowords alloc in
    (* can remaining <= 0 actually happen? not sure *)
    if remaining <= 0L then raise AllocLimit;
    let remaining = { Control.kilowords = remaining } in
    let allocated = { Control.kilowords = Int64.add allocated.Control.kilowords alloc } in
    Some (ControlAllocLimit { remaining; allocated }, v)

let fmt_allocated { Control.kilowords = allocated } =
  let open Pp in
  (* XXX print a few more digits for low Mw allocated? *)
  let alloc = if allocated >= 1000L then
    int64 (Int64.div allocated 1000L) ++ str "Mw."
  else int64 allocated ++ str "kw."
  in
  fmt "Succeeded without reaching the allocation limit@ (estimated %t allocated)."
    (fun () -> alloc)

let real_error_loc ~cmdloc ~eloc =
  if Loc.finer eloc cmdloc then eloc
  else cmdloc

(* Restoring the state is the caller's responsibility *)
let with_fail f : (Loc.t option * Pp.t, 'a) result =
  try
    let x = f () in
    Error x
  with
  | e ->
    (* The error has to be printed in the failing state *)
    let _, info as exn = Exninfo.capture e in
    (* Don't catch async exceptions, don't turn anomalies into successes *)
    if CErrors.is_async e || CErrors.is_sync_anomaly e then Exninfo.iraise exn;
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
  | ControlProfile {to_file; profstate} ->
    with_measure measure_profile add_profile (fun v -> fmt_profile to_file v)
      (fun profstate -> ControlProfile {to_file; profstate})
      profstate
      f
  | ControlRedirect { fname; truncate } ->
    let v = Topfmt.with_output_to_file ~truncate fname f () in
    Some (ControlRedirect {fname; truncate=false}, v)
  | ControlTimeout {remaining} -> with_timeout ~timeout:remaining f
  | ControlAllocLimit {remaining; allocated} -> with_alloc_limit ~limit:remaining ~allocated f
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

let finish = function
  | ControlTime {duration} ->
    Feedback.msg_notice @@ System.fmt_transaction_result (Ok ((),duration));
    false
  | ControlInstructions {instructions} ->
    Feedback.msg_notice @@ System.fmt_instructions_result (Ok ((),instructions));
    false
  | ControlProfile {to_file; profstate} ->
    Feedback.msg_notice @@ fmt_profile to_file (Ok ((),profstate));
    false
  | ControlRedirect _ -> false
  | ControlTimeout _ -> false
  | ControlAllocLimit { remaining = _; allocated } ->
    Feedback.msg_notice @@ fmt_allocated allocated;
    false
  | ControlFail _ -> CErrors.user_err Pp.(str "The command has not failed!")
  | ControlSucceed _ -> true

let rec last_under_control ~loc ~with_local_state controls ~noop f =
  match controls with
  | [] -> f()
  | control :: rest ->
    let f () = last_under_control ~loc ~with_local_state rest ~noop f in
    match under_one_control ~loc ~with_local_state control f with
    | Some (control, v) ->
      if finish control then noop
      else v
    | None -> noop

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
    | { CAst.v = Vernacexpr.ControlTimeout _ } -> true
    | _ -> false)

let add_default_timeout control =
  match !default_timeout with
  | None -> control
  | Some n ->
    if has_timeout control then control
    else CAst.make (Vernacexpr.ControlTimeout n) :: control

let from_syntax_one : Vernacexpr.control_flag -> unit control_entry = fun flag ->
  match flag.v with
  | ControlTime -> ControlTime { duration = System.empty_duration }
  | ControlInstructions -> ControlInstructions { instructions = Ok 0L }
  | ControlProfile to_file -> ControlProfile {to_file; profstate = empty_profstate}
  | ControlRedirect s -> ControlRedirect { fname = s; truncate = true }
  | ControlTimeout timeout ->
    (* don't check_timeout here as the error won't be caught by surrounding Fail *)
    ControlTimeout { remaining = float_of_int timeout }
  | ControlAllocLimit limit -> ControlAllocLimit { remaining = limit; allocated = { kilowords = 0L } }
  | ControlFail -> ControlFail { st = () }
  | ControlSucceed -> ControlSucceed { st = () }

let from_syntax control = List.map from_syntax_one (add_default_timeout control)
