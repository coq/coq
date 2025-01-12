(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp

(** Aliases *)

let push = Exninfo.capture

(* Errors *)

exception Anomaly of string option * Pp.t (* System errors *)

let _ =
  let pr = function
  | Anomaly (s, pp) -> Some ("\"Anomaly: " ^ string_of_ppcmds pp ^ "\"")
  | _ -> None
  in
  Printexc.register_printer pr

let anomaly ?loc ?info ?label pp =
  let info = Option.default Exninfo.null info in
  let info = Option.cata (Loc.add_loc info) info loc in
  Exninfo.iraise (Anomaly (label, pp), info)

exception UserError of Pp.t (* User errors *)

(* We register Rocq Errors with the global printer here as they will be
   printed if Dynlink.loadfile raises UserError in the module
   intializers, and in some other cases. We should make this more
   principled. *)
let _ = Printexc.register_printer (function
    | UserError msg ->
      Some (Format.asprintf "@[Rocq Error: %a@]" Pp.pp_with msg)
    | _ -> None)

let user_err ?loc ?info strm =
  let info = Option.default Exninfo.null info in
  let info = Option.cata (Loc.add_loc info) info loc in
  Exninfo.iraise (UserError strm, info)

exception Timeout = Control.Timeout

(** Only anomalies should reach the bottom of the handler stack.
    In usual situation, the [handle_stack] is treated as it if was always
    non-empty with [print_anomaly] as its bottom handler. *)

let where = function
| None -> mt ()
| Some s ->
  str "in " ++ str s ++ str ":" ++ spc ()

let raw_anomaly e = match e with
  | Anomaly (s, pps) ->
    where s ++ pps
  | Assert_failure _ | Match_failure _ ->
    str (Printexc.to_string e) ++ str "."
  | _ ->
    str "Uncaught exception " ++ str (Printexc.to_string e) ++ str "."

let print_backtrace e = match Exninfo.get_backtrace e with
| None -> None
| Some bt ->
  let bt = str (Exninfo.backtrace_to_string bt) in
  Some (hov 0 bt)

let print_anomaly askreport e =
  if askreport then
    hov 0 (str "Anomaly" ++ spc () ++ quote (raw_anomaly e)) ++ spc () ++
    hov 0 (str "Please report at " ++ str Coq_config.wwwbugtracker ++ str ".")
  else
    hov 0 (raw_anomaly e)

let handle_stack = ref []

let register_handler h = handle_stack := h::!handle_stack

let is_handled e =
  let is_handled_by h = Option.has_some (h e) in
  List.exists is_handled_by !handle_stack

let is_anomaly = function
| Anomaly _ -> true
| exn -> not (is_handled exn)

(** Printing of additional error info, from Exninfo *)
let additional_error_info_handler = ref []

let register_additional_error_info (f : Exninfo.info -> Pp.t option) =
  additional_error_info_handler := f :: !additional_error_info_handler

let () = register_additional_error_info print_backtrace

(** [print_gen] is a general exception printer which tries successively
    all the handlers of a list, and finally a [bottom] handler if all
    others have failed *)

let rec print_gen ~anomaly stk e =
  match stk with
  | [] ->
    print_anomaly anomaly e
  | h::stk' ->
    match h e with
    | Some err_msg -> err_msg
    | None -> print_gen ~anomaly stk' e

let print_extra info =
  let pp =
    CList.map_filter (fun f -> f info) !additional_error_info_handler
  in
  if CList.is_empty pp then mt()
  else fnl() ++ prlist_with_sep fnl (fun x -> x) pp

let print_gen ~anomaly (e, info) =
  let extra_msg = print_extra info in
  try
    print_gen ~anomaly !handle_stack e ++ extra_msg
  with exn ->
    let exn, info = Exninfo.capture exn in
    (* exception in error printer *)
    str "<in exception printer>:" ++ spc() ++ print_anomaly anomaly exn ++ print_extra info ++ fnl() ++
    str "<original exception>:" ++ spc() ++ print_anomaly false e ++ extra_msg

let print_quickfix = function
  | [] -> mt ()
  | qf -> fnl () ++ Quickfix.print qf

(** The standard exception printer *)
let iprint (e, info) =
  print_gen ~anomaly:true (e,info) ++
  if !Flags.test_mode then
    Result.fold ~ok:print_quickfix ~error:(print_gen ~anomaly:true) (Quickfix.from_exception e)
  else
    mt ()

let print e =
  iprint (e, Exninfo.info e)

(** Same as [print], except that the "Please report" part of an anomaly
    isn't printed (used in Ltac debugging). *)
let iprint_no_report (e, info) =
  print_gen ~anomaly:false (e,info)
let print_no_report e = iprint_no_report (e, Exninfo.info e)

(** Predefined handlers **)

let _ = register_handler begin function
  | UserError pps ->
    Some pps
  | _ -> None
  end

(** Critical exceptions should not be caught and ignored by mistake
    by inner functions during a [vernacinterp]. They should be handled
    only at the very end of interp, to be displayed to the user. *)

[@@@ocaml.warning "-52"]
let noncritical = function
  | Sys.Break | Out_of_memory | Stack_overflow
  | Assert_failure _ | Match_failure _ | Anomaly _
  | Control.Timeout -> false
  | Invalid_argument "equal: functional value" -> false
  | _ -> not (Memprof_coq.is_interrupted ())
[@@@ocaml.warning "+52"]

(* This should be in exninfo, but noncritical is here... *)
let to_result ~f x =
  try Ok (f x)
  with exn when noncritical exn ->
    let iexn = Exninfo.capture exn in
    Error iexn
