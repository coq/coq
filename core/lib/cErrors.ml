(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

(* TODO remove the option *)
exception UserError of string option * Pp.t (* User errors *)

let user_err ?loc ?info ?hdr strm =
  let info = Option.default Exninfo.null info in
  let info = Option.cata (Loc.add_loc info) info loc in
  Exninfo.iraise (UserError (hdr, strm), info)

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
| None -> mt ()
| Some bt ->
  let bt = str (Exninfo.backtrace_to_string bt) in
  fnl () ++ hov 0 bt

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

let register_additional_error_info (f : Exninfo.info -> (Pp.t Loc.located) option) =
  additional_error_info_handler := f :: !additional_error_info_handler

(** [print_gen] is a general exception printer which tries successively
    all the handlers of a list, and finally a [bottom] handler if all
    others have failed *)

let rec print_gen ~anomaly ~extra_msg stk e =
  match stk with
  | [] ->
    print_anomaly anomaly e
  | h::stk' ->
    match h e with
    | Some err_msg ->
      extra_msg ++ err_msg
    | None ->
      print_gen ~anomaly ~extra_msg stk' e

let print_gen ~anomaly (e, info) =
  let extra_msg =
    CList.map_filter (fun f -> f info) !additional_error_info_handler
    (* Location info in the handler is ignored *)
    |> List.map snd |> Pp.seq
  in
  try
    print_gen ~anomaly ~extra_msg !handle_stack e
  with exn ->
    let exn, info = Exninfo.capture exn in
    (* exception in error printer *)
    str "<in exception printer>:" ++ print_backtrace info ++
    str "<original exception:" ++ print_anomaly anomaly exn

(** The standard exception printer *)
let iprint (e, info) =
  print_gen ~anomaly:true (e,info) ++ print_backtrace info

let print e =
  iprint (e, Exninfo.info e)

(** Same as [print], except that the "Please report" part of an anomaly
    isn't printed (used in Ltac debugging). *)
let iprint_no_report (e, info) =
  print_gen ~anomaly:false (e,info) ++ print_backtrace info
let print_no_report e = iprint_no_report (e, Exninfo.info e)

(** Predefined handlers **)

let _ = register_handler begin function
  | UserError(s, pps) ->
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
  | _ -> true
[@@@ocaml.warning "+52"]
