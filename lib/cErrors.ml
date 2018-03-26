(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp

(** Aliases *)

let push = Backtrace.add_backtrace

(* Errors *)

exception Anomaly of string option * Pp.t (* System errors *)

let _ =
  let pr = function
  | Anomaly (s, pp) -> Some ("\"Anomaly: " ^ string_of_ppcmds pp ^ "\"")
  | _ -> None
  in
  Printexc.register_printer pr

let make_anomaly ?label pp =
  Anomaly (label, pp)

let anomaly ?loc ?label pp =
  Loc.raise ?loc (Anomaly (label, pp))

let is_anomaly = function
| Anomaly _ -> true
| _ -> false

exception UserError of string option * Pp.t (* User errors *)

let todo s = prerr_string ("TODO: "^s^"\n")

let user_err ?loc ?hdr strm = Loc.raise ?loc (UserError (hdr, strm))

let invalid_arg ?loc s   = Loc.raise ?loc (Invalid_argument s)

exception AlreadyDeclared of Pp.t (* for already declared Schemes *)
let alreadydeclared pps = raise (AlreadyDeclared(pps))

exception Timeout

let handle_stack = ref []

exception Unhandled

let register_handler h = handle_stack := h::!handle_stack

(** [print_gen] is a general exception printer which tries successively
    all the handlers of a list, and finally a [bottom] handler if all
    others have failed *)

let rec print_gen bottom stk e =
  match stk with
  | [] -> bottom e
  | h::stk' ->
    try h e
    with
    | Unhandled -> print_gen bottom stk' e
    | any -> print_gen bottom stk' any

(** Only anomalies should reach the bottom of the handler stack.
    In usual situation, the [handle_stack] is treated as it if was always
    non-empty with [print_anomaly] as its bottom handler. *)

let where = function
| None -> mt ()
| Some s ->
  if !Flags.debug then str "in " ++ str s ++ str ":" ++ spc () else mt ()

let raw_anomaly e = match e with
  | Anomaly (s, pps) -> where s ++ pps
  | Assert_failure _ | Match_failure _ -> str (Printexc.to_string e) ++ str "."
  | _ -> str "Uncaught exception " ++ str (Printexc.to_string e) ++ str "."

let print_backtrace e = match Backtrace.get_backtrace e with
| None -> mt ()
| Some bt ->
  let bt = Backtrace.repr bt in
  let pr_frame f = str (Backtrace.print_frame f) in
  let bt = prlist_with_sep fnl pr_frame bt in
  fnl () ++ hov 0 bt

let print_anomaly askreport e =
  if askreport then
    hov 0 (str "Anomaly" ++ spc () ++ quote (raw_anomaly e)) ++ spc () ++
    hov 0 (str "Please report at " ++ str Coq_config.wwwbugtracker ++ str ".")
  else
    hov 0 (raw_anomaly e)

(** The standard exception printer *)
let print ?(info = Exninfo.null) e =
  print_gen (print_anomaly true) !handle_stack e ++ print_backtrace info

let iprint (e, info) = print ~info e

(** Same as [print], except that the "Please report" part of an anomaly
    isn't printed (used in Ltac debugging). *)
let print_no_report e = print_gen (print_anomaly false) !handle_stack e
let iprint_no_report (e, info) =
  print_gen (print_anomaly false) !handle_stack e ++ print_backtrace info

(** Predefined handlers **)

let _ = register_handler begin function
  | UserError(s, pps) ->
    hov 0 (where s ++ pps)
  | _ -> raise Unhandled
end

(** Critical exceptions should not be caught and ignored by mistake
    by inner functions during a [vernacinterp]. They should be handled
    only at the very end of interp, to be displayed to the user. *)

[@@@ocaml.warning "-52"]
let noncritical = function
  | Sys.Break | Out_of_memory | Stack_overflow
  | Assert_failure _ | Match_failure _ | Anomaly _
  | Timeout -> false
  | Invalid_argument "equal: functional value" -> false
  | _ -> true
[@@@ocaml.warning "+52"]

(** Check whether an exception is handled *)

exception Bottom

let handled e =
  let bottom _ = raise Bottom in
  try let _ = print_gen bottom !handle_stack e in true
  with Bottom -> false
