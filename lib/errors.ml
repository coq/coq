(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

open Pp

(** Aliases *)

let push = Backtrace.add_backtrace

(* Errors *)

exception Anomaly of string option * std_ppcmds (* System errors *)

let _ =
  let pr = function
  | Anomaly (s, pp) -> Some ("\"Anomaly: " ^ string_of_ppcmds pp ^ "\"")
  | _ -> None
  in
  Printexc.register_printer pr

let make_anomaly ?label pp =
  Anomaly (label, pp)

let anomaly ?loc ?label pp = match loc with
  | None -> raise (Anomaly (label, pp))
  | Some loc -> Loc.raise loc (Anomaly (label, pp))

let is_anomaly = function
| Anomaly _ -> true
| _ -> false

exception UserError of string * std_ppcmds (* User errors *)
let error string = raise (UserError("_", str string))
let errorlabstrm l pps = raise (UserError(l,pps))

exception AlreadyDeclared of std_ppcmds (* for already declared Schemes *)
let alreadydeclared pps = raise (AlreadyDeclared(pps))

let todo s = prerr_string ("TODO: "^s^"\n")

let user_err_loc (loc,s,strm) = Loc.raise loc (UserError (s,strm))
let invalid_arg_loc (loc,s) = Loc.raise loc (Invalid_argument s)

exception Timeout
exception Drop
exception Quit

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
  | Anomaly (s, pps) -> where s ++ pps ++ str "."
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
    hov 0 (str "Anomaly: " ++ raw_anomaly e ++ spc () ++ str "Please report.")
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
    hov 0 (str "Error: " ++ where (Some s) ++ pps)
  | _ -> raise Unhandled
end

(** Critical exceptions should not be caught and ignored by mistake
    by inner functions during a [vernacinterp]. They should be handled
    only at the very end of interp, to be displayed to the user. *)

let noncritical = function
  | Sys.Break | Out_of_memory | Stack_overflow
  | Assert_failure _ | Match_failure _ | Anomaly _
  | Timeout | Drop | Quit -> false
  | Invalid_argument "equal: functional value" -> false
  | _ -> true

(** Check whether an exception is handled *)

exception Bottom

let handled e =
  let bottom _ = raise Bottom in
  try let _ = print_gen bottom !handle_stack e in true
  with Bottom -> false

(** Prints info which is either an error or
   an anomaly and then exits with the appropriate
   error code *)

let fatal_error info anomaly =
  let msg = info ++ fnl () in
  pp_with ~pp_tag:Ppstyle.pp_tag !Pp_control.err_ft msg;
  Format.pp_print_flush !Pp_control.err_ft ();
  exit (if anomaly then 129 else 1)
