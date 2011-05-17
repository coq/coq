(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

open Pp

(* spiwack: it might be reasonable to decide and move the declarations
   of Anomaly and so on to this module so as not to depend on Util. *)

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
    | e' -> print_gen bottom stk' e'

(** Only anomalies should reach the bottom of the handler stack.
    In usual situation, the [handle_stack] is treated as it if was always
    non-empty with [print_anomaly] as its bottom handler. *)

let where s =
  if !Flags.debug then str ("in "^s^":") ++ spc () else mt ()

let raw_anomaly e = match e with
  | Util.Anomaly (s,pps) -> where s ++ pps ++ str "."
  | Assert_failure _ | Match_failure _ -> str (Printexc.to_string e ^ ".")
  | _ -> str ("Uncaught exception " ^ Printexc.to_string e ^ ".")

let print_anomaly askreport e =
  if askreport then
    hov 0 (str "Anomaly: " ++ raw_anomaly e ++ spc () ++ str "Please report.")
  else
    hov 0 (raw_anomaly e)

(** The standard exception printer *)
let print e = print_gen (print_anomaly true) !handle_stack e

(** Same as [print], except that the "Please report" part of an anomaly
    isn't printed (used in Ltac debugging). *)
let print_no_report e = print_gen (print_anomaly false) !handle_stack e

(** Same as [print], except that anomalies are not printed but re-raised
    (used for the Fail command) *)
let print_no_anomaly e = print_gen (fun e -> raise e) !handle_stack e

(** Predefined handlers **)

let _ = register_handler begin function
  | Util.UserError(s,pps) -> hov 0 (str "Error: " ++ where s ++ pps)
  | _ -> raise Unhandled
end

