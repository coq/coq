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
(* spiwack: This module contains stuff exfiltrated from Cerrors. *)

let handle_stack = ref []

exception Unhandled

let register_handler h = handle_stack := h::!handle_stack

(* spiwack: [anomaly_string] and [report_fn] are copies from Cerrors.
   Ultimately they should disapear from Cerrors. *)
let anomaly_string () = str "Anomaly: "
let report_fn () = (str "." ++ spc () ++ str "Please report.")
(* [print_unhandled_exception] is the virtual bottom of the stack:
   the [handle_stack] is treated as it if was always non-empty
   with [print_unhandled_exception] as its last handler. *)
let print_unhandled_exception e =
  hov 0 (anomaly_string () ++ str "Uncaught exception " ++
	 str (Printexc.to_string e) ++ report_fn ())

let rec print_gen s e =
  match s with
  | [] -> print_unhandled_exception e
  | h::s' ->
    try h e
    with
    | Unhandled -> print_gen s' e
    | e' -> print_gen s' e'

let print e = print_gen !handle_stack e


(*** Predefined handlers ***)

let where s =
  if !Flags.debug then  (str"in " ++ str s ++ str":" ++ spc ()) else (mt ())

let _ = register_handler begin function
  | Util.UserError(s,pps) ->
      hov 0 (str "Error: " ++ where s ++ pps)
  | Util.Anomaly (s,pps) ->
      hov 0 (anomaly_string () ++ where s ++ pps ++ report_fn ())
  | _ -> raise Unhandled
end

