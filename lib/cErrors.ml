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

let () =
  let pr = function
  | Anomaly (s, pp) -> Some ("\"Anomaly: " ^ string_of_ppcmds pp ^ "\"")
  | _ -> None
  in
  Printexc.register_printer pr

let anomaly ?loc ?info ?label pp =
  let info = Option.default Exninfo.null info in
  let info = Option.cata (Loc.add_loc info) info loc in
  Exninfo.iraise (Anomaly (label, pp), info)

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

type _ tag = ..

module E = PolyMap.Make(struct type nonrec 'e tag = 'e tag = .. end)
module EMap = E.Map(struct type 'a t = 'a -> Pp.t end)

type exn += CoqError : 'e tag * 'e -> exn

let coq_error ?loc ?info e v =
  let info = Option.default Exninfo.null info in
  let info = Option.cata (Loc.add_loc info) info loc in
  Exninfo.iraise (CoqError (e, v), info)

let handlers = ref EMap.empty

module type Register = sig
  type e
  type _ tag += T : e tag
  val pp : e -> Pp.t
end

let register (module M : Register) =
  handlers :=
    EMap.add
      (module struct
        type a = M.e
        type _ tag += T = M.T
      end)
      M.pp
      !handlers

let handle_stack = ref []

let register_handler h = handle_stack := h::!handle_stack

(* Keep in sync with print_gen below *)
let is_handled e =
  match e with
  | CoqError (e, _) -> true

  (* Exceptions not defined by Coq *)
  | Sys_error _ -> true
  | Out_of_memory -> true
  | Stack_overflow -> true
  | Sys.Break -> true

  (* This is a handled error defined by coq, but special because critical.
     Not sure if can/should be turned into a CoqError. *)
  | Control.Timeout -> true

  | _ ->
    let is_handled_by h = Option.has_some (h e) in
    List.exists is_handled_by !handle_stack

let is_anomaly = function
| Anomaly _ -> true
| exn -> not (is_handled exn)

(* keep in sync with is_handled above *)
let print_gen ~anomaly = function
  | CoqError (t, v) as e ->
    begin match EMap.find t !handlers with
    | pp -> pp v
    | exception Not_found -> print_anomaly anomaly e
    end
  | Sys_error msg -> hov 0 (str "System error: " ++ quote (str msg))
  | Out_of_memory -> hov 0 (str "Out of memory.")
  | Stack_overflow -> hov 0 (str "Stack overflow.")
  | Sys.Break -> hov 0 (str "User interrupt.")
  | Control.Timeout -> hov 0 (str "Timeout!")
  | e ->
    match CList.find_map (fun h -> h e) !handle_stack with
    | pp -> pp
    | exception Not_found ->
      print_anomaly anomaly e

(** Printing of additional error info, from Exninfo *)
let additional_error_info_handler = ref []

let register_additional_error_info (f : Exninfo.info -> Pp.t option) =
  additional_error_info_handler := f :: !additional_error_info_handler

let print_gen ~anomaly (e, info) =
  let extra_msg =
    CList.map_filter (fun f -> f info) !additional_error_info_handler
    (* Location info in the handler is ignored *)
    |> Pp.seq
  in
  try
    extra_msg ++ print_gen ~anomaly e
  with exn ->
    let exn, info = Exninfo.capture exn in
    (* exception in error printer *)
    str "<in exception printer>:" ++ spc() ++ print_anomaly anomaly exn ++
    print_backtrace info ++ fnl() ++
    str "<original exception>:" ++ spc() ++ extra_msg ++ print_anomaly false e

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

type _ tag += UserError : Pp.t tag (* User errors *)

let () = register (module struct
    type e = Pp.t
    type _ tag += T = UserError
    let pp x = x
  end)

(* We register Coq Errors with the global printer here as they will be
   printed if Dynlink.loadfile raises UserError in the module
   intializers, and in some other cases. We should make this more
   principled. *)
let () = Printexc.register_printer (function
    | CoqError (UserError, msg) ->
      Some (Format.asprintf "@[Coq Error: %a@]" Pp.pp_with msg)
    | _ -> None)

let user_err ?loc ?info strm =
  coq_error ?loc ?info UserError strm

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
