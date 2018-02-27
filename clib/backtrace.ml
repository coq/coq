(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
[@@@ocaml.warning "-37"]

type raw_frame =
| Known_location of bool   (* is_raise *)
  * string (* filename *)
  * int    (* line number *)
  * int    (* start char *)
  * int    (* end char *)
| Unknown_location of bool (*is_raise*)

type location = {
  loc_filename : string;
  loc_line : int;
  loc_start : int;
  loc_end : int;
}

type frame = { frame_location : location option; frame_raised : bool; }

external get_exception_backtrace: unit -> raw_frame array option
  = "caml_get_exception_backtrace"

type t = raw_frame array list
(** List of partial raw stack frames, in reverse order *)

let empty = []

let of_raw = function
| Unknown_location r ->
  { frame_location = None; frame_raised = r; }
| Known_location (r, file, line, st, en) ->
  let loc = {
    loc_filename = file;
    loc_line = line;
    loc_start = st;
    loc_end = en;
  } in
  { frame_location = Some loc; frame_raised = r; }

let rec repr_aux accu = function
| [] -> accu
| fragment :: stack ->
  let len = Array.length fragment in
  let rec append accu i =
    if i = len then accu
    else append (of_raw fragment.(i) :: accu) (succ i)
  in
  repr_aux (append accu 0) stack

let repr bt = repr_aux [] (List.rev bt)

let push stack = match get_exception_backtrace () with
| None -> []
| Some frames -> frames :: stack

(** Utilities *)

let print_frame frame =
  let raise = if frame.frame_raised then "raise" else "frame" in
  match frame.frame_location with
  | None -> Printf.sprintf "%s @ unknown" raise
  | Some loc ->
    Printf.sprintf "%s @ file \"%s\", line %d, characters %d-%d"
      raise loc.loc_filename loc.loc_line loc.loc_start loc.loc_end

(** Exception manipulation *)

let backtrace : t Exninfo.t = Exninfo.make ()

let is_recording = ref false

let record_backtrace b =
  let () = Printexc.record_backtrace b in
  is_recording := b

let get_backtrace e =
  Exninfo.get e backtrace

let add_backtrace e =
  if !is_recording then
    (** This must be the first function call, otherwise the stack may be
        destroyed *)
    let current = get_exception_backtrace () in
    let info = Exninfo.info e in
    begin match current with
    | None -> (e, info)
    | Some fragment ->
      let bt = match get_backtrace info with
      | None -> []
      | Some bt -> bt
      in
      let bt = fragment :: bt in
      (e, Exninfo.add info backtrace bt)
    end
  else
    let info = Exninfo.info e in
    (e, info)

let app_backtrace ~src ~dst =
  if !is_recording then
    match get_backtrace src with
    | None -> dst
    | Some bt ->
      match get_backtrace dst with
      | None ->
        Exninfo.add dst backtrace bt
      | Some nbt ->
        let bt = bt @ nbt in
        Exninfo.add dst backtrace bt
  else dst
