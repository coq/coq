(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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

type t = frame list

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

let push stack = match get_exception_backtrace () with
| None -> []
| Some frames ->
  let len = Array.length frames in
  let rec append accu i =
    if i = len then accu
    else append (of_raw frames.(i) :: accu) (succ i)
  in
  append stack 0

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
    let current = get_exception_backtrace () in
    begin match current with
    | None -> e
    | Some frames ->
      let len = Array.length frames in
      let rec append accu i =
        if i = len then accu
        else append (of_raw frames.(i) :: accu) (succ i)
      in
      let old = match get_backtrace e with
      | None -> []
      | Some bt -> bt
      in
      let bt = append old 0 in
      Exninfo.add e backtrace bt
    end
  else e
