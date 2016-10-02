(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp

type status =
  Disabled | Enabled | AsError

type t = {
  default : status;
  category : string;
  status : status;
}

let warnings : (string, t) Hashtbl.t = Hashtbl.create 97
let categories : (string, string list) Hashtbl.t = Hashtbl.create 97

let current_loc = ref Loc.ghost
let flags = ref "default"

let set_current_loc = (:=) current_loc

let get_flags () = !flags

let add_warning_in_category ~name ~category =
  let ws =
    try
      Hashtbl.find categories category
    with Not_found -> []
  in
  Hashtbl.replace categories category (name::ws)

let create ~name ~category ?(default=Enabled) pp =
  Hashtbl.add warnings name { default; category; status = default };
  add_warning_in_category ~name ~category;
  if default <> Disabled then
    add_warning_in_category ~name ~category:"default";
  fun ?loc x -> let w = Hashtbl.find warnings name in
           match w.status with
           | Disabled -> ()
           | AsError ->
              let loc = Option.default !current_loc loc in
              CErrors.user_err ~loc (pp x)
           | Enabled ->
              let msg =
                pp x ++ spc () ++ str "[" ++ str name ++ str "," ++
                  str category ++ str "]"
              in
              let loc = Option.default !current_loc loc in
              Feedback.msg_warning ~loc msg

let warn_unknown_warning =
  create ~name:"unknown-warning" ~category:"toplevel"
         (fun name -> strbrk "Unknown warning name: " ++ str name)

let set_warning_status ~name status =
  try
    let w = Hashtbl.find warnings name in 
    Hashtbl.replace warnings name { w with status = status }
  with Not_found -> warn_unknown_warning name

let reset_default_warnings () =
  Hashtbl.iter (fun name w ->
                Hashtbl.replace warnings name { w with status = w.default })
    warnings

let set_all_warnings_status status =
  Hashtbl.iter (fun name w ->
                Hashtbl.replace warnings name { w with status })
    warnings

let parse_flag s =
  if String.length s > 1 then
    match String.get s 0 with
    | '+' -> (AsError, String.sub s 1 (String.length s - 1))
    | '-' -> (Disabled, String.sub s 1 (String.length s - 1))
    | _ -> (Enabled, s)
  else CErrors.error "Invalid warnings flag"

let rec do_all_keyword = function
  | [] -> []
  | (status, name as item) :: items -> 
     if CString.equal name "all" then
       (set_all_warnings_status status; do_all_keyword items)
     else item :: do_all_keyword items

let rec do_categories = function
  | [] -> []
  | (status, name as item) :: items -> 
     try
       let names = Hashtbl.find categories name in
       List.iter (fun name -> set_warning_status name status) names;
       do_categories items
     with Not_found -> item :: do_categories items

let rec parse_warnings items =
  List.iter (fun (status, name) -> set_warning_status ~name status) items

(* For compatibility, we accept "none" *)
let parse_flags s = 
  if CString.equal s "none" then begin
      Flags.make_warn false;
      set_all_warnings_status Disabled
    end
  else begin
      Flags.make_warn true;
      let reg = Str.regexp "[ ,]+" in
      let items = List.map parse_flag (Str.split reg s) in
      let items = do_all_keyword items in
      let items = do_categories items in
      parse_warnings items
    end

let set_flags s =
  flags := s; reset_default_warnings (); parse_flags s
