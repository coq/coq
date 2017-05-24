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

let current_loc = ref None
let flags = ref ""

let set_current_loc loc = current_loc := loc

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
  fun ?loc x ->
           let w = Hashtbl.find warnings name in
           let loc = Option.append loc !current_loc in
           match w.status with
           | Disabled -> ()
           | AsError -> CErrors.user_err ?loc (pp x)
           | Enabled ->
              let msg =
                pp x ++ spc () ++ str "[" ++ str name ++ str "," ++
                  str category ++ str "]"
              in
              Feedback.msg_warning ?loc msg

let warn_unknown_warning =
  create ~name:"unknown-warning" ~category:"toplevel"
         (fun name -> strbrk "Unknown warning name: " ++ str name)

let set_warning_status ~name status =
  try
    let w = Hashtbl.find warnings name in 
    Hashtbl.replace warnings name { w with status = status }
  with Not_found -> ()

let reset_default_warnings () =
  Hashtbl.iter (fun name w ->
                Hashtbl.replace warnings name { w with status = w.default })
    warnings

let set_all_warnings_status status =
  Hashtbl.iter (fun name w ->
                Hashtbl.replace warnings name { w with status })
    warnings

let set_category_status ~name status =
  let names = Hashtbl.find categories name in
  List.iter (fun name -> set_warning_status ~name status) names

let is_all_keyword name = CString.equal name "all"
let is_none_keyword s = CString.equal s "none"

let parse_flag s =
  if String.length s > 1 then
    match String.get s 0 with
    | '+' -> (AsError, String.sub s 1 (String.length s - 1))
    | '-' -> (Disabled, String.sub s 1 (String.length s - 1))
    | _ -> (Enabled, s)
  else CErrors.error "Invalid warnings flag"

let string_of_flag (status,name) =
  match status with
  | AsError -> "+" ^ name
  | Disabled -> "-" ^ name
  | Enabled -> name

let string_of_flags flags =
  String.concat "," (List.map string_of_flag flags)

let set_status ~name status =
  if is_all_keyword name then
    set_all_warnings_status status
  else
    try
      set_category_status ~name status
    with Not_found ->
         try
           set_warning_status ~name status
         with Not_found -> ()

let split_flags s =
  let reg = Str.regexp "[ ,]+" in Str.split reg s

let check_warning ~silent (_status,name) =
  is_all_keyword name ||
  Hashtbl.mem categories name ||
  Hashtbl.mem warnings name ||
  (if not silent then warn_unknown_warning name; false)

(** [cut_before_all_rev] removes all flags subsumed by a later occurrence of the
    "all" flag, and reverses the list. *)
let rec cut_before_all_rev acc = function
  | [] -> acc
  | (_status,name as w) :: warnings ->
     cut_before_all_rev (w :: if is_all_keyword name then [] else acc) warnings

let cut_before_all_rev warnings = cut_before_all_rev [] warnings

(** [uniquize_flags_rev] removes flags that are subsumed by later occurrences of
    themselves or their categories, and reverses the list. *)
let uniquize_flags_rev flags =
  let rec aux acc visited = function
    | (_,name as flag)::flags ->
       if CString.Set.mem name visited then aux acc visited flags else
         let visited =
           try
             let warnings = Hashtbl.find categories name in
             List.fold_left (fun v w -> CString.Set.add w v) visited warnings
           with Not_found ->
             visited
         in
         aux (flag::acc) (CString.Set.add name visited) flags
    | [] -> acc
  in aux [] CString.Set.empty flags

(** [normalize_flags] removes unknown or redundant warnings. If [silent] is
    true, it emits a warning when an unknown warning is met. *)
let normalize_flags ~silent warnings =
  let warnings = List.filter (check_warning ~silent) warnings in
  let warnings = cut_before_all_rev warnings in
  uniquize_flags_rev warnings

let flags_of_string s = List.map parse_flag (split_flags s)

let normalize_flags_string s =
  if is_none_keyword s then s
  else
    let flags = flags_of_string s in
    let flags = normalize_flags ~silent:false flags in
    string_of_flags flags

let parse_warnings items =
  CList.iter (fun (status, name) -> set_status ~name status) items

(* For compatibility, we accept "none" *)
let parse_flags s =
  if is_none_keyword s then begin
      Flags.make_warn false;
      set_all_warnings_status Disabled;
      "none"
    end
  else begin
      Flags.make_warn true;
      let flags = flags_of_string s in
      let flags = normalize_flags ~silent:true flags in
      parse_warnings flags;
      string_of_flags flags
    end

let set_flags s =
  reset_default_warnings (); let s = parse_flags s in flags := s
