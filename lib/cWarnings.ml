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

type status =
  Disabled | Enabled | AsError

type t = {
  default : status;
  category : string;
  status : status;
}

let warnings : (string, t) Hashtbl.t = Hashtbl.create 97
let categories : (string, string list) Hashtbl.t = Hashtbl.create 97

let flags = ref ""

let get_flags () = !flags

let add_warning_in_category ~name ~category =
  let ws =
    try
      Hashtbl.find categories category
    with Not_found -> []
  in
  Hashtbl.replace categories category (name::ws)

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
  else CErrors.user_err Pp.(str "Invalid warnings flag")

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

(** [cut_before_all_rev] removes all flags subsumed by a later occurrence of the
    "all" flag, and reverses the list. *)
let rec cut_before_all_rev acc = function
  | [] -> acc
  | (status,name as w) :: warnings ->
    let acc =
      if is_all_keyword name then [w]
      else if is_none_keyword name then [(Disabled,"all")]
      else w :: acc in
    cut_before_all_rev acc warnings

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

(** [normalize_flags] removes redundant warnings. Unknown warnings are kept
    because they may be declared in a plugin that will be linked later. *)
let normalize_flags warnings =
  let warnings = cut_before_all_rev warnings in
  uniquize_flags_rev warnings

let flags_of_string s = List.map parse_flag (split_flags s)

let normalize_flags_string s =
  if is_none_keyword s then s
  else
    let flags = flags_of_string s in
    let flags = normalize_flags flags in
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
      let flags = normalize_flags flags in
      parse_warnings flags;
      string_of_flags flags
    end

let set_flags s =
  reset_default_warnings (); let s = parse_flags s in flags := s

(* Adds a warning to the [warnings] and [category] tables. We then reparse the
   warning flags string, because the warning being created might have been set
   already. *)
let create ~name ~category ?(default=Enabled) pp =
  Hashtbl.replace warnings name { default; category; status = default };
  add_warning_in_category ~name ~category;
  if default <> Disabled then
    add_warning_in_category ~name ~category:"default";
  (* We re-parse and also re-normalize the flags, because the category of the
     new warning is now known. *)
  set_flags !flags;
  fun ?loc x ->
           let w = Hashtbl.find warnings name in
           match w.status with
           | Disabled -> ()
           | AsError -> CErrors.user_err ?loc (pp x)
           | Enabled ->
              let msg =
                pp x ++ spc () ++ str "[" ++ str name ++ str "," ++
                  str category ++ str "]"
              in
              Feedback.msg_warning ?loc msg
