(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type status =
  Disabled | Enabled | AsError

type state = {
  default : status;
  category : string;
  status : status;
}

type _ tag = ..

type w = W : 'a tag * 'a -> w
exception WarnError of w

module DMap = PolyMap.Make (struct type nonrec 'a tag = 'a tag = .. end)
module PrintMap = DMap.Map(struct type 'a t = 'a -> Pp.t end)
module RevMap = DMap.Map(struct type 'a t = string end)

type 'a t = 'a DMap.onetag

let printers = ref PrintMap.empty
let revmap = ref RevMap.empty

let print (W (tag, w)) =
  let pp = try PrintMap.find tag !printers with Not_found -> assert false in
  pp w

let () = CErrors.register_handler (function
    | WarnError w -> Some (print w)
    | _ -> None)

let warnings : (string, state) Hashtbl.t = Hashtbl.create 97
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
let create_gen ~name ~category ?(default=Enabled) () =
  let tag = DMap.make () in
  revmap := RevMap.add tag name !revmap;
  Hashtbl.replace warnings name { default; category; status = default };
  add_warning_in_category ~name ~category;
  if default <> Disabled then
    add_warning_in_category ~name ~category:"default";
  (* We re-parse and also re-normalize the flags, because the category of the
     new warning is now known. *)
  set_flags !flags;
  tag

let wrap_pp ~name ~category pp =
  let open Pp in
  fun x ->
    pp x ++ spc () ++ str "[" ++ str name ++ str "," ++
    str category ++ str "]"

let warn ?loc tag v =
  let tag = DMap.tag_of_onetag tag in
  let w = Hashtbl.find warnings (RevMap.find tag !revmap) in
  match w.status with
  | Disabled -> ()
  | AsError -> Loc.raise ?loc (WarnError (W (tag, v)))
  | Enabled -> Feedback.msg_warning ?loc (print (W (tag, v)))

let register_printer tag pp =
  let name = RevMap.find (DMap.tag_of_onetag tag) !revmap in
  let {category} = Hashtbl.find warnings name in
  let pp x = wrap_pp ~name ~category pp x in
  printers := PrintMap.add tag pp !printers

let create ~name ~category ?default pp =
  let tag = create_gen ~name ~category ?default () in
  register_printer tag pp;
  fun ?loc x -> warn ?loc tag x

let get_status ~name = (Hashtbl.find warnings name).status

(* Remark: [warn] does not need to start with a comma, but if present
   it won't hurt (",," is normalized into ","). *)
let with_warn warn (f:'b -> 'a) x =
  let s = get_flags () in
  Util.try_finally (fun x -> set_flags (s^","^warn);f x) x set_flags s
