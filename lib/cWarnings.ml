(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util

type status =
  Disabled | Enabled | AsError

type warning =
  { wname : string;
    wparents : category list;
    pp : Pp.t
  ; default : status
  ; hybrid : bool
  (* also counts as a category *)
  ; mutable current : status
  }

and category = {
  name : string;
  parents : category list;
  warning : warning option;
}

let category_of_warning w = {
  name = w.wname;
  parents = w.wparents;
  warning = Some w;
}

(* Some values of type [category] should not be exposed as such in the interface. *)
let is_category x = match x.warning with
  | None -> true
  | Some {hybrid} -> hybrid

let graph : category String.Map.t ref = ref String.Map.empty

let revgraph : category list String.Map.t ref = ref String.Map.empty
(** Map from categories to the warnings and categories they contain, including transitively. *)

type 'a elt =
  | There of 'a
  | NotThere
  | OtherType

let get_category name =
  match String.Map.find_opt name !graph with
  | None -> NotThere
  | Some v ->
    if is_category v then There v
    else OtherType

let get_warning name =
  match String.Map.find_opt name !graph with
  | None -> NotThere
  | Some v -> match v.warning with
    | None -> OtherType
    | Some v -> There v

let warning_status w = w.current

let get_status ~name = match get_warning name with
  | There w -> warning_status w
  | NotThere | OtherType -> assert false

type _ tag = ..

type w = W : 'a tag * Quickfix.t list * 'a -> w
exception WarnError of w

module DMap = PolyMap.Make (struct type nonrec 'a tag = 'a tag = .. end)
module PrintMap = DMap.Map(struct type 'a t = 'a -> Pp.t end)

module Msg = struct
  type 'a t = {
    tag : 'a DMap.onetag;
    warning : warning;
  }
end
type 'a msg = 'a Msg.t

let printers = ref PrintMap.empty

let wrap_pp w pp =
  let open Pp in
  fun x -> pp x ++ spc () ++ str "[" ++ w.pp ++ str "]"

let register_printer { Msg.tag; warning} pp =
  let pp x = wrap_pp warning pp x in
  printers := PrintMap.add tag pp !printers

let create_msg warning () =
  let v = { Msg.tag = DMap.make(); warning; } in
  v

let print (W (tag,_, w)) =
  let pp = try PrintMap.find tag !printers with Not_found -> assert false in
  pp w

let () = CErrors.register_handler (function
    | WarnError w -> Some (print w)
    | _ -> None)

let () = Quickfix.register (function
| WarnError (W(_,qf,_)) -> qf
| _ -> [])

let warn { Msg.tag; warning } ?loc ?(quickfix=[]) v =
  let tag = DMap.tag_of_onetag tag in
  match warning_status warning with
  | Disabled -> ()
  | AsError -> Loc.raise ?loc (WarnError (W (tag,quickfix,v)))
  | Enabled -> Feedback.msg_warning ?loc ~quickfix (print (W (tag,quickfix,v)))

(** Flag handling *)

let flags = ref ""

let get_flags () = !flags

let iter_warnings f =
  !graph |> String.Map.iter (fun _ w -> Option.iter f w.warning)

let reset_default_warnings () =
  iter_warnings (fun w -> w.current <- w.default)

let set_all_warnings_status status =
  iter_warnings (fun w -> w.current <- status)

type flag =
  | All
  | Other of string

let is_none_keyword s = CString.equal s "none"

let parse_flag s =
  if String.length s > 1 then
    let status, name = match String.get s 0 with
    | '+' -> (AsError, String.sub s 1 (String.length s - 1))
    | '-' -> (Disabled, String.sub s 1 (String.length s - 1))
    | _ -> (Enabled, s)
    in
    match name with
    | "all" -> status, All
    | "none" ->
      if status = Enabled then Disabled, All
      else CErrors.user_err
          Pp.(str "Invalid warnings flag: \"none\" used with " ++ str (String.make 1 s.[0]))
    | _ -> status, Other name
  else CErrors.user_err Pp.(str "Invalid warnings flag")

let string_of_flag (status,name) =
  let name = match name with
    | All -> "all"
    | Other s -> s
  in
  match status with
  | AsError -> "+" ^ name
  | Disabled -> "-" ^ name
  | Enabled -> name

let string_of_flags flags =
  String.concat "," (List.map string_of_flag flags)

let set_status ~name status = match name with
  | All ->
    set_all_warnings_status status
  | Other name ->
    begin match String.Map.find_opt name !graph with
    | None ->
      (* unknown warning or category *)
      ()
    | Some elt ->
      let () = Option.iter (fun w -> w.current <- status) elt.warning in
      let () =
        if is_category elt then begin
          let contents = String.Map.get name !revgraph in
          List.iter (fun elt -> Option.iter (fun w -> w.current <- status) elt.warning) contents
        end
      in
      ()
    end

let split_flags s =
  let reg = Str.regexp "[ ,]+" in Str.split reg s

(** [cut_before_all_rev] removes all flags subsumed by a later occurrence of the
    "all" flag, and reverses the list. *)
let rec cut_before_all_rev acc = function
  | [] -> acc
  | (_, All as w) :: warnings -> cut_before_all_rev [w] warnings
  | w :: warnings -> cut_before_all_rev (w::acc) warnings

let cut_before_all_rev warnings = cut_before_all_rev [] warnings

(** [uniquize_flags_rev] removes flags that are subsumed by later occurrences of
    themselves or their categories, and reverses the list. *)
let uniquize_flags_rev flags =
  let rec aux acc visited = function
    | (_, All as flag) :: flags ->
      assert (List.is_empty flags);
      flag :: acc

    | (_,Other name as flag)::flags ->
      if CString.Set.mem name visited then aux acc visited flags else
        let visited =
          match String.Map.find_opt name !revgraph with
          | Some contents ->
            List.fold_left (fun v w ->
                CString.Set.add w.name v)
              visited contents
          | None ->
            (* Maybe a known non-category warning, maybe an unknown warning or category *)
            visited
        in
        aux (flag::acc) (CString.Set.add name visited) flags
    | [] -> acc
  in
  aux [] CString.Set.empty flags

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

(* Remark: [warn] does not need to start with a comma, but if present
   it won't hurt (",," is normalized into ","). *)
let with_warn warn (f:'b -> 'a) x =
  let s = get_flags () in
  Util.try_finally (fun x -> set_flags (s^","^warn);f x) x set_flags s

let is_used_name name =
  String.equal name "none" ||
  String.Map.mem name !graph

let check_fresh_name name =
  if is_used_name name then
    CErrors.anomaly Pp.(str "Already used warning name " ++ str name ++ str ".")

let rec add_in_categories_rec v visited {name; parents} =
  if String.Set.mem name visited then visited
  else
    let visited = String.Set.add name visited in
    revgraph := String.Map.update name (function
        | None -> assert false
        | Some l -> Some (v :: l))
        !revgraph;
    List.fold_left (add_in_categories_rec v) visited parents

let add_in_categories v cats =
  let _ : String.Set.t =
    List.fold_left (add_in_categories_rec v) String.Set.empty cats
  in
  ()

let check_cat_list cats =
  assert (not (List.is_empty cats));
  assert (not (List.exists (fun cat -> String.equal cat.name "default") cats))

(* We could re-normalize flags but it only matters if a warning will
   be added to the new category so we just normalize at that time. *)
let create_category ~from ~name () =
  let v = {
    name = name;
    parents = from;
    warning = None;
  }
  in
  graph := String.Map.add name v !graph;
  revgraph := String.Map.add name []  !revgraph;
  add_in_categories v from;
  v

let all = create_category ~from:[] ~name:"all" ()

let default_cat = create_category ~from:[all] ~name:"default" ()

let create_category ?(from=[all]) ~name () =
  check_fresh_name name;
  check_cat_list from;
  create_category ~from ~name ()

let add_pp name pp =
  let open Pp in
  if ismt pp then str name
  else str name ++ str "," ++ pp

let rec make_cat_pp visited suffix cat =
  let name = cat.name in
  if String.Set.mem name visited then visited, suffix
  else
    let visited = String.Set.add name visited in
    if String.equal cat.name "all" then
      visited, suffix
    else
      let visited, pp = make_cats_pp visited suffix cat.parents in
      visited, add_pp name pp

and make_cats_pp visited suffix cats =
  List.fold_left (fun (visited,pp) cat -> make_cat_pp visited pp cat)
    (visited, suffix)
    cats

let make_warning_pp ~from name =
  let _, pp = make_cats_pp String.Set.empty (Pp.mt()) from in
  add_pp name pp

(* Adds a warning to the [warnings] and [categories] tables. We then reparse the
   warning flags string, because the warning being created might have been set
   already. *)
let create_gen ?(from=[all]) ?(default=Enabled) ~name ~hybrid () =
  check_fresh_name name;
  check_cat_list from;
  let from = if default <> Disabled then default_cat :: from else from in
  let pp = make_warning_pp ~from name in
  let w = {
    wname = name;
    default = default;
    wparents = from;
    current = default;
    hybrid;
    pp;
  }
  in
  let elt = category_of_warning w in
  let () = graph := String.Map.add name elt !graph in
  let () = if hybrid then revgraph := String.Map.add name [] !revgraph in
  add_in_categories elt from;
  (* We re-parse and also re-normalize the flags, because the category of the
     new warning is now known. *)
  set_flags !flags;
  elt, w

let create_warning ?from ?default ~name () =
  let _, w = create_gen ?from ?default ~name ~hybrid:false () in
  w

let create_hybrid ?from ?default ~name () =
  create_gen ?from ?default ~name ~hybrid:true ()

let create_in w pp =
  let msg = create_msg w () in
  let () = register_printer msg pp in
  fun ?loc ?quickfix x -> warn ?loc ?quickfix msg x

let create_with_quickfix ~name ?category ?default pp =
  let from = Option.map (fun x -> [x]) category in
  let w = create_warning ?from ?default ~name () in
  create_in w pp

let create ~name ?category ?default pp =
  let f = create_with_quickfix ~name ?category ?default pp in
  fun ?loc x -> f ?quickfix:None ?loc x

let warn_unknown_warnings = create ~name:"unknown-warning" Pp.(fun flags ->
    str "Could not enable unknown " ++
    str (CString.plural (List.length flags) "warning") ++ spc() ++
    prlist_with_sep spc str flags)

let override_unknown_warning = ref false

let warn_unknown_warnings ?loc flags =
  if not !override_unknown_warning then warn_unknown_warnings ?loc flags

let check_unknown_warnings flags =
  let flags = flags_of_string flags in
  let flags = List.filter_map (function
      | Disabled, _ | _, All -> None
      | (Enabled|AsError), Other name ->
        if String.Map.mem name !graph then None
        else Some name)
      flags
  in
  if not (List.is_empty flags) then
    warn_unknown_warnings flags

module CoreCategories = struct

  let make name = create_category ~name ()

  (* Update the list of core categories in
     doc/sphinx/proof-engine/vernacular-commands.rst
     when adding a new category here. *)

  let automation = make "automation"
  let bytecode_compiler = make "bytecode-compiler"
  let coercions = make "coercions"
  let deprecated = make "deprecated"
  let extraction = make "extraction"
  let filesystem = make "filesystem"
  let fixpoints = make "fixpoints"
  let fragile = make "fragile"
  let funind = make "funind"
  let implicits = make "implicits"
  let ltac = make "ltac"
  let ltac2 = make "ltac2"
  let native_compiler = make "native-compiler"
  let numbers = make "numbers"
  let parsing = make "parsing"
  let pedantic = make "pedantic"
  let records = make "records"
  let rewrite_rules = make "rewrite-rules"
  let ssr = make "ssr"
  let syntax = make "syntax"
  let tactics = make "tactics"
  let user_warn = make "user-warn"
  let vernacular = make "vernacular"

end
