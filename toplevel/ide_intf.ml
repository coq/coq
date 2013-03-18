(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Protocol version of this file. This is the date of the last modification. *)

(** WARNING: TO BE UPDATED WHEN MODIFIED! *)

let protocol_version = "20120710"

(** * Interface of calls to Coq by CoqIde *)

open Xml_parser
open Interface

type xml = Xml_parser.xml

(** We use phantom types and GADT to protect ourselves against wild casts *)

type 'a call =
  | Interp of raw * verbose * string
  | Rewind of int
  | Goal
  | Evars
  | Hints
  | Status
  | Search of search_flags
  | GetOptions
  | SetOptions of (option_name * option_value) list
  | InLoadPath of string
  | MkCases of string
  | Quit
  | About

(** The structure that coqtop should implement *)

type handler = {
  interp : raw * verbose * string -> string;
  rewind : int -> int;
  goals : unit -> goals option;
  evars : unit -> evar list option;
  hints : unit -> (hint list * hint) option;
  status : unit -> status;
  search : search_flags -> string coq_object list;
  get_options : unit -> (option_name * option_state) list;
  set_options : (option_name * option_value) list -> unit;
  inloadpath : string -> bool;
  mkcases : string -> string list list;
  quit : unit -> unit;
  about : unit -> coq_info;
  handle_exn : exn -> location * string;
}

(** The actual calls *)

let interp (r,b,s) : string call = Interp (r,b,s)
let rewind i : int call = Rewind i
let goals : goals option call = Goal
let evars : evar list option call = Evars
let hints : (hint list * hint) option call = Hints
let status : status call = Status
let search flags : string coq_object list call = Search flags
let get_options : (option_name * option_state) list call = GetOptions
let set_options l : unit call = SetOptions l
let inloadpath s : bool call = InLoadPath s
let mkcases s : string list list call = MkCases s
let quit : unit call = Quit

(** * Coq answers to CoqIde *)

let abstract_eval_call handler c =
  try
    let res = match c with
      | Interp (r,b,s) -> Obj.magic (handler.interp (r,b,s) : string)
      | Rewind i -> Obj.magic (handler.rewind i : int)
      | Goal -> Obj.magic (handler.goals () : goals option)
      | Evars -> Obj.magic (handler.evars () : evar list option)
      | Hints -> Obj.magic (handler.hints () : (hint list * hint) option)
      | Status -> Obj.magic (handler.status () : status)
      | Search flags -> Obj.magic (handler.search flags : string coq_object list)
      | GetOptions -> Obj.magic (handler.get_options () : (option_name * option_state) list)
      | SetOptions opts -> Obj.magic (handler.set_options opts : unit)
      | InLoadPath s -> Obj.magic (handler.inloadpath s : bool)
      | MkCases s -> Obj.magic (handler.mkcases s : string list list)
      | Quit -> Obj.magic (handler.quit () : unit)
      | About -> Obj.magic (handler.about () : coq_info)
    in Good res
  with any ->
    let (l, str) = handler.handle_exn any in
    Fail (l,str)

(** * XML data marshalling *)

exception Marshal_error

(** Utility functions *)

let massoc x l =
  try List.assoc x l
  with Not_found -> raise Marshal_error

let constructor t c args = Element (t, ["val", c], args)

let do_match constr t mf = match constr with
| Element (s, attrs, args) ->
  if s = t then
    let c = massoc "val" attrs in
    mf c args
  else raise Marshal_error
| _ -> raise Marshal_error

let pcdata = function
| PCData s -> s
| _ -> raise Marshal_error

let singleton = function
| [x] -> x
| _ -> raise Marshal_error

let raw_string = function
| [] -> ""
| [PCData s] -> s
| _ -> raise Marshal_error

let bool_arg tag b = if b then [tag, ""] else []

(** Base types *)

let of_unit () = Element ("unit", [], [])

let to_unit = function
  | Element ("unit", [], []) -> ()
  | _ -> raise Marshal_error

let of_bool b =
  if b then constructor "bool" "true" []
  else constructor "bool" "false" []

let to_bool xml = do_match xml "bool"
  (fun s _ -> match s with
  | "true" -> true
  | "false" -> false
  | _ -> raise Marshal_error)

let of_list f l =
  Element ("list", [], List.map f l)

let to_list f = function
| Element ("list", [], l) ->
  List.map f l
| _ -> raise Marshal_error

let of_option f = function
| None -> Element ("option", ["val", "none"], [])
| Some x -> Element ("option", ["val", "some"], [f x])

let to_option f = function
| Element ("option", ["val", "none"], []) -> None
| Element ("option", ["val", "some"], [x]) -> Some (f x)
| _ -> raise Marshal_error

let of_string s = Element ("string", [], [PCData s])

let to_string = function
| Element ("string", [], l) -> raw_string l
| _ -> raise Marshal_error

let of_int i = Element ("int", [], [PCData (string_of_int i)])

let to_int = function
| Element ("int", [], [PCData s]) ->
  (try int_of_string s with Failure _ -> raise Marshal_error)
| _ -> raise Marshal_error

let of_pair f g (x, y) = Element ("pair", [], [f x; g y])

let to_pair f g = function
| Element ("pair", [], [x; y]) -> (f x, g y)
| _ -> raise Marshal_error

(** More elaborate types *)

let of_option_value = function
| IntValue i ->
  constructor "option_value" "intvalue" [of_option of_int i]
| BoolValue b ->
  constructor "option_value" "boolvalue" [of_bool b]
| StringValue s ->
  constructor "option_value" "stringvalue" [of_string s]

let to_option_value xml = do_match xml "option_value"
  (fun s args -> match s with
  | "intvalue" -> IntValue (to_option to_int (singleton args))
  | "boolvalue" -> BoolValue (to_bool (singleton args))
  | "stringvalue" -> StringValue (to_string (singleton args))
  | _ -> raise Marshal_error
  )

let of_option_state s =
  Element ("option_state", [], [
    of_bool s.opt_sync;
    of_bool s.opt_depr;
    of_string s.opt_name;
    of_option_value s.opt_value]
  )

let to_option_state = function
| Element ("option_state", [], [sync; depr; name; value]) ->
  {
    opt_sync = to_bool sync;
    opt_depr = to_bool depr;
    opt_name = to_string name;
    opt_value = to_option_value value;
  }
| _ -> raise Marshal_error

let of_search_constraint = function
| Name_Pattern s ->
  constructor "search_constraint" "name_pattern" [of_string s]
| Type_Pattern s ->
  constructor "search_constraint" "type_pattern" [of_string s]
| SubType_Pattern s ->
  constructor "search_constraint" "subtype_pattern" [of_string s]
| In_Module m ->
  constructor "search_constraint" "in_module" [of_list of_string m]
| Include_Blacklist ->
  constructor "search_constraint" "include_blacklist" []

let to_search_constraint xml = do_match xml "search_constraint"
  (fun s args -> match s with
  | "name_pattern" -> Name_Pattern (to_string (singleton args))
  | "type_pattern" -> Type_Pattern (to_string (singleton args))
  | "subtype_pattern" -> SubType_Pattern (to_string (singleton args))
  | "in_module" -> In_Module (to_list to_string (singleton args))
  | "include_blacklist" -> Include_Blacklist
  | _ -> raise Marshal_error)

let of_coq_object f ans =
  let prefix = of_list of_string ans.coq_object_prefix in
  let qualid = of_list of_string ans.coq_object_qualid in
  let obj = f ans.coq_object_object in
  Element ("coq_object", [], [prefix; qualid; obj])

let to_coq_object f = function
| Element ("coq_object", [], [prefix; qualid; obj]) ->
  let prefix = to_list to_string prefix in
  let qualid = to_list to_string qualid in
  let obj = f obj in {
    coq_object_prefix = prefix;
    coq_object_qualid = qualid;
    coq_object_object = obj;
  }
| _ -> raise Marshal_error

let of_value f = function
| Good x -> Element ("value", ["val", "good"], [f x])
| Fail (loc, msg) ->
  let loc = match loc with
  | None -> []
  | Some (s, e) -> [("loc_s", string_of_int s); ("loc_e", string_of_int e)]
  in
  Element ("value", ["val", "fail"] @ loc, [PCData msg])

let to_value f = function
| Element ("value", attrs, l) ->
  let ans = massoc "val" attrs in
  if ans = "good" then Good (f (singleton l))
  else if ans = "fail" then
    let loc =
      try
        let loc_s = int_of_string (List.assoc "loc_s" attrs) in
        let loc_e = int_of_string (List.assoc "loc_e" attrs) in
        Some (loc_s, loc_e)
      with e when e <> Sys.Break -> None
    in
    let msg = raw_string l in
    Fail (loc, msg)
  else raise Marshal_error
| _ -> raise Marshal_error

let of_call = function
| Interp (raw, vrb, cmd) ->
  let flags = (bool_arg "raw" raw) @ (bool_arg "verbose" vrb) in
  Element ("call", ("val", "interp") :: flags, [PCData cmd])
| Rewind n ->
  Element ("call", ("val", "rewind") :: ["steps", string_of_int n], [])
| Goal ->
  Element ("call", ["val", "goal"], [])
| Evars ->
  Element ("call", ["val", "evars"], [])
| Hints ->
  Element ("call", ["val", "hints"], [])
| Status ->
  Element ("call", ["val", "status"], [])
| Search flags ->
  let args = List.map (of_pair of_search_constraint of_bool) flags in
  Element ("call", ["val", "search"], args)
| GetOptions ->
  Element ("call", ["val", "getoptions"], [])
| SetOptions opts ->
  let args = List.map (of_pair (of_list of_string) of_option_value) opts in
  Element ("call", ["val", "setoptions"], args)
| InLoadPath file ->
  Element ("call", ["val", "inloadpath"], [PCData file])
| MkCases ind ->
  Element ("call", ["val", "mkcases"], [PCData ind])
| Quit ->
  Element ("call", ["val", "quit"], [])
| About ->
  Element ("call", ["val", "about"], [])

let to_call = function
| Element ("call", attrs, l) ->
  let ans = massoc "val" attrs in
  begin match ans with
  | "interp" ->
    let raw = List.mem_assoc "raw" attrs in
    let vrb = List.mem_assoc "verbose" attrs in
    Interp (raw, vrb, raw_string l)
  | "rewind" ->
    let steps = int_of_string (massoc "steps" attrs) in
    Rewind steps
  | "goal" -> Goal
  | "evars" -> Evars
  | "status" -> Status
  | "search" ->
    let args = List.map (to_pair to_search_constraint to_bool) l in
    Search args
  | "getoptions" -> GetOptions
  | "setoptions" ->
    let args = List.map (to_pair (to_list to_string) to_option_value) l in
    SetOptions args
  | "inloadpath" -> InLoadPath (raw_string l)
  | "mkcases" -> MkCases (raw_string l)
  | "hints" -> Hints
  | "quit" -> Quit
  | "about" -> About
  | _ -> raise Marshal_error
  end
| _ -> raise Marshal_error

let of_status s =
  let of_so = of_option of_string in
  let of_sl = of_list of_string in
  Element ("status", [],
    [
      of_sl s.status_path;
      of_so s.status_proofname;
      of_sl s.status_allproofs;
      of_int s.status_statenum;
      of_int s.status_proofnum;
    ]
  )

let to_status = function
| Element ("status", [], [path; name; prfs; snum; pnum]) ->
  {
    status_path = to_list to_string path;
    status_proofname = to_option to_string name;
    status_allproofs = to_list to_string prfs;
    status_statenum = to_int snum;
    status_proofnum = to_int pnum;
  }
| _ -> raise Marshal_error

let of_evar s =
  Element ("evar", [], [PCData s.evar_info])

let to_evar = function
| Element ("evar", [], data) -> { evar_info = raw_string data; }
| _ -> raise Marshal_error

let of_goal g =
  let hyp = of_list of_string g.goal_hyp in
  let ccl = of_string g.goal_ccl in
  let id = of_string g.goal_id in
  Element ("goal", [], [id; hyp; ccl])

let to_goal = function
| Element ("goal", [], [id; hyp; ccl]) ->
  let hyp = to_list to_string hyp in
  let ccl = to_string ccl in
  let id = to_string id in
  { goal_hyp = hyp; goal_ccl = ccl; goal_id = id; }
| _ -> raise Marshal_error

let of_goals g =
  let of_glist = of_list of_goal in
  let fg = of_list of_goal g.fg_goals in
  let bg = of_list (of_pair of_glist of_glist) g.bg_goals in
  Element ("goals", [], [fg; bg])

let to_goals = function
| Element ("goals", [], [fg; bg]) ->
  let to_glist = to_list to_goal in
  let fg = to_list to_goal fg in
  let bg = to_list (to_pair to_glist to_glist) bg in
  { fg_goals = fg; bg_goals = bg; }
| _ -> raise Marshal_error

let of_coq_info info =
  let version = of_string info.coqtop_version in
  let protocol = of_string info.protocol_version in
  let release = of_string info.release_date in
  let compile = of_string info.compile_date in
  Element ("coq_info", [], [version; protocol; release; compile])

let to_coq_info = function
| Element ("coq_info", [], [version; protocol; release; compile]) ->
  {
    coqtop_version = to_string version;
    protocol_version = to_string protocol;
    release_date = to_string release;
    compile_date = to_string compile;
  }
| _ -> raise Marshal_error

(** Conversions between ['a value] and xml answers

  When decoding an xml answer, we dynamically check that it is compatible
  with the original call. For that we now rely on the fact that all
  sub-fonctions [to_xxx : xml -> xxx] check that the current xml element
  is "xxx", and raise [Marshal_error] if anything goes wrong.
*)

type value_type =
  | Unit | String | Int | Bool | Goals | Evar | State | Option_state | Coq_info
  | Option of value_type
  | List of value_type
  | Coq_object of value_type
  | Pair of value_type * value_type

let hint = List (Pair (String, String))
let option_name = List String

let expected_answer_type = function
  | Interp _ -> String
  | Rewind _ -> Int
  | Goal -> Option Goals
  | Evars -> Option (List Evar)
  | Hints -> Option (Pair (List hint, hint))
  | Status -> State
  | Search _ -> List (Coq_object String)
  | GetOptions -> List (Pair (option_name, Option_state))
  | SetOptions _ -> Unit
  | InLoadPath _ -> Bool
  | MkCases _ -> List (List String)
  | Quit -> Unit
  | About -> Coq_info

let of_answer (q : 'a call) (r : 'a value) : xml =
  let rec convert ty : 'a -> xml = match ty with
    | Unit -> Obj.magic of_unit
    | Bool -> Obj.magic of_bool
    | String -> Obj.magic of_string
    | Int -> Obj.magic of_int
    | State -> Obj.magic of_status
    | Option_state -> Obj.magic of_option_state
    | Coq_info -> Obj.magic of_coq_info
    | Goals -> Obj.magic of_goals
    | Evar -> Obj.magic of_evar
    | List t -> Obj.magic (of_list (convert t))
    | Option t -> Obj.magic (of_option (convert t))
    | Coq_object t -> Obj.magic (of_coq_object (convert t))
    | Pair (t1,t2) -> Obj.magic (of_pair (convert t1) (convert t2))
  in
  of_value (convert (expected_answer_type q)) r

let to_answer xml (c : 'a call) : 'a value =
  let rec convert ty : xml -> 'a = match ty with
    | Unit -> Obj.magic to_unit
    | Bool -> Obj.magic to_bool
    | String -> Obj.magic to_string
    | Int -> Obj.magic to_int
    | State -> Obj.magic to_status
    | Option_state -> Obj.magic to_option_state
    | Coq_info -> Obj.magic to_coq_info
    | Goals -> Obj.magic to_goals
    | Evar -> Obj.magic to_evar
    | List t -> Obj.magic (to_list (convert t))
    | Option t -> Obj.magic (to_option (convert t))
    | Coq_object t -> Obj.magic (to_coq_object (convert t))
    | Pair (t1,t2) -> Obj.magic (to_pair (convert t1) (convert t2))
  in
  to_value (convert (expected_answer_type c)) xml

(** * Debug printing *)

let pr_option_value = function
| IntValue None -> "none"
| IntValue (Some i) -> string_of_int i
| StringValue s -> s
| BoolValue b -> if b then "true" else "false"

let rec pr_setoptions opts =
  let map (key, v) =
    let key = String.concat " " key in
    key ^ " := " ^ (pr_option_value v)
  in
  String.concat "; " (List.map map opts)

let pr_getoptions opts =
  let map (key, s) =
    let key = String.concat " " key in
    Printf.sprintf "%s: sync := %b; depr := %b; name := %s; value := %s\n"
      key s.opt_sync s.opt_depr s.opt_name (pr_option_value s.opt_value)
  in
  "\n" ^ String.concat "" (List.map map opts)

let pr_call = function
  | Interp (r,b,s) ->
    let raw = if r then "RAW" else "" in
    let verb = if b then "" else "SILENT" in
    "INTERP"^raw^verb^" ["^s^"]"
  | Rewind i -> "REWIND "^(string_of_int i)
  | Goal -> "GOALS"
  | Evars -> "EVARS"
  | Hints -> "HINTS"
  | Status -> "STATUS"
  | Search _ -> "SEARCH"
  | GetOptions -> "GETOPTIONS"
  | SetOptions l -> "SETOPTIONS" ^ " [" ^ pr_setoptions l ^ "]"
  | InLoadPath s -> "INLOADPATH "^s
  | MkCases s -> "MKCASES "^s
  | Quit -> "QUIT"
  | About -> "ABOUT"

let pr_value_gen pr = function
  | Good v -> "GOOD " ^ pr v
  | Fail (_,str) -> "FAIL ["^str^"]"

let pr_value v = pr_value_gen (fun _ -> "") v

let pr_string s = "["^s^"]"
let pr_bool b = if b then "true" else "false"

let pr_status s =
  let path =
    let l = String.concat "." s.status_path in
    "path=" ^ l ^ ";"
  in
  let name = match s.status_proofname with
  | None -> "no proof;"
  | Some n -> "proof = " ^ n ^ ";"
  in
  "Status: " ^ path ^ name

let pr_mkcases l =
  let l = List.map (String.concat " ") l in
  "[" ^ String.concat " | " l ^ "]"

let pr_goals_aux g =
  if g.fg_goals = [] then
    if g.bg_goals = [] then "Proof completed."
    else
      let rec pr_focus _ = function
      | [] -> assert false
      | [lg, rg] -> Printf.sprintf "%i" (List.length lg + List.length rg)
      | (lg, rg) :: l ->
        Printf.sprintf "%i:%a" (List.length lg + List.length rg) pr_focus l
      in
      Printf.sprintf "Still focussed: [%a]." pr_focus g.bg_goals
  else
    let pr_menu s = s in
    let pr_goal { goal_hyp = hyps; goal_ccl = goal } =
      "[" ^ String.concat "; " (List.map pr_menu hyps) ^ " |- " ^ pr_menu goal ^ "]"
    in
    String.concat " " (List.map pr_goal g.fg_goals)

let pr_goals = function
| None -> "No proof in progress."
| Some g -> pr_goals_aux g

let pr_evar ev = "[" ^ ev.evar_info ^ "]"

let pr_evars = function
| None -> "No proof in progress."
| Some evars -> String.concat " " (List.map pr_evar evars)

let pr_full_value call value =
  match call with
    | Interp _ -> pr_value_gen pr_string (Obj.magic value : string value)
    | Rewind i -> pr_value_gen string_of_int (Obj.magic value : int value)
    | Goal -> pr_value_gen pr_goals (Obj.magic value : goals option value)
    | Evars -> pr_value_gen pr_evars (Obj.magic value : evar list option value)
    | Hints -> pr_value value
    | Status -> pr_value_gen pr_status (Obj.magic value : status value)
    | Search _ -> pr_value value
    | GetOptions -> pr_value_gen pr_getoptions (Obj.magic value : (option_name * option_state) list value)
    | SetOptions _ -> pr_value value
    | InLoadPath s -> pr_value_gen pr_bool (Obj.magic value : bool value)
    | MkCases s -> pr_value_gen pr_mkcases (Obj.magic value : string list list value)
    | Quit -> pr_value value
    | About -> pr_value value

