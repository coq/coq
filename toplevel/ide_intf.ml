(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Interface of calls to Coq by CoqIde *)

open Xml_parser
open Interface

type xml = Xml_parser.xml

(** We use phantom types and GADT to protect ourselves against wild casts *)

type 'a call =
  | Interp of raw * verbose * string
  | Rewind of int
  | Goal
  | Hints
  | Status
  | GetOptions
  | SetOptions of (option_name * option_value) list
  | InLoadPath of string
  | MkCases of string

(** The actual calls *)

let interp (r,b,s) : string call = Interp (r,b,s)
let rewind i : int call = Rewind i
let goals : goals call = Goal
let hints : (hint list * hint) option call = Hints
let status : status call = Status
let get_options : (option_name * option_state) list call = GetOptions
let set_options l : unit call = SetOptions l
let inloadpath s : bool call = InLoadPath s
let mkcases s : string list list call = MkCases s

(** * Coq answers to CoqIde *)

let abstract_eval_call handler c =
  try
    let res = match c with
      | Interp (r,b,s) -> Obj.magic (handler.interp (r,b,s))
      | Rewind i -> Obj.magic (handler.rewind i)
      | Goal -> Obj.magic (handler.goals ())
      | Hints -> Obj.magic (handler.hints ())
      | Status -> Obj.magic (handler.status ())
      | GetOptions -> Obj.magic (handler.get_options ())
      | SetOptions opts -> Obj.magic (handler.set_options opts)
      | InLoadPath s -> Obj.magic (handler.inloadpath s)
      | MkCases s -> Obj.magic (handler.mkcases s)
    in Good res
  with e ->
    let (l, str) = handler.handle_exn e in
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
| Element ("int", [], [PCData s]) -> int_of_string s
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

let to_option_state xml = function
| Element ("option_state", [], [sync; depr; name; value]) ->
  {
    opt_sync = to_bool sync;
    opt_depr = to_bool depr;
    opt_name = to_string name;
    opt_value = to_option_value value;
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
      with _ -> None
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
| Hints ->
  Element ("call", ["val", "hints"], [])
| Status ->
  Element ("call", ["val", "status"], [])
| GetOptions ->
  Element ("call", ["val", "getoptions"], [])
| SetOptions opts ->
  let args = List.map (of_pair (of_list of_string) of_option_value) opts in
  Element ("call", ["val", "setoptions"], args)
| InLoadPath file ->
  Element ("call", ["val", "inloadpath"], [PCData file])
| MkCases ind ->
  Element ("call", ["val", "mkcases"], [PCData ind])

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
  | "status" -> Status
  | "getoptions" -> GetOptions
  | "setoptions" ->
    let args = List.map (to_pair (to_list to_string) to_option_value) l in
    SetOptions args
  | "inloadpath" -> InLoadPath (raw_string l)
  | "mkcases" -> MkCases (raw_string l)
  | "hints" -> Hints
  | _ -> raise Marshal_error
  end
| _ -> raise Marshal_error

let of_status s =
  let of_so = of_option of_string in
  Element ("status", [], [of_so s.status_path; of_so s.status_proofname])

let to_status = function
| Element ("status", [], [path; name]) ->
  {
    status_path = to_option to_string path;
    status_proofname = to_option to_string name;
  }
| _ -> raise Marshal_error

let of_goal g =
  let hyp = of_list of_string g.goal_hyp in
  let ccl = of_string g.goal_ccl in
  Element ("goal", [], [hyp; ccl])

let to_goal = function
| Element ("goal", [], [hyp; ccl]) ->
  let hyp = to_list to_string hyp in
  let ccl = to_string ccl in
  { goal_hyp = hyp; goal_ccl = ccl }
| _ -> raise Marshal_error

let of_goals = function
| No_current_proof ->
  Element ("goals", ["val", "no_current_proof"], [])
| Proof_completed ->
  Element ("goals", ["val", "proof_completed"], [])
| Unfocused_goals l ->
  let xml = of_list of_goal l in
  Element ("goals", ["val", "unfocused_goals"], [xml])
| Uninstantiated_evars el ->
  let xml = of_list of_string el in
  Element ("goals", ["val", "uninstantiated_evars"], [xml])
| Goals l ->
  let xml = of_list of_goal l in
  Element ("goals", ["val", "goals"], [xml])

let to_goals = function
| Element ("goals", ["val", "no_current_proof"], []) ->
  No_current_proof
| Element ("goals", ["val", "proof_completed"], []) ->
  Proof_completed
| Element ("goals", ["val", "unfocused_goals"], [xml]) ->
  let l = to_list to_goal xml in
  Unfocused_goals l
| Element ("goals", ["val", "uninstantiated_evars"], [xml]) ->
  let l = to_list to_string xml in
  Uninstantiated_evars l
| Element ("goals", ["val", "goals"], [xml]) ->
  let l = to_list to_goal xml in
  Goals l
| _ -> raise Marshal_error

let of_hints =
  let of_hint = of_list (of_pair of_string of_string) in
  of_option (of_pair (of_list of_hint) of_hint)

let of_answer (q : 'a call) (r : 'a value) =
  let convert = match q with
  | Interp _ -> Obj.magic (of_string : string -> xml)
  | Rewind _ -> Obj.magic (of_int : int -> xml)
  | Goal -> Obj.magic (of_goals : goals -> xml)
  | Hints -> Obj.magic (of_hints : (hint list * hint) option -> xml)
  | Status -> Obj.magic (of_status : status -> xml)
  | GetOptions -> Obj.magic (of_list (of_pair (of_list of_string) of_option_state) : (option_name * option_state) list -> xml)
  | SetOptions _ -> Obj.magic (fun _ -> Element ("unit", [], []))
  | InLoadPath _ -> Obj.magic (of_bool : bool -> xml)
  | MkCases _ -> Obj.magic (of_list (of_list of_string) : string list list -> xml)
  in
  of_value convert r

let to_answer xml =
  let rec convert elt = match elt with
  | Element (tpe, attrs, l) ->
    begin match tpe with
    | "unit" -> Obj.magic ()
    | "string" -> Obj.magic (to_string elt)
    | "int" -> Obj.magic (to_int elt)
    | "status" -> Obj.magic (to_status elt)
    | "bool" -> Obj.magic (to_bool elt)
    | "list" -> Obj.magic (to_list convert elt)
    | "option" -> Obj.magic (to_option convert elt)
    | "pair" -> Obj.magic (to_pair convert convert elt)
    | "goals" -> Obj.magic (to_goals elt)
    | "option_value" -> Obj.magic (to_option_value elt)
    | "option_state" -> Obj.magic (to_option_state elt)
    | _ -> raise Marshal_error
    end
  | _ -> raise Marshal_error
  in
  to_value convert xml

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
    s.opt_name
(*     Printf.sprintf "%s: sync := %b; depr := %b; name := %s; value := %s" *)
(*       key s.opt_sync s.opt_depr s.opt_name (*(pr_option_value s.opt_value)*) "" *)
  in
  "\n  " ^ String.concat "\n  " (List.map map opts)

let pr_call = function
  | Interp (r,b,s) ->
    let raw = if r then "RAW" else "" in
    let verb = if b then "" else "SILENT" in
    "INTERP"^raw^verb^" ["^s^"]"
  | Rewind i -> "REWIND "^(string_of_int i)
  | Goal -> "GOALS"
  | Hints -> "HINTS"
  | Status -> "STATUS"
  | GetOptions -> "GETOPTIONS"
  | SetOptions l -> "SETOPTIONS" ^ " [" ^ pr_setoptions l ^ "]"
  | InLoadPath s -> "INLOADPATH "^s
  | MkCases s -> "MKCASES "^s

let pr_value_gen pr = function
  | Good v -> "GOOD " ^ pr v
  | Fail (_,str) -> "FAIL ["^str^"]"

let pr_value v = pr_value_gen (fun _ -> "") v

let pr_string s = "["^s^"]"
let pr_bool b = if b then "true" else "false"

let pr_status s =
  let path = match s.status_path with
  | None -> "no path; "
  | Some p -> "path = " ^ p ^ "; "
  in
  let name = match s.status_proofname with
  | None -> "no proof;"
  | Some n -> "proof = " ^ n ^ ";"
  in
  "Status: " ^ path ^ name

let pr_mkcases l =
  let l = List.map (String.concat " ") l in
  "[" ^ String.concat " | " l ^ "]"

let pr_goals = function
| No_current_proof -> "No current proof."
| Proof_completed -> "Proof completed."
| Unfocused_goals gl -> Printf.sprintf "Still %i unfocused goals." (List.length gl)
| Uninstantiated_evars el -> Printf.sprintf "Still %i uninstantiated evars." (List.length el)
| Goals gl ->
  let pr_menu s = s in
  let pr_goal { goal_hyp = hyps; goal_ccl = goal } =
    "[" ^ String.concat "; " (List.map pr_menu hyps) ^ " |- " ^ pr_menu goal ^ "]"
  in
  String.concat " " (List.map pr_goal gl)

let pr_full_value call value =
  match call with
    | Interp _ -> pr_value_gen pr_string (Obj.magic value : string value)
    | Rewind i -> pr_value_gen string_of_int (Obj.magic value : int value)
    | Goal -> pr_value_gen pr_goals (Obj.magic value : goals value)
    | Hints -> pr_value value
    | Status -> pr_value_gen pr_status (Obj.magic value : status value)
    | GetOptions -> pr_value_gen pr_getoptions (Obj.magic value : (option_name * option_state) list value)
    | SetOptions _ -> pr_value value
    | InLoadPath s -> pr_value_gen pr_bool (Obj.magic value : bool value)
    | MkCases s -> pr_value_gen pr_mkcases (Obj.magic value : string list list value)
