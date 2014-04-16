(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2014     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Protocol version of this file. This is the date of the last modification. *)

(** WARNING: TO BE UPDATED WHEN MODIFIED! *)

let protocol_version = "20130425~2"

(** * Interface of calls to Coq by CoqIde *)

open Xml_parser
open Interface

type xml = Xml_parser.xml

(** We use phantom types and GADT to protect ourselves against wild casts *)

type 'a call =
  | Interp     of interp_sty
  | Rewind     of rewind_sty
  | Goal       of goals_sty
  | Evars      of evars_sty
  | Hints      of hints_sty
  | Status     of status_sty
  | Search     of search_sty
  | GetOptions of get_options_sty
  | SetOptions of set_options_sty
  | InLoadPath of inloadpath_sty
  | MkCases    of mkcases_sty
  | Quit       of quit_sty
  | About      of about_sty

type unknown

(** The actual calls *)

let interp x      : interp_rty call      = Interp x
let rewind x      : rewind_rty call      = Rewind x
let goals x       : goals_rty call       = Goal x
let evars x       : evars_rty call       = Evars x
let hints x       : hints_rty call       = Hints x
let status x      : status_rty call      = Status x
let get_options x : get_options_rty call = GetOptions x
let set_options x : set_options_rty call = SetOptions x
let inloadpath x  : inloadpath_rty call  = InLoadPath x
let mkcases x     : mkcases_rty call     = MkCases x
let search x      : search_rty call      = Search x
let quit x        : quit_rty call        = Quit x

(** * Coq answers to CoqIde *)

let abstract_eval_call handler (c : 'a call) =
  let mkGood x : 'a value = Good (Obj.magic x) in
  try
    match c with
      | Interp x     -> mkGood (handler.interp x)
      | Rewind x     -> mkGood (handler.rewind x)
      | Goal x       -> mkGood (handler.goals x)
      | Evars x      -> mkGood (handler.evars x)
      | Hints x      -> mkGood (handler.hints x)
      | Status x     -> mkGood (handler.status x)
      | Search x     -> mkGood (handler.search x)
      | GetOptions x -> mkGood (handler.get_options x)
      | SetOptions x -> mkGood (handler.set_options x)
      | InLoadPath x -> mkGood (handler.inloadpath x)
      | MkCases x    -> mkGood (handler.mkcases x)
      | Quit x       -> mkGood (handler.quit x)
      | About x      -> mkGood (handler.about x)
  with any ->
    Fail (handler.handle_exn any)

(* To read and typecheck the answers we give a description of the types,
   and a way to statically check that the reified version is in sync *)
module ReifType : sig

  type 'a val_t

  val unit_t         : unit val_t
  val string_t       : string val_t
  val int_t          : int val_t
  val bool_t         : bool val_t
  val goals_t        : goals val_t
  val evar_t         : evar val_t
  val state_t        : status val_t
  val coq_info_t     : coq_info val_t
  val option_state_t : option_state val_t
  val option_t       : 'a val_t -> 'a option val_t
  val list_t         : 'a val_t -> 'a list val_t
  val coq_object_t   : 'a val_t -> 'a coq_object val_t
  val pair_t         : 'a val_t -> 'b val_t -> ('a * 'b) val_t
  val union_t        : 'a val_t -> 'b val_t -> ('a ,'b) Util.union val_t

  type value_type = private
    | Unit | String | Int | Bool | Goals | Evar | State | Option_state | Coq_info
    | Option of value_type
    | List of value_type
    | Coq_object of value_type
    | Pair of value_type * value_type
    | Union of value_type * value_type

  val check : 'a val_t -> value_type

end = struct

  type value_type =
    | Unit | String | Int | Bool | Goals | Evar | State | Option_state | Coq_info
    | Option of value_type
    | List of value_type
    | Coq_object of value_type
    | Pair of value_type * value_type
    | Union of value_type * value_type

  type 'a val_t = value_type
  let check x = x

  let unit_t         = Unit
  let string_t       = String
  let int_t          = Int
  let bool_t         = Bool
  let goals_t        = Goals
  let evar_t         = Evar
  let state_t        = State
  let coq_info_t     = Coq_info
  let option_state_t = Option_state
  let option_t x     = Option x
  let list_t x       = List x
  let coq_object_t x = Coq_object x
  let pair_t x y     = Pair (x, y)
  let union_t x y    = Union (x, y)

end

open ReifType

(* For every (call : 'a call), we build the reification of 'a.
 * In OCaml 4 we could use GATDs to do that I guess *)
let expected_answer_type call : value_type =
  let hint = list_t (pair_t string_t string_t) in
  let hints = pair_t (list_t hint) hint in
  let options = pair_t (list_t string_t) option_state_t in
  let objs = coq_object_t string_t in
  match call with
  | Interp _     -> check (string_t                     : interp_rty      val_t)
  | Rewind _     -> check (int_t                        : rewind_rty      val_t)
  | Goal _       -> check (option_t goals_t             : goals_rty       val_t)
  | Evars _      -> check (option_t (list_t evar_t)     : evars_rty       val_t)
  | Hints  _     -> check (option_t hints               : hints_rty       val_t)
  | Status _     -> check (state_t                      : status_rty      val_t)
  | Search _     -> check (list_t objs                  : search_rty      val_t)
  | GetOptions _ -> check (list_t options               : get_options_rty val_t)
  | SetOptions _ -> check (unit_t                       : set_options_rty val_t)
  | InLoadPath _ -> check (bool_t                       : inloadpath_rty  val_t)
  | MkCases _    -> check (list_t (list_t string_t)     : mkcases_rty     val_t)
  | Quit _       -> check (unit_t                       : quit_rty        val_t)
  | About _      -> check (coq_info_t                   : about_rty       val_t)

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

let to_unit : xml -> unit = function
  | Element ("unit", [], []) -> ()
  | _ -> raise Marshal_error

let of_bool (b : bool) : xml =
  if b then constructor "bool" "true" []
  else constructor "bool" "false" []

let to_bool xml : bool = do_match xml "bool"
  (fun s _ -> match s with
  | "true" -> true
  | "false" -> false
  | _ -> raise Marshal_error)

let of_list (f : 'a -> xml) (l : 'a list) =
  Element ("list", [], List.map f l)

let to_list (f : xml -> 'a) : xml -> 'a list = function
| Element ("list", [], l) ->
  List.map f l
| _ -> raise Marshal_error

let of_option (f : 'a -> xml) : 'a option -> xml = function
| None -> Element ("option", ["val", "none"], [])
| Some x -> Element ("option", ["val", "some"], [f x])

let to_option (f : xml -> 'a) : xml -> 'a option = function
| Element ("option", ["val", "none"], []) -> None
| Element ("option", ["val", "some"], [x]) -> Some (f x)
| _ -> raise Marshal_error

let of_string (s : string) : xml = Element ("string", [], [PCData s])

let to_string : xml -> string = function
| Element ("string", [], l) -> raw_string l
| _ -> raise Marshal_error

let of_int (i : int) : xml = Element ("int", [], [PCData (string_of_int i)])

let to_int : xml -> int = function
| Element ("int", [], [PCData s]) ->
  (try int_of_string s with Failure _ -> raise Marshal_error)
| _ -> raise Marshal_error

let of_pair (f : 'a -> xml) (g : 'b -> xml) : 'a * 'b -> xml =
  function (x,y) -> Element ("pair", [], [f x; g y])

let to_pair (f : xml -> 'a) (g : xml -> 'b) : xml -> 'a * 'b = function
| Element ("pair", [], [x; y]) -> (f x, g y)
| _ -> raise Marshal_error

let of_union (f : 'a -> xml) (g : 'b -> xml) : ('a,'b) Util.union -> xml =
function
| Util.Inl x -> Element ("union", ["val","in_l"], [f x])
| Util.Inr x -> Element ("union", ["val","in_r"], [g x])

let to_union (f : xml -> 'a) (g : xml -> 'b) : xml -> ('a,'b) Util.union=
function
| Element ("union", ["val","in_l"], [x]) -> Util.Inl (f x)
| Element ("union", ["val","in_r"], [x]) -> Util.Inr (g x)
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
      with Not_found | Failure _ -> None
    in
    let msg = raw_string l in
    Fail (loc, msg)
  else raise Marshal_error
| _ -> raise Marshal_error

let of_call = function
| Interp (id,raw, vrb, cmd) ->
  let flags = (bool_arg "raw" raw) @ (bool_arg "verbose" vrb) in
  Element ("call", ("val", "interp") :: ("id", string_of_int id) :: flags,
  [PCData cmd])
| Rewind n ->
  Element ("call", ("val", "rewind") :: ["steps", string_of_int n], [])
| Goal () ->
  Element ("call", ["val", "goal"], [])
| Evars () ->
  Element ("call", ["val", "evars"], [])
| Hints () ->
  Element ("call", ["val", "hints"], [])
| Status () ->
  Element ("call", ["val", "status"], [])
| Search flags ->
  let args = List.map (of_pair of_search_constraint of_bool) flags in
  Element ("call", ["val", "search"], args)
| GetOptions () ->
  Element ("call", ["val", "getoptions"], [])
| SetOptions opts ->
  let args = List.map (of_pair (of_list of_string) of_option_value) opts in
  Element ("call", ["val", "setoptions"], args)
| InLoadPath file ->
  Element ("call", ["val", "inloadpath"], [PCData file])
| MkCases ind ->
  Element ("call", ["val", "mkcases"], [PCData ind])
| Quit () ->
  Element ("call", ["val", "quit"], [])
| About () ->
  Element ("call", ["val", "about"], [])

let to_call = function
| Element ("call", attrs, l) ->
  let ans = massoc "val" attrs in
  begin match ans with
  | "interp" -> begin
    try
      let id = List.assoc "id" attrs in
      let raw = List.mem_assoc "raw" attrs in
      let vrb = List.mem_assoc "verbose" attrs in
      Interp (int_of_string id, raw, vrb, raw_string l)
    with Not_found -> raise Marshal_error end
  | "rewind" ->
    let steps = int_of_string (massoc "steps" attrs) in
    Rewind steps
  | "goal" -> Goal ()
  | "evars" -> Evars ()
  | "status" -> Status ()
  | "search" ->
    let args = List.map (to_pair to_search_constraint to_bool) l in
    Search args
  | "getoptions" -> GetOptions ()
  | "setoptions" ->
    let args = List.map (to_pair (to_list to_string) to_option_value) l in
    SetOptions args
  | "inloadpath" -> InLoadPath (raw_string l)
  | "mkcases" -> MkCases (raw_string l)
  | "hints" -> Hints ()
  | "quit" -> Quit ()
  | "about" -> About ()
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

let of_message_level = function
| Debug s -> constructor "message_level" "debug" [PCData s]
| Info -> constructor "message_level" "info" []
| Notice -> constructor "message_level" "notice" []
| Warning -> constructor "message_level" "warning" []
| Error -> constructor "message_level" "error" []

let to_message_level xml = do_match xml "message_level"
  (fun s args -> match s with
  | "debug" -> Debug (raw_string args)
  | "info" -> Info
  | "notice" -> Notice
  | "warning" -> Warning
  | "error" -> Error
  | _ -> raise Marshal_error)

let of_message msg =
  let lvl = of_message_level msg.message_level in
  let content = of_string msg.message_content in
  Element ("message", [], [lvl; content])

let to_message xml = match xml with
| Element ("message", [], [lvl; content]) ->
  { message_level = to_message_level lvl; message_content = to_string content }
| _ -> raise Marshal_error

let is_message = function
| Element ("message", _, _) -> true
| _ -> false

let of_loc loc =
  let start, stop = loc in
  Element ("loc",[("start",string_of_int start);("stop",string_of_int stop)],[])

let to_loc xml = match xml with
| Element ("loc", l,[]) ->
    (try
      let start = List.assoc "start" l in
      let stop = List.assoc "stop" l in
      (int_of_string start, int_of_string stop)
    with Not_found | Invalid_argument _ -> raise Marshal_error)
| _ -> raise Marshal_error

let to_feedback_content xml = do_match xml "feedback_content"
  (fun s args -> match s with
  | "addedaxiom" -> AddedAxiom
  | "processed" -> Processed
  | "globref" ->
       (match args with
       | [loc; filepath; modpath; ident; ty] ->
            GlobRef(to_loc loc, to_string filepath, to_string modpath,
                    to_string ident, to_string ty)
       | _ -> raise Marshal_error)
  | _ -> raise Marshal_error)

let of_feedback_content = function
| AddedAxiom -> constructor "feedback_content" "addedaxiom" []
| Processed -> constructor "feedback_content" "processed" []
| GlobRef(loc, filepath, modpath, ident, ty) ->
    constructor "feedback_content" "globref" [
      of_loc loc;
      of_string filepath;
      of_string modpath;
      of_string ident;
      of_string ty
    ]

let of_feedback msg =
  let content = of_feedback_content msg.content in
  Element ("feedback", ["id",string_of_int msg.edit_id], [content])

let to_feedback xml = match xml with
| Element ("feedback", ["id",id], [content]) ->
  { edit_id = int_of_string id;
    content = to_feedback_content content }
| _ -> raise Marshal_error

let is_feedback = function
| Element ("feedback", _, _) -> true
| _ -> false

(** Conversions between ['a value] and xml answers

  When decoding an xml answer, we dynamically check that it is compatible
  with the original call. For that we now rely on the fact that all
  sub-fonctions [to_xxx : xml -> xxx] check that the current xml element
  is "xxx", and raise [Marshal_error] if anything goes wrong.  *)

let of_answer (q : 'a call) (r : 'a value) : xml =
  let rec convert ty : 'a -> xml = match ty with
    | Unit          -> Obj.magic of_unit
    | Bool          -> Obj.magic of_bool
    | String        -> Obj.magic of_string
    | Int           -> Obj.magic of_int
    | State         -> Obj.magic of_status
    | Option_state  -> Obj.magic of_option_state
    | Coq_info      -> Obj.magic of_coq_info
    | Goals         -> Obj.magic of_goals
    | Evar          -> Obj.magic of_evar
    | List t        -> Obj.magic (of_list (convert t))
    | Option t      -> Obj.magic (of_option (convert t))
    | Coq_object t  -> Obj.magic (of_coq_object (convert t))
    | Pair (t1,t2)  -> Obj.magic (of_pair (convert t1) (convert t2))
    | Union (t1,t2) -> Obj.magic (of_union (convert t1) (convert t2))
  in
  of_value (convert (expected_answer_type q)) r

let to_answer xml (c : 'a call) : 'a value =
  let rec convert ty : xml -> 'a = match ty with
    | Unit          -> Obj.magic to_unit
    | Bool          -> Obj.magic to_bool
    | String        -> Obj.magic to_string
    | Int           -> Obj.magic to_int
    | State         -> Obj.magic to_status
    | Option_state  -> Obj.magic to_option_state
    | Coq_info      -> Obj.magic to_coq_info
    | Goals         -> Obj.magic to_goals
    | Evar          -> Obj.magic to_evar
    | List t        -> Obj.magic (to_list (convert t))
    | Option t      -> Obj.magic (to_option (convert t))
    | Coq_object t  -> Obj.magic (to_coq_object (convert t))
    | Pair (t1,t2)  -> Obj.magic (to_pair (convert t1) (convert t2))
    | Union (t1,t2) -> Obj.magic (to_union (convert t1) (convert t2))
  in
  to_value (convert (expected_answer_type c)) xml

(** * Debug printing *)

let pr_unit () = ""
let pr_string s = Printf.sprintf "%S" s
let pr_int i = string_of_int i
let pr_bool b = Printf.sprintf "%B" b
let pr_goal (g : goals) =
  if g.fg_goals = [] then
    if g.bg_goals = [] then "Proof completed."
    else
      let rec pr_focus _ = function
        | [] -> assert false
        | [lg, rg] -> Printf.sprintf "%i" (List.length lg + List.length rg)
        | (lg, rg) :: l ->
          Printf.sprintf "%i:%a" (List.length lg + List.length rg) pr_focus l in
      Printf.sprintf "Still focussed: [%a]." pr_focus g.bg_goals
  else
    let pr_menu s = s in
    let pr_goal { goal_hyp = hyps; goal_ccl = goal } =
      "[" ^ String.concat "; " (List.map pr_menu hyps) ^ " |- " ^
          pr_menu goal ^ "]" in
    String.concat " " (List.map pr_goal g.fg_goals)
let pr_evar (e : evar) = "[" ^ e.evar_info ^ "]"
let pr_status (s : status) =
  let path =
    let l = String.concat "." s.status_path in
    "path=" ^ l ^ ";" in
  let name = match s.status_proofname with
    | None -> "no proof;"
    | Some n -> "proof = " ^ n ^ ";" in
  "Status: " ^ path ^ name
let pr_coq_info (i : coq_info) = "FIXME"
let pr_option_value = function
  | IntValue None -> "none"
  | IntValue (Some i) -> string_of_int i
  | StringValue s -> s
  | BoolValue b -> if b then "true" else "false"
let pr_option_state (s : option_state) =
  Printf.sprintf "sync := %b; depr := %b; name := %s; value := %s\n"
    s.opt_sync s.opt_depr s.opt_name (pr_option_value s.opt_value)
let pr_list pr l = "["^String.concat ";" (List.map pr l)^"]"
let pr_option pr = function None -> "None" | Some x -> "Some("^pr x^")"
let pr_coq_object (o : 'a coq_object) = "FIXME"
let pr_pair pr1 pr2 (a,b) = "("^pr1 a^","^pr2 b^")"
let pr_union pr1 pr2 = function Util.Inl x -> pr1 x | Util.Inr x -> pr2 x

let pr_call = function
  | Interp (id,r,b,s) ->
    let raw = if r then "RAW" else "" in
    let verb = if b then "" else "SILENT" in
    "INTERP"^raw^verb^" "^string_of_int id^" ["^s^"]"
  | Rewind i -> "REWIND "^(string_of_int i)
  | Goal _ -> "GOALS"
  | Evars _ -> "EVARS"
  | Hints _ -> "HINTS"
  | Status _ -> "STATUS"
  | Search _ -> "SEARCH"
  | GetOptions _ -> "GETOPTIONS"
  | SetOptions l -> "SETOPTIONS" ^ " [" ^
      String.concat ";"
        (List.map (pr_pair (pr_list pr_string) pr_option_value) l) ^ "]"
  | InLoadPath s -> "INLOADPATH "^s
  | MkCases s -> "MKCASES "^s
  | Quit _ -> "QUIT"
  | About _ -> "ABOUT"
let pr_value_gen pr = function
  | Good v -> "GOOD " ^ pr v
  | Fail (_,str) -> "FAIL ["^str^"]"
let pr_value v = pr_value_gen (fun _ -> "FIXME") v
let pr_full_value call value =
  let rec pr = function
  | Unit          -> Obj.magic pr_unit
  | Bool          -> Obj.magic pr_bool
  | String        -> Obj.magic pr_string
  | Int           -> Obj.magic pr_int
  | State         -> Obj.magic pr_status
  | Option_state  -> Obj.magic pr_option_state
  | Coq_info      -> Obj.magic pr_coq_info
  | Goals         -> Obj.magic pr_goal
  | Evar          -> Obj.magic pr_evar
  | List t        -> Obj.magic (pr_list (pr t))
  | Option t      -> Obj.magic (pr_option (pr t))
  | Coq_object t  -> Obj.magic pr_coq_object
  | Pair (t1,t2)  -> Obj.magic (pr_pair (pr t1) (pr t2))
  | Union (t1,t2) -> Obj.magic (pr_union (pr t1) (pr t2))
  in
  pr_value_gen (pr (expected_answer_type call)) value
