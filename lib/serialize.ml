(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Protocol version of this file. This is the date of the last modification. *)

(** WARNING: TO BE UPDATED WHEN MODIFIED! *)

let protocol_version = "20140312"

(** * Interface of calls to Coq by CoqIde *)

open Util
open Interface
open Xml_datatype

(* Marshalling of basic types and type constructors *)
module Xml_marshalling = struct

exception Marshal_error

(** Utility functions *)

let rec get_attr attr = function
  | [] -> raise Not_found
  | (k, v) :: l when CString.equal k attr -> v
  | _ :: l -> get_attr attr l

let massoc x l =
  try get_attr x l
  with Not_found -> raise Marshal_error

let constructor t c args = Element (t, ["val", c], args)
let do_match t mf = function
  | Element (s, attrs, args) when CString.equal s t ->
      let c = massoc "val" attrs in
      mf c args
  | _ -> raise Marshal_error

let singleton = function
  | [x] -> x
  | _ -> raise Marshal_error

let raw_string = function
  | [] -> ""
  | [PCData s] -> s
  | _ -> raise Marshal_error

(** Base types *)

let of_unit () = Element ("unit", [], [])
let to_unit : xml -> unit = function
  | Element ("unit", [], []) -> ()
  | _ -> raise Marshal_error

let of_bool (b : bool) : xml =
  if b then constructor "bool" "true" []
  else constructor "bool" "false" []
let to_bool : xml -> bool = do_match "bool" (fun s _ -> match s with
  | "true" -> true
  | "false" -> false
  | _ -> raise Marshal_error)

let of_list (f : 'a -> xml) (l : 'a list) =
  Element ("list", [], List.map f l)
let to_list (f : xml -> 'a) : xml -> 'a list = function
  | Element ("list", [], l) -> List.map f l
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

let of_pair (f : 'a -> xml) (g : 'b -> xml) (x : 'a * 'b) : xml =
  Element ("pair", [], [f (fst x); g (snd x)])
let to_pair (f : xml -> 'a) (g : xml -> 'b) : xml -> 'a * 'b = function
  | Element ("pair", [], [x; y]) -> (f x, g y)
  | _ -> raise Marshal_error

let of_union (f : 'a -> xml) (g : 'b -> xml) : ('a,'b) union -> xml = function
  | Inl x -> Element ("union", ["val","in_l"], [f x])
  | Inr x -> Element ("union", ["val","in_r"], [g x])
let to_union (f : xml -> 'a) (g : xml -> 'b) : xml -> ('a,'b) union = function
  | Element ("union", ["val","in_l"], [x]) -> Inl (f x)
  | Element ("union", ["val","in_r"], [x]) -> Inr (g x)
  | _ -> raise Marshal_error

(** More elaborate types *)

let of_option_value = function
  | IntValue i -> constructor "option_value" "intvalue" [of_option of_int i]
  | BoolValue b -> constructor "option_value" "boolvalue" [of_bool b]
  | StringValue s -> constructor "option_value" "stringvalue" [of_string s]
let to_option_value = do_match "option_value" (fun s args -> match s with
  | "intvalue" -> IntValue (to_option to_int (singleton args))
  | "boolvalue" -> BoolValue (to_bool (singleton args))
  | "stringvalue" -> StringValue (to_string (singleton args))
  | _ -> raise Marshal_error)

let of_option_state s =
  Element ("option_state", [], [
    of_bool s.opt_sync;
    of_bool s.opt_depr;
    of_string s.opt_name;
    of_option_value s.opt_value])
let to_option_state = function
  | Element ("option_state", [], [sync; depr; name; value]) -> {
      opt_sync = to_bool sync;
      opt_depr = to_bool depr;
      opt_name = to_string name;
      opt_value = to_option_value value }
  | _ -> raise Marshal_error

let of_search_cst = function
  | Name_Pattern s ->
    constructor "search_cst" "name_pattern" [of_string s]
  | Type_Pattern s ->
    constructor "search_cst" "type_pattern" [of_string s]
  | SubType_Pattern s ->
    constructor "search_cst" "subtype_pattern" [of_string s]
  | In_Module m ->
    constructor "search_cst" "in_module" [of_list of_string m]
  | Include_Blacklist ->
    constructor "search_cst" "include_blacklist" []
let to_search_cst = do_match "search_cst" (fun s args -> match s with
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

let of_edit_id i = Element ("edit_id",["val",string_of_int i],[])
let to_edit_id = function
  | Element ("edit_id",["val",i],[]) ->
      let id = int_of_string i in
      assert (id <= 0 );
      id
  | _ -> raise Marshal_error

let of_state_id id =
  try Stateid.to_xml id with Invalid_argument _ -> raise Marshal_error
let to_state_id xml =
  try Stateid.of_xml xml with Invalid_argument _ -> raise Marshal_error

let of_edit_or_state_id = function
  | Interface.Edit id -> ["object","edit"], of_edit_id id
  | Interface.State id -> ["object","state"], of_state_id id

let of_value f = function
| Good x -> Element ("value", ["val", "good"], [f x])
| Fail (id,loc, msg) ->
  let loc = match loc with
  | None -> []
  | Some (s, e) -> [("loc_s", string_of_int s); ("loc_e", string_of_int e)] in
  let id = of_state_id id in
  Element ("value", ["val", "fail"] @ loc, [id;PCData msg])
let to_value f = function
| Element ("value", attrs, l) ->
  let ans = massoc "val" attrs in
  if ans = "good" then Good (f (singleton l))
  else if ans = "fail" then
    let loc =
      try
        let loc_s = int_of_string (get_attr "loc_s" attrs) in
        let loc_e = int_of_string (get_attr "loc_e" attrs) in
        Some (loc_s, loc_e)
      with Not_found | Failure _ -> None
    in
    let id = to_state_id (List.hd l) in
    let msg = raw_string (List.tl l) in
    Fail (id, loc, msg)
  else raise Marshal_error
| _ -> raise Marshal_error

let of_status s =
  let of_so = of_option of_string in
  let of_sl = of_list of_string in
  Element ("status", [], [
      of_sl s.status_path;
      of_so s.status_proofname;
      of_sl s.status_allproofs;
      of_int s.status_proofnum; ])
let to_status = function
  | Element ("status", [], [path; name; prfs; pnum]) -> {
      status_path = to_list to_string path;
      status_proofname = to_option to_string name;
      status_allproofs = to_list to_string prfs;
      status_proofnum = to_int pnum; }
  | _ -> raise Marshal_error

let of_evar s = Element ("evar", [], [PCData s.evar_info])
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
  let shelf = of_list of_goal g.shelved_goals in
  let given_up = of_list of_goal g.given_up_goals in
  Element ("goals", [], [fg; bg; shelf; given_up])
let to_goals = function
  | Element ("goals", [], [fg; bg; shelf; given_up]) ->
    let to_glist = to_list to_goal in
    let fg = to_list to_goal fg in
    let bg = to_list (to_pair to_glist to_glist) bg in
    let shelf = to_list to_goal shelf in
    let given_up = to_list to_goal given_up in
    { fg_goals = fg; bg_goals = bg; shelved_goals = shelf; given_up_goals = given_up }
  | _ -> raise Marshal_error

let of_coq_info info =
  let version = of_string info.coqtop_version in
  let protocol = of_string info.protocol_version in
  let release = of_string info.release_date in
  let compile = of_string info.compile_date in
  Element ("coq_info", [], [version; protocol; release; compile])
let to_coq_info = function
  | Element ("coq_info", [], [version; protocol; release; compile]) -> {
      coqtop_version = to_string version;
      protocol_version = to_string protocol;
      release_date = to_string release;
      compile_date = to_string compile; }
  | _ -> raise Marshal_error

let of_message_level = function
  | Debug s -> constructor "message_level" "debug" [PCData s]
  | Info -> constructor "message_level" "info" []
  | Notice -> constructor "message_level" "notice" []
  | Warning -> constructor "message_level" "warning" []
  | Error -> constructor "message_level" "error" []
let to_message_level = do_match "message_level" (fun s args -> match s with
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
  | Element ("message", [], [lvl; content]) -> {
      message_level = to_message_level lvl;
      message_content = to_string content }
  | _ -> raise Marshal_error

let is_message = function
  | Element ("message", _, _) -> true
  | _ -> false

let of_loc loc =
  let start, stop = Loc.unloc loc in
  Element ("loc",[("start",string_of_int start);("stop",string_of_int stop)],[])
let to_loc xml = match xml with
  | Element ("loc", l,[]) ->
      (try
        let start = massoc "start" l in
        let stop = massoc "stop" l in
        Loc.make_loc (int_of_string start, int_of_string stop)
      with Not_found | Invalid_argument _ -> raise Marshal_error)
  | _ -> raise Marshal_error

let to_feedback_content = do_match "feedback_content" (fun s a -> match s,a with
  | "addedaxiom", _ -> AddedAxiom
  | "processed", _ -> Processed
  | "processinginmaster", _ -> ProcessingInMaster
  | "incomplete", _ -> Incomplete
  | "complete", _ -> Complete
  | "globref", [loc; filepath; modpath; ident; ty] ->
       GlobRef(to_loc loc, to_string filepath,
         to_string modpath, to_string ident, to_string ty)
  | "globdef", [loc; ident; secpath; ty] ->
       GlobDef(to_loc loc, to_string ident, to_string secpath, to_string ty)
  | "errormsg", [loc;  s] -> ErrorMsg (to_loc loc, to_string s)
  | "inprogress", [n] -> InProgress (to_int n)
  | "slavestatus", [ns] ->
       let n, s = to_pair to_int to_string ns in
       SlaveStatus(n,s)
  | _ -> raise Marshal_error)
let of_feedback_content = function
  | AddedAxiom -> constructor "feedback_content" "addedaxiom" []
  | Processed -> constructor "feedback_content" "processed" []
  | ProcessingInMaster -> constructor "feedback_content" "processinginmaster" []
  | Incomplete -> constructor "feedback_content" "incomplete" []
  | Complete -> constructor "feedback_content" "complete" []
  | GlobRef(loc, filepath, modpath, ident, ty) ->
      constructor "feedback_content" "globref" [
        of_loc loc;
        of_string filepath;
        of_string modpath;
        of_string ident;
        of_string ty ]
  | GlobDef(loc, ident, secpath, ty) ->
      constructor "feedback_content" "globdef" [
        of_loc loc;
        of_string ident;
        of_string secpath;
        of_string ty ]
  | ErrorMsg(loc, s) ->
      constructor "feedback_content" "errormsg" [of_loc loc; of_string s]
  | InProgress n -> constructor "feedback_content" "inprogress" [of_int n]
  | SlaveStatus(n,s) ->
      constructor "feedback_content" "slavestatus"
        [of_pair of_int of_string (n,s)]

let of_feedback msg =
  let content = of_feedback_content msg.content in
  let obj, id = of_edit_or_state_id msg.id in
  Element ("feedback", obj, [id;content])
let to_feedback xml = match xml with
  | Element ("feedback", ["object","edit"], [id;content]) -> {
      id = Interface.Edit(to_edit_id id);
      content = to_feedback_content content }
  | Element ("feedback", ["object","state"], [id;content]) -> { 
      id = Interface.State(to_state_id id);
      content = to_feedback_content content }
  | _ -> raise Marshal_error

end
include Xml_marshalling

(* Reification of basic types and type constructors, and functions
   from to xml *)
module ReifType : sig

  type 'a val_t

  val unit_t         : unit val_t
  val string_t       : string val_t
  val int_t          : int val_t
  val bool_t         : bool val_t
  
  val option_t       : 'a val_t -> 'a option val_t
  val list_t         : 'a val_t -> 'a list val_t
  val pair_t         : 'a val_t -> 'b val_t -> ('a * 'b) val_t
  val union_t        : 'a val_t -> 'b val_t -> ('a ,'b) union val_t

  val goals_t        : goals val_t
  val evar_t         : evar val_t
  val state_t        : status val_t
  val option_state_t : option_state val_t
  val option_value_t : option_value val_t
  val coq_info_t     : coq_info val_t
  val coq_object_t   : 'a val_t -> 'a coq_object val_t
  val state_id_t     : state_id val_t
  val search_cst_t   : search_constraint val_t

  val of_value_type : 'a val_t -> 'a -> xml
  val to_value_type : 'a val_t -> xml -> 'a

  val print         : 'a val_t -> 'a -> string

  type value_type
  val erase         : 'a val_t -> value_type
  val print_type    : value_type -> string

  val document_type_encoding : (xml -> string) -> unit

end = struct

  type value_type =
    | Unit | String | Int | Bool

    | Option of value_type
    | List of value_type
    | Pair of value_type * value_type
    | Union of value_type * value_type
    
    | Goals | Evar | State | Option_state | Option_value | Coq_info
    | Coq_object of value_type
    | State_id
    | Search_cst

  type 'a val_t = value_type
  
  let erase (x : 'a val_t) : value_type = x

  let unit_t         = Unit
  let string_t       = String
  let int_t          = Int
  let bool_t         = Bool

  let option_t x     = Option x
  let list_t x       = List x
  let pair_t x y     = Pair (x, y)
  let union_t x y    = Union (x, y)

  let goals_t        = Goals
  let evar_t         = Evar
  let state_t        = State
  let option_state_t = Option_state
  let option_value_t = Option_value
  let coq_info_t     = Coq_info
  let coq_object_t x = Coq_object x
  let state_id_t     = State_id
  let search_cst_t   = Search_cst

  let of_value_type (ty : 'a val_t) : 'a -> xml =
    let rec convert ty : 'a -> xml = match ty with
      | Unit          -> Obj.magic of_unit
      | Bool          -> Obj.magic of_bool
      | String        -> Obj.magic of_string
      | Int           -> Obj.magic of_int
      | State         -> Obj.magic of_status
      | Option_state  -> Obj.magic of_option_state
      | Option_value  -> Obj.magic of_option_value
      | Coq_info      -> Obj.magic of_coq_info
      | Goals         -> Obj.magic of_goals
      | Evar          -> Obj.magic of_evar
      | List t        -> Obj.magic (of_list (convert t))
      | Option t      -> Obj.magic (of_option (convert t))
      | Coq_object t  -> Obj.magic (of_coq_object (convert t))
      | Pair (t1,t2)  -> Obj.magic (of_pair (convert t1) (convert t2))
      | Union (t1,t2) -> Obj.magic (of_union (convert t1) (convert t2))
      | State_id      -> Obj.magic of_state_id
      | Search_cst    -> Obj.magic of_search_cst
    in
      convert ty
  
  let to_value_type (ty : 'a val_t) : xml -> 'a =
    let rec convert ty : xml -> 'a = match ty with
      | Unit          -> Obj.magic to_unit
      | Bool          -> Obj.magic to_bool
      | String        -> Obj.magic to_string
      | Int           -> Obj.magic to_int
      | State         -> Obj.magic to_status
      | Option_state  -> Obj.magic to_option_state
      | Option_value  -> Obj.magic to_option_value
      | Coq_info      -> Obj.magic to_coq_info
      | Goals         -> Obj.magic to_goals
      | Evar          -> Obj.magic to_evar
      | List t        -> Obj.magic (to_list (convert t))
      | Option t      -> Obj.magic (to_option (convert t))
      | Coq_object t  -> Obj.magic (to_coq_object (convert t))
      | Pair (t1,t2)  -> Obj.magic (to_pair (convert t1) (convert t2))
      | Union (t1,t2) -> Obj.magic (to_union (convert t1) (convert t2))
      | State_id      -> Obj.magic to_state_id
      | Search_cst    -> Obj.magic to_search_cst
    in
      convert ty

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
            Printf.sprintf "%i:%a"
              (List.length lg + List.length rg) pr_focus l in
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
  let pr_union pr1 pr2 = function Inl x -> "Inl "^pr1 x | Inr x -> "Inr "^pr2 x

  let pr_search_cst = function
    | Name_Pattern s -> "Name_Pattern " ^ s
    | Type_Pattern s -> "Type_Pattern " ^ s
    | SubType_Pattern s -> "SubType_Pattern " ^ s
    | In_Module s -> "In_Module " ^ String.concat "." s
    | Include_Blacklist -> "Include_Blacklist"

  let rec print = function
  | Unit          -> Obj.magic pr_unit
  | Bool          -> Obj.magic pr_bool
  | String        -> Obj.magic pr_string
  | Int           -> Obj.magic pr_int
  | State         -> Obj.magic pr_status
  | Option_state  -> Obj.magic pr_option_state
  | Option_value  -> Obj.magic pr_option_value
  | Search_cst    -> Obj.magic pr_search_cst
  | Coq_info      -> Obj.magic pr_coq_info
  | Goals         -> Obj.magic pr_goal
  | Evar          -> Obj.magic pr_evar
  | List t        -> Obj.magic (pr_list (print t))
  | Option t      -> Obj.magic (pr_option (print t))
  | Coq_object t  -> Obj.magic pr_coq_object
  | Pair (t1,t2)  -> Obj.magic (pr_pair (print t1) (print t2))
  | Union (t1,t2) -> Obj.magic (pr_union (print t1) (print t2))
  | State_id      -> Obj.magic pr_int

  (* This is to break if a rename/refactoring makes the strings below outdated *)
  type 'a exists = bool

  let rec print_type = function
  | Unit          -> "unit"
  | Bool          -> "bool"
  | String        -> "string"
  | Int           -> "int"
  | State         -> assert(true : status exists); "Interface.status"
  | Option_state  -> assert(true : option_state exists); "Interface.option_state"
  | Option_value  -> assert(true : option_value exists); "Interface.option_value"
  | Search_cst    -> assert(true : search_constraint exists); "Interface.search_constraint"
  | Coq_info      -> assert(true : coq_info exists); "Interface.coq_info"
  | Goals         -> assert(true : goals exists); "Interface.goals"
  | Evar          -> assert(true : evar exists); "Interface.evar"
  | List t        -> Printf.sprintf "(%s list)" (print_type t)
  | Option t      -> Printf.sprintf "(%s option)" (print_type t)
  | Coq_object t  -> assert(true : 'a coq_object exists);
                     Printf.sprintf "(%s Interface.coq_object)" (print_type t)
  | Pair (t1,t2)  -> Printf.sprintf "(%s * %s)" (print_type t1) (print_type t2)
  | Union (t1,t2) -> assert(true : ('a,'b) CSig.union exists);
                     Printf.sprintf "((%s, %s) CSig.union)" (print_type t1) (print_type t2)
  | State_id      -> assert(true : Stateid.t exists); "Stateid.t"

  let document_type_encoding pr_xml =
    Printf.printf "\n=== Data encoding by examples ===\n\n";
    Printf.printf "%s:\n\n%s\n\n" (print_type Unit) (pr_xml (of_unit ()));
    Printf.printf "%s:\n\n%s\n%s\n\n" (print_type Bool)
      (pr_xml (of_bool true)) (pr_xml (of_bool false));
    Printf.printf "%s:\n\n%s\n\n" (print_type String) (pr_xml (of_string "hello"));
    Printf.printf "%s:\n\n%s\n\n" (print_type Int) (pr_xml (of_int 256));
    Printf.printf "%s:\n\n%s\n\n" (print_type State_id) (pr_xml (of_state_id Stateid.initial));
    Printf.printf "%s:\n\n%s\n\n" (print_type (List Int)) (pr_xml (of_list of_int [3;4;5]));
    Printf.printf "%s:\n\n%s\n%s\n\n" (print_type (Option Int))
      (pr_xml (of_option of_int (Some 3))) (pr_xml (of_option of_int None));
    Printf.printf "%s:\n\n%s\n\n" (print_type (Pair (Bool,Int)))
      (pr_xml (of_pair of_bool of_int (false,3)));
    Printf.printf "%s:\n\n%s\n\n" (print_type (Union (Bool,Int)))
      (pr_xml (of_union of_bool of_int (Inl false)));
    print_endline ("All other types are records represented by a node named like the OCaml\n"^
                   "type which contains a flattened n-tuple.  We provide one example.\n");
    Printf.printf "%s:\n\n%s\n\n" (print_type Option_state)
      (pr_xml (of_option_state { opt_sync = true; opt_depr = false;
        opt_name = "name1"; opt_value = IntValue (Some 37) }));

end
open ReifType

(** Types reification, checked with explicit casts *)
let add_sty_t : add_sty val_t = 
  pair_t (pair_t string_t int_t) (pair_t state_id_t bool_t)
let edit_at_sty_t : edit_at_sty val_t = state_id_t
let query_sty_t : query_sty val_t = pair_t string_t state_id_t
let goals_sty_t : goals_sty val_t = unit_t
let evars_sty_t : evars_sty val_t = unit_t
let hints_sty_t : hints_sty val_t = unit_t
let status_sty_t : status_sty val_t = bool_t
let search_sty_t : search_sty val_t = list_t (pair_t search_cst_t bool_t)
let get_options_sty_t : get_options_sty val_t = unit_t
let set_options_sty_t : set_options_sty val_t =
  list_t (pair_t (list_t string_t) option_value_t)
let mkcases_sty_t : mkcases_sty val_t = string_t
let quit_sty_t : quit_sty val_t = unit_t
let about_sty_t : about_sty val_t = unit_t
let init_sty_t : init_sty val_t = option_t string_t
let interp_sty_t : interp_sty val_t = pair_t (pair_t bool_t bool_t) string_t
let stop_worker_sty_t : stop_worker_sty val_t = int_t

let add_rty_t : add_rty val_t =
  pair_t state_id_t (pair_t (union_t unit_t state_id_t) string_t)
let edit_at_rty_t : edit_at_rty val_t =
  union_t unit_t (pair_t state_id_t (pair_t state_id_t state_id_t))
let query_rty_t : query_rty val_t = string_t
let goals_rty_t : goals_rty val_t = option_t goals_t
let evars_rty_t : evars_rty val_t = option_t (list_t evar_t)
let hints_rty_t : hints_rty val_t =
  let hint = list_t (pair_t string_t string_t) in
  option_t (pair_t (list_t hint) hint)
let status_rty_t : status_rty val_t = state_t
let search_rty_t : search_rty val_t = list_t (coq_object_t string_t)
let get_options_rty_t : get_options_rty val_t =
  list_t (pair_t (list_t string_t) option_state_t) 
let set_options_rty_t : set_options_rty val_t = unit_t
let mkcases_rty_t : mkcases_rty val_t = list_t (list_t string_t)
let quit_rty_t : quit_rty val_t = unit_t
let about_rty_t : about_rty val_t = coq_info_t
let init_rty_t : init_rty val_t = state_id_t
let interp_rty_t : interp_rty val_t = pair_t state_id_t (union_t string_t string_t)
let stop_worker_rty_t : stop_worker_rty val_t = unit_t

let ($) x = erase x
let calls = [|  
  "Add",        ($)add_sty_t,         ($)add_rty_t;
  "Edit_at",    ($)edit_at_sty_t,     ($)edit_at_rty_t;
  "Query",      ($)query_sty_t,       ($)query_rty_t;
  "Goal",       ($)goals_sty_t,       ($)goals_rty_t;
  "Evars",      ($)evars_sty_t,       ($)evars_rty_t;
  "Hints",      ($)hints_sty_t,       ($)hints_rty_t;
  "Status",     ($)status_sty_t,      ($)status_rty_t;
  "Search",     ($)search_sty_t,      ($)search_rty_t;
  "GetOptions", ($)get_options_sty_t, ($)get_options_rty_t;
  "SetOptions", ($)set_options_sty_t, ($)set_options_rty_t;
  "MkCases",    ($)mkcases_sty_t,     ($)mkcases_rty_t;
  "Quit",       ($)quit_sty_t,        ($)quit_rty_t;
  "About",      ($)about_sty_t,       ($)about_rty_t;
  "Init",       ($)init_sty_t,        ($)init_rty_t;
  "Interp",     ($)interp_sty_t,      ($)interp_rty_t;
  "StopWorker", ($)stop_worker_sty_t, ($)stop_worker_rty_t;
|]

type 'a call =
  | Add        of add_sty
  | Edit_at    of edit_at_sty
  | Query      of query_sty
  | Goal       of goals_sty
  | Evars      of evars_sty
  | Hints      of hints_sty
  | Status     of status_sty
  | Search     of search_sty
  | GetOptions of get_options_sty
  | SetOptions of set_options_sty
  | MkCases    of mkcases_sty
  | Quit       of quit_sty
  | About      of about_sty
  | Init       of init_sty
  | StopWorker of stop_worker_sty
  (* retrocompatibility *)
  | Interp     of interp_sty

let id_of_call = function
  | Add _        -> 0
  | Edit_at _    -> 1
  | Query _      -> 2
  | Goal _       -> 3
  | Evars _      -> 4
  | Hints _      -> 5
  | Status _     -> 6
  | Search _     -> 7
  | GetOptions _ -> 8
  | SetOptions _ -> 9
  | MkCases _    -> 10
  | Quit _       -> 11
  | About _      -> 12
  | Init _       -> 13
  | Interp _     -> 14
  | StopWorker _ -> 15

let str_of_call c = pi1 calls.(id_of_call c)

type unknown

(** We use phantom types and GADT to protect ourselves against wild casts *)
let add x         : add_rty call         = Add x
let edit_at x     : edit_at_rty call     = Edit_at x
let query x       : query_rty call       = Query x
let goals x       : goals_rty call       = Goal x
let evars x       : evars_rty call       = Evars x
let hints x       : hints_rty call       = Hints x
let status x      : status_rty call      = Status x
let get_options x : get_options_rty call = GetOptions x
let set_options x : set_options_rty call = SetOptions x
let mkcases x     : mkcases_rty call     = MkCases x
let search x      : search_rty call      = Search x
let quit x        : quit_rty call        = Quit x
let init x        : init_rty call        = Init x
let interp x      : interp_rty call      = Interp x
let stop_worker x : stop_worker_rty call = StopWorker x

let abstract_eval_call handler (c : 'a call) : 'a value =
  let mkGood x : 'a value = Good (Obj.magic x) in
  try
    match c with
    | Add x        -> mkGood (handler.add x)
    | Edit_at x    -> mkGood (handler.edit_at x)
    | Query x      -> mkGood (handler.query x)
    | Goal x       -> mkGood (handler.goals x)
    | Evars x      -> mkGood (handler.evars x)
    | Hints x      -> mkGood (handler.hints x)
    | Status x     -> mkGood (handler.status x)
    | Search x     -> mkGood (handler.search x)
    | GetOptions x -> mkGood (handler.get_options x)
    | SetOptions x -> mkGood (handler.set_options x)
    | MkCases x    -> mkGood (handler.mkcases x)
    | Quit x       -> mkGood (handler.quit x)
    | About x      -> mkGood (handler.about x)
    | Init x       -> mkGood (handler.init x)
    | Interp x     -> mkGood (handler.interp x)
    | StopWorker x -> mkGood (handler.stop_worker x)
  with any ->
    Fail (handler.handle_exn any)

(** brain dead code, edit if protocol messages are added/removed *)
let of_answer (q : 'a call) (v : 'a value) : xml = match q with
  | Add _        -> of_value (of_value_type add_rty_t        ) (Obj.magic v)
  | Edit_at _    -> of_value (of_value_type edit_at_rty_t    ) (Obj.magic v)
  | Query _      -> of_value (of_value_type query_rty_t      ) (Obj.magic v)
  | Goal _       -> of_value (of_value_type goals_rty_t      ) (Obj.magic v)
  | Evars _      -> of_value (of_value_type evars_rty_t      ) (Obj.magic v)
  | Hints _      -> of_value (of_value_type hints_rty_t      ) (Obj.magic v)
  | Status _     -> of_value (of_value_type status_rty_t     ) (Obj.magic v)
  | Search _     -> of_value (of_value_type search_rty_t     ) (Obj.magic v)
  | GetOptions _ -> of_value (of_value_type get_options_rty_t) (Obj.magic v)
  | SetOptions _ -> of_value (of_value_type set_options_rty_t) (Obj.magic v)
  | MkCases _    -> of_value (of_value_type mkcases_rty_t    ) (Obj.magic v)
  | Quit _       -> of_value (of_value_type quit_rty_t       ) (Obj.magic v)
  | About _      -> of_value (of_value_type about_rty_t      ) (Obj.magic v)
  | Init _       -> of_value (of_value_type init_rty_t       ) (Obj.magic v)
  | Interp _     -> of_value (of_value_type interp_rty_t     ) (Obj.magic v)
  | StopWorker _ -> of_value (of_value_type stop_worker_rty_t) (Obj.magic v)

let to_answer (q : 'a call) (x : xml) : 'a value = match q with
  | Add _        -> Obj.magic (to_value (to_value_type add_rty_t        ) x)
  | Edit_at _    -> Obj.magic (to_value (to_value_type edit_at_rty_t    ) x)
  | Query _      -> Obj.magic (to_value (to_value_type query_rty_t      ) x)
  | Goal _       -> Obj.magic (to_value (to_value_type goals_rty_t      ) x)
  | Evars _      -> Obj.magic (to_value (to_value_type evars_rty_t      ) x)
  | Hints _      -> Obj.magic (to_value (to_value_type hints_rty_t      ) x)
  | Status _     -> Obj.magic (to_value (to_value_type status_rty_t     ) x)
  | Search _     -> Obj.magic (to_value (to_value_type search_rty_t     ) x)
  | GetOptions _ -> Obj.magic (to_value (to_value_type get_options_rty_t) x)
  | SetOptions _ -> Obj.magic (to_value (to_value_type set_options_rty_t) x)
  | MkCases _    -> Obj.magic (to_value (to_value_type mkcases_rty_t    ) x)
  | Quit _       -> Obj.magic (to_value (to_value_type quit_rty_t       ) x)
  | About _      -> Obj.magic (to_value (to_value_type about_rty_t      ) x)
  | Init _       -> Obj.magic (to_value (to_value_type init_rty_t       ) x)
  | Interp _     -> Obj.magic (to_value (to_value_type interp_rty_t     ) x)
  | StopWorker _ -> Obj.magic (to_value (to_value_type stop_worker_rty_t) x)

let of_call (q : 'a call) : xml =
  let mkCall x = constructor "call" (str_of_call q) [x] in
  match q with
  | Add x        -> mkCall (of_value_type add_sty_t         x) 
  | Edit_at x    -> mkCall (of_value_type edit_at_sty_t     x) 
  | Query x      -> mkCall (of_value_type query_sty_t       x) 
  | Goal x       -> mkCall (of_value_type goals_sty_t       x) 
  | Evars x      -> mkCall (of_value_type evars_sty_t       x) 
  | Hints x      -> mkCall (of_value_type hints_sty_t       x) 
  | Status x     -> mkCall (of_value_type status_sty_t      x) 
  | Search x     -> mkCall (of_value_type search_sty_t      x) 
  | GetOptions x -> mkCall (of_value_type get_options_sty_t x) 
  | SetOptions x -> mkCall (of_value_type set_options_sty_t x) 
  | MkCases x    -> mkCall (of_value_type mkcases_sty_t     x) 
  | Quit x       -> mkCall (of_value_type quit_sty_t        x) 
  | About x      -> mkCall (of_value_type about_sty_t       x) 
  | Init x       -> mkCall (of_value_type init_sty_t        x)
  | Interp x     -> mkCall (of_value_type interp_sty_t      x)
  | StopWorker x -> mkCall (of_value_type stop_worker_sty_t x)

let to_call : xml -> unknown call =
  do_match "call" (fun s a ->
    let mkCallArg vt a = to_value_type vt (singleton a) in
    match s with
    | "Add"        -> Add        (mkCallArg add_sty_t         a)
    | "Edit_at"    -> Edit_at    (mkCallArg edit_at_sty_t     a)
    | "Query"      -> Query      (mkCallArg query_sty_t       a)
    | "Goal"       -> Goal       (mkCallArg goals_sty_t       a)
    | "Evars"      -> Evars      (mkCallArg evars_sty_t       a)
    | "Hints"      -> Hints      (mkCallArg hints_sty_t       a)
    | "Status"     -> Status     (mkCallArg status_sty_t      a)
    | "Search"     -> Search     (mkCallArg search_sty_t      a)
    | "GetOptions" -> GetOptions (mkCallArg get_options_sty_t a)
    | "SetOptions" -> SetOptions (mkCallArg set_options_sty_t a)
    | "MkCases"    -> MkCases    (mkCallArg mkcases_sty_t     a)
    | "Quit"       -> Quit       (mkCallArg quit_sty_t        a)
    | "About"      -> About      (mkCallArg about_sty_t       a)
    | "Init"       -> Init       (mkCallArg init_sty_t        a)
    | "Interp"     -> Interp     (mkCallArg interp_sty_t      a)
    | "StopWorker" -> StopWorker (mkCallArg stop_worker_sty_t a)
    | _ -> raise Marshal_error)

(** misc *)

let is_feedback = function
  | Element ("feedback", _, _) -> true
  | _ -> false

(** Debug printing *)

let pr_value_gen pr = function
  | Good v -> "GOOD " ^ pr v
  | Fail (id,None,str) -> "FAIL "^Stateid.to_string id^" ["^str^"]"
  | Fail (id,Some(i,j),str) ->
      "FAIL "^Stateid.to_string id^
        " ("^string_of_int i^","^string_of_int j^")["^str^"]"
let pr_value v = pr_value_gen (fun _ -> "FIXME") v
let pr_full_value call value = match call with
  | Add _        -> pr_value_gen (print add_rty_t        ) (Obj.magic value) 
  | Edit_at _    -> pr_value_gen (print edit_at_rty_t    ) (Obj.magic value) 
  | Query _      -> pr_value_gen (print query_rty_t      ) (Obj.magic value) 
  | Goal _       -> pr_value_gen (print goals_rty_t      ) (Obj.magic value) 
  | Evars _      -> pr_value_gen (print evars_rty_t      ) (Obj.magic value) 
  | Hints _      -> pr_value_gen (print hints_rty_t      ) (Obj.magic value) 
  | Status _     -> pr_value_gen (print status_rty_t     ) (Obj.magic value) 
  | Search _     -> pr_value_gen (print search_rty_t     ) (Obj.magic value) 
  | GetOptions _ -> pr_value_gen (print get_options_rty_t) (Obj.magic value) 
  | SetOptions _ -> pr_value_gen (print set_options_rty_t) (Obj.magic value) 
  | MkCases _    -> pr_value_gen (print mkcases_rty_t    ) (Obj.magic value) 
  | Quit _       -> pr_value_gen (print quit_rty_t       ) (Obj.magic value) 
  | About _      -> pr_value_gen (print about_rty_t      ) (Obj.magic value) 
  | Init _       -> pr_value_gen (print init_rty_t       ) (Obj.magic value)
  | Interp _     -> pr_value_gen (print interp_rty_t     ) (Obj.magic value)
  | StopWorker _ -> pr_value_gen (print stop_worker_rty_t) (Obj.magic value)
let pr_call call = match call with
  | Add x        -> str_of_call call ^ " " ^ print add_sty_t         x
  | Edit_at x    -> str_of_call call ^ " " ^ print edit_at_sty_t     x
  | Query x      -> str_of_call call ^ " " ^ print query_sty_t       x
  | Goal x       -> str_of_call call ^ " " ^ print goals_sty_t       x
  | Evars x      -> str_of_call call ^ " " ^ print evars_sty_t       x
  | Hints x      -> str_of_call call ^ " " ^ print hints_sty_t       x
  | Status x     -> str_of_call call ^ " " ^ print status_sty_t      x
  | Search x     -> str_of_call call ^ " " ^ print search_sty_t      x
  | GetOptions x -> str_of_call call ^ " " ^ print get_options_sty_t x
  | SetOptions x -> str_of_call call ^ " " ^ print set_options_sty_t x
  | MkCases x    -> str_of_call call ^ " " ^ print mkcases_sty_t     x
  | Quit x       -> str_of_call call ^ " " ^ print quit_sty_t        x
  | About x      -> str_of_call call ^ " " ^ print about_sty_t       x
  | Init x       -> str_of_call call ^ " " ^ print init_sty_t        x
  | Interp x     -> str_of_call call ^ " " ^ print interp_sty_t      x
  | StopWorker x -> str_of_call call ^ " " ^ print stop_worker_sty_t x

let document to_string_fmt =
  Printf.printf "=== Available calls ===\n\n";
  Array.iter (fun (cname, csty, crty) ->
      Printf.printf "%12s :  %s\n %14s %s\n"
        ("\""^cname^"\"") (print_type csty) "->" (print_type crty))
    calls;
  Printf.printf "\n=== Calls XML encoding ===\n\n";
  Printf.printf "A call \"C\" carrying input a is encoded as:\n\n%s\n\n"
    (to_string_fmt (constructor "call" "C" [PCData "a"]));
  Printf.printf "A response carrying output b can either be:\n\n%s\n\n"
    (to_string_fmt (of_value (fun _ -> PCData "b") (Good ())));
  Printf.printf "or:\n\n%s\n\nwhere the attributes loc_s and loc_c are optional.\n"
    (to_string_fmt (of_value (fun _ -> PCData "b")
      (Fail (Stateid.initial,Some (15,34),"error message"))));
  document_type_encoding to_string_fmt

(* vim: set foldmethod=marker: *)
