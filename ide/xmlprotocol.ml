(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Protocol version of this file. This is the date of the last modification. *)

(** WARNING: TO BE UPDATED WHEN MODIFIED! *)

let protocol_version = "20170413"

type msg_format = Richpp of int | Ppcmds
let msg_format = ref (Richpp 72)

(** * Interface of calls to Coq by CoqIde *)

open Util
open Interface
open Serialize
open Xml_datatype

(* Marshalling of basic types and type constructors *)
module Xml_marshalling = struct

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
  | x -> raise (Marshal_error("search",PCData x)))

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
| x -> raise (Marshal_error("coq_object",x))

let of_option_value = function
  | IntValue i -> constructor "option_value" "intvalue" [of_option of_int i]
  | BoolValue b -> constructor "option_value" "boolvalue" [of_bool b]
  | StringValue s -> constructor "option_value" "stringvalue" [of_string s]
  | StringOptValue s -> constructor "option_value" "stringoptvalue" [of_option of_string s]
let to_option_value = do_match "option_value" (fun s args -> match s with
  | "intvalue" -> IntValue (to_option to_int (singleton args))
  | "boolvalue" -> BoolValue (to_bool (singleton args))
  | "stringvalue" -> StringValue (to_string (singleton args))
  | "stringoptvalue" -> StringOptValue (to_option to_string (singleton args))
  | x -> raise (Marshal_error("*value",PCData x)))

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
  | x -> raise (Marshal_error("option_state",x))

let to_stateid = function
  | Element ("state_id",["val",i],[]) ->
      let id = int_of_string i in
      Stateid.of_int id
  | _ -> raise (Invalid_argument "to_state_id")

let of_stateid i = Element ("state_id",["val",string_of_int (Stateid.to_int i)],[])

let to_routeid = function
  | Element ("route_id",["val",i],[]) ->
      let id = int_of_string i in id
  | _ -> raise (Invalid_argument "to_route_id")

let of_routeid i = Element ("route_id",["val",string_of_int i],[])

let of_box (ppb : Pp.block_type) = let open Pp in match ppb with
  | Pp_hbox   i -> constructor "ppbox" "hbox"   [of_int i]
  | Pp_vbox   i -> constructor "ppbox" "vbox"   [of_int i]
  | Pp_hvbox  i -> constructor "ppbox" "hvbox"  [of_int i]
  | Pp_hovbox i -> constructor "ppbox" "hovbox" [of_int i]

let to_box = let open Pp in
  do_match "ppbox" (fun s args -> match s with
      | "hbox"   -> Pp_hbox   (to_int (singleton args))
      | "vbox"   -> Pp_vbox   (to_int (singleton args))
      | "hvbox"  -> Pp_hvbox  (to_int (singleton args))
      | "hovbox" -> Pp_hovbox (to_int (singleton args))
      | x        -> raise (Marshal_error("*ppbox",PCData x))
    )

let rec of_pp (pp : Pp.t) = let open Pp in match Pp.repr pp with
    | Ppcmd_empty         -> constructor "ppdoc" "empty"  []
    | Ppcmd_string s      -> constructor "ppdoc" "string" [of_string s]
    | Ppcmd_glue sl       -> constructor "ppdoc" "glue"   [of_list of_pp sl]
    | Ppcmd_box (bt,s)    -> constructor "ppdoc" "box"    [of_pair of_box of_pp (bt,s)]
    | Ppcmd_tag (t,s)     -> constructor "ppdoc" "tag"    [of_pair of_string of_pp (t,s)]
    | Ppcmd_print_break (i,j)
                          -> constructor "ppdoc" "break"     [of_pair of_int of_int (i,j)]
    | Ppcmd_force_newline -> constructor "ppdoc" "newline"   []
    | Ppcmd_comment cmd   -> constructor "ppdoc" "comment" [of_list of_string cmd]


let rec to_pp xpp = let open Pp in
  Pp.unrepr @@
  do_match "ppdoc" (fun s args -> match s with
    | "empty"     -> Ppcmd_empty
    | "string"    -> Ppcmd_string (to_string (singleton args))
    | "glue"      -> Ppcmd_glue (to_list to_pp (singleton args))
    | "box"       -> let (bt,s) = to_pair to_box to_pp (singleton args) in
                     Ppcmd_box(bt,s)
    | "tag"       -> let (tg,s) = to_pair to_string to_pp (singleton args) in
                     Ppcmd_tag(tg,s)
    | "break"     -> let (i,j)   = to_pair to_int to_int (singleton args) in
                     Ppcmd_print_break(i, j)
    | "newline"   -> Ppcmd_force_newline
    | "comment"   -> Ppcmd_comment (to_list to_string (singleton args))
    | x           -> raise (Marshal_error("*ppdoc",PCData x))
  ) xpp

let of_richpp x = Element ("richpp", [], [x])

(* Run-time Selectable *)
let of_pp (pp : Pp.t) =
  match !msg_format with
  | Richpp margin -> of_richpp (Richpp.richpp_of_pp margin pp)
  | Ppcmds        -> of_pp pp

let of_value f = function
| Good x -> Element ("value", ["val", "good"], [f x])
| Fail (id,loc, msg) ->
  let loc = match loc with
  | None -> []
  | Some (s, e) -> [("loc_s", string_of_int s); ("loc_e", string_of_int e)] in
  let id = of_stateid id in
  Element ("value", ["val", "fail"] @ loc, [id; of_pp msg])

let to_value f = function
| Element ("value", attrs, l) ->
  let ans = massoc "val" attrs in
  if ans = "good" then Good (f (singleton l))
  else if ans = "fail" then
    let loc =
      try
        let loc_s = int_of_string (Serialize.massoc "loc_s" attrs) in
        let loc_e = int_of_string (Serialize.massoc "loc_e" attrs) in
        Some (loc_s, loc_e)
      with Marshal_error _ | Failure _ -> None
    in
    let (id, msg) = match l with [id; msg] -> (id, msg) | _ -> raise (Marshal_error("val",PCData "no id attribute")) in
    let id = to_stateid id in
    let msg = to_pp msg    in
    Fail (id, loc, msg)
  else raise (Marshal_error("good or fail",PCData ans))
| x -> raise (Marshal_error("value",x))

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
  | x -> raise (Marshal_error("status",x))

let of_evar s = Element ("evar", [], [PCData s.evar_info])
let to_evar = function
  | Element ("evar", [], data) -> { evar_info = raw_string data; }
  | x -> raise (Marshal_error("evar",x))

let of_goal g =
  let hyp = of_list of_pp g.goal_hyp in
  let ccl = of_pp g.goal_ccl in
  let id = of_string g.goal_id in
  Element ("goal", [], [id; hyp; ccl])
let to_goal = function
  | Element ("goal", [], [id; hyp; ccl]) ->
    let hyp = to_list to_pp hyp in
    let ccl = to_pp ccl         in
    let id  = to_string id      in
    { goal_hyp = hyp; goal_ccl = ccl; goal_id = id; }
  | x -> raise (Marshal_error("goal",x))

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
    { fg_goals = fg; bg_goals = bg; shelved_goals = shelf;
      given_up_goals = given_up }
  | x -> raise (Marshal_error("goals",x))

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
  | x -> raise (Marshal_error("coq_info",x))

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
  val xml_t          : Xml_datatype.xml val_t

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
  val route_id_t     : route_id val_t
  val search_cst_t   : search_constraint val_t

  val of_value_type : 'a val_t -> 'a -> xml
  val to_value_type : 'a val_t -> xml -> 'a

  val print         : 'a val_t -> 'a -> string

  type value_type
  val erase         : 'a val_t -> value_type
  val print_type    : value_type -> string

  val document_type_encoding : (xml -> string) -> unit

end = struct

  type _ val_t =
    | Unit : unit val_t
    | String : string val_t
    | Int : int val_t
    | Bool : bool val_t
    | Xml : Xml_datatype.xml val_t

    | Option : 'a val_t -> 'a option val_t
    | List : 'a val_t -> 'a list val_t
    | Pair : 'a val_t * 'b val_t -> ('a * 'b) val_t
    | Union : 'a val_t * 'b val_t -> ('a, 'b) union val_t

    | Goals : goals val_t
    | Evar : evar val_t
    | State : status val_t
    | Option_state : option_state val_t
    | Option_value : option_value val_t
    | Coq_info : coq_info val_t
    | Coq_object : 'a val_t -> 'a coq_object val_t
    | State_id : state_id val_t
    | Route_id : route_id val_t
    | Search_cst : search_constraint val_t

  type value_type = Value_type : 'a val_t -> value_type

  let erase (x : 'a val_t) = Value_type x

  let unit_t         = Unit
  let string_t       = String
  let int_t          = Int
  let bool_t         = Bool
  let xml_t          = Xml

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
  let route_id_t     = Route_id
  let search_cst_t   = Search_cst

  let of_value_type (ty : 'a val_t) : 'a -> xml =
    let rec convert : type a. a val_t -> a -> xml = function
      | Unit          -> of_unit
      | Bool          -> of_bool
      | Xml           -> (fun x -> x)
      | String        -> of_string
      | Int           -> of_int
      | State         -> of_status
      | Option_state  -> of_option_state
      | Option_value  -> of_option_value
      | Coq_info      -> of_coq_info
      | Goals         -> of_goals
      | Evar          -> of_evar
      | List t        -> (of_list (convert t))
      | Option t      -> (of_option (convert t))
      | Coq_object t  -> (of_coq_object (convert t))
      | Pair (t1,t2)  -> (of_pair (convert t1) (convert t2))
      | Union (t1,t2) -> (of_union (convert t1) (convert t2))
      | State_id      -> of_stateid
      | Route_id      -> of_routeid
      | Search_cst    -> of_search_cst
    in
      convert ty

  let to_value_type (ty : 'a val_t) : xml -> 'a =
    let rec convert : type a. a val_t -> xml -> a = function
      | Unit          -> to_unit
      | Bool          -> to_bool
      | Xml           -> (fun x -> x)
      | String        -> to_string
      | Int           -> to_int
      | State         -> to_status
      | Option_state  -> to_option_state
      | Option_value  -> to_option_value
      | Coq_info      -> to_coq_info
      | Goals         -> to_goals
      | Evar          -> to_evar
      | List t        -> (to_list (convert t))
      | Option t      -> (to_option (convert t))
      | Coq_object t  -> (to_coq_object (convert t))
      | Pair (t1,t2)  -> (to_pair (convert t1) (convert t2))
      | Union (t1,t2) -> (to_union (convert t1) (convert t2))
      | State_id      -> to_stateid
      | Route_id      -> to_routeid
      | Search_cst    -> to_search_cst
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
      let pr_goal { goal_hyp = hyps; goal_ccl = goal } =
        "[" ^ String.concat "; " (List.map Pp.string_of_ppcmds hyps) ^ " |- " ^
            Pp.string_of_ppcmds goal ^ "]" in
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
    | StringOptValue None -> "none"
    | StringOptValue (Some s) -> s
    | BoolValue b -> if b then "true" else "false"
  let pr_option_state (s : option_state) =
    Printf.sprintf "sync := %b; depr := %b; name := %s; value := %s\n"
      s.opt_sync s.opt_depr s.opt_name (pr_option_value s.opt_value)
  let pr_list pr l = "["^String.concat ";" (List.map pr l)^"]"
  let pr_option pr = function None -> "None" | Some x -> "Some("^pr x^")"
  let pr_coq_object (o : 'a coq_object) = "FIXME"
  let pr_pair pr1 pr2 (a,b) = "("^pr1 a^","^pr2 b^")"
  let pr_union pr1 pr2 = function Inl x -> "Inl "^pr1 x | Inr x -> "Inr "^pr2 x
  let pr_state_id = Stateid.to_string

  let pr_search_cst = function
    | Name_Pattern s -> "Name_Pattern " ^ s
    | Type_Pattern s -> "Type_Pattern " ^ s
    | SubType_Pattern s -> "SubType_Pattern " ^ s
    | In_Module s -> "In_Module " ^ String.concat "." s
    | Include_Blacklist -> "Include_Blacklist"

  let rec print : type a. a val_t -> a -> string = function
  | Unit          -> pr_unit
  | Bool          -> pr_bool
  | String        -> pr_string
  | Xml           -> Xml_printer.to_string_fmt
  | Int           -> pr_int
  | State         -> pr_status
  | Option_state  -> pr_option_state
  | Option_value  -> pr_option_value
  | Search_cst    -> pr_search_cst
  | Coq_info      -> pr_coq_info
  | Goals         -> pr_goal
  | Evar          -> pr_evar
  | List t        -> (pr_list (print t))
  | Option t      -> (pr_option (print t))
  | Coq_object t  -> pr_coq_object
  | Pair (t1,t2)  -> (pr_pair (print t1) (print t2))
  | Union (t1,t2) -> (pr_union (print t1) (print t2))
  | State_id      -> pr_state_id
  | Route_id      -> pr_int

  (* This is to break if a rename/refactoring makes the strings below outdated *)
  type 'a exists = bool

  let rec print_val_t : type a. a val_t -> string = function
  | Unit          -> "unit"
  | Bool          -> "bool"
  | String        -> "string"
  | Xml           -> "xml"
  | Int           -> "int"
  | State         -> assert(true : status exists); "Interface.status"
  | Option_state  -> assert(true : option_state exists); "Interface.option_state"
  | Option_value  -> assert(true : option_value exists); "Interface.option_value"
  | Search_cst    -> assert(true : search_constraint exists); "Interface.search_constraint"
  | Coq_info      -> assert(true : coq_info exists); "Interface.coq_info"
  | Goals         -> assert(true : goals exists); "Interface.goals"
  | Evar          -> assert(true : evar exists); "Interface.evar"
  | List t        -> Printf.sprintf "(%s list)" (print_val_t t)
  | Option t      -> Printf.sprintf "(%s option)" (print_val_t t)
  | Coq_object t  -> assert(true : 'a coq_object exists);
                     Printf.sprintf "(%s Interface.coq_object)" (print_val_t t)
  | Pair (t1,t2)  -> Printf.sprintf "(%s * %s)" (print_val_t t1) (print_val_t t2)
  | Union (t1,t2) -> assert(true : ('a,'b) CSig.union exists);
                     Printf.sprintf "((%s, %s) CSig.union)" (print_val_t t1) (print_val_t t2)
  | State_id      -> assert(true : Stateid.t exists); "Stateid.t"
  | Route_id      -> assert(true : route_id exists); "route_id"

  let print_type = function Value_type ty -> print_val_t ty

  let document_type_encoding pr_xml =
    Printf.printf "\n=== Data encoding by examples ===\n\n";
    Printf.printf "%s:\n\n%s\n\n" (print_val_t Unit) (pr_xml (of_unit ()));
    Printf.printf "%s:\n\n%s\n%s\n\n" (print_val_t Bool)
      (pr_xml (of_bool true)) (pr_xml (of_bool false));
    Printf.printf "%s:\n\n%s\n\n" (print_val_t String) (pr_xml (of_string "hello"));
    Printf.printf "%s:\n\n%s\n\n" (print_val_t Int) (pr_xml (of_int 256));
    Printf.printf "%s:\n\n%s\n\n" (print_val_t State_id) (pr_xml (of_stateid Stateid.initial));
    Printf.printf "%s:\n\n%s\n\n" (print_val_t (List Int)) (pr_xml (of_list of_int [3;4;5]));
    Printf.printf "%s:\n\n%s\n%s\n\n" (print_val_t (Option Int))
      (pr_xml (of_option of_int (Some 3))) (pr_xml (of_option of_int None));
    Printf.printf "%s:\n\n%s\n\n" (print_val_t (Pair (Bool,Int)))
      (pr_xml (of_pair of_bool of_int (false,3)));
    Printf.printf "%s:\n\n%s\n\n" (print_val_t (Union (Bool,Int)))
      (pr_xml (of_union of_bool of_int (Inl false)));
    print_endline ("All other types are records represented by a node named like the OCaml\n"^
                   "type which contains a flattened n-tuple.  We provide one example.\n");
    Printf.printf "%s:\n\n%s\n\n" (print_val_t Option_state)
      (pr_xml (of_option_state { opt_sync = true; opt_depr = false;
        opt_name = "name1"; opt_value = IntValue (Some 37) }));

end
open ReifType

(** Types reification, checked with explicit casts *)
let add_sty_t : add_sty val_t =
  pair_t (pair_t string_t int_t) (pair_t state_id_t bool_t)
let edit_at_sty_t : edit_at_sty val_t = state_id_t
let query_sty_t : query_sty val_t = pair_t route_id_t (pair_t string_t state_id_t)
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
let wait_sty_t : wait_sty val_t = unit_t
let about_sty_t : about_sty val_t = unit_t
let init_sty_t : init_sty val_t = option_t string_t
let interp_sty_t : interp_sty val_t = pair_t (pair_t bool_t bool_t) string_t
let stop_worker_sty_t : stop_worker_sty val_t = string_t
let print_ast_sty_t : print_ast_sty val_t = state_id_t
let annotate_sty_t : annotate_sty val_t = string_t

let add_rty_t : add_rty val_t =
  pair_t state_id_t (pair_t (union_t unit_t state_id_t) string_t)
let edit_at_rty_t : edit_at_rty val_t =
  union_t unit_t (pair_t state_id_t (pair_t state_id_t state_id_t))
let query_rty_t : query_rty val_t = unit_t
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
let wait_rty_t : wait_rty val_t = unit_t
let about_rty_t : about_rty val_t = coq_info_t
let init_rty_t : init_rty val_t = state_id_t
let interp_rty_t : interp_rty val_t = pair_t state_id_t (union_t string_t string_t)
let stop_worker_rty_t : stop_worker_rty val_t = unit_t
let print_ast_rty_t : print_ast_rty val_t = xml_t
let annotate_rty_t : annotate_rty val_t = xml_t

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
  "Wait",       ($)wait_sty_t,        ($)wait_rty_t;
  "About",      ($)about_sty_t,       ($)about_rty_t;
  "Init",       ($)init_sty_t,        ($)init_rty_t;
  "Interp",     ($)interp_sty_t,      ($)interp_rty_t;
  "StopWorker", ($)stop_worker_sty_t, ($)stop_worker_rty_t;
  "PrintAst",   ($)print_ast_sty_t,   ($)print_ast_rty_t;
  "Annotate",   ($)annotate_sty_t,    ($)annotate_rty_t;
|]

type 'a call =
  | Add        : add_sty -> add_rty call
  | Edit_at    : edit_at_sty -> edit_at_rty call
  | Query      : query_sty -> query_rty call
  | Goal       : goals_sty -> goals_rty call
  | Evars      : evars_sty -> evars_rty call
  | Hints      : hints_sty -> hints_rty call
  | Status     : status_sty -> status_rty call
  | Search     : search_sty -> search_rty call
  | GetOptions : get_options_sty -> get_options_rty call
  | SetOptions : set_options_sty -> set_options_rty call
  | MkCases    : mkcases_sty -> mkcases_rty call
  | Quit       : quit_sty -> quit_rty call
  | About      : about_sty -> about_rty call
  | Init       : init_sty -> init_rty call
  | StopWorker : stop_worker_sty -> stop_worker_rty call
  (* internal use (fake_ide) only, do not use *)
  | Wait       : wait_sty -> wait_rty call
  (* retrocompatibility *)
  | Interp     : interp_sty -> interp_rty call
  | PrintAst   : print_ast_sty -> print_ast_rty call
  | Annotate   : annotate_sty -> annotate_rty call

let id_of_call : type a. a call -> int = function
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
  | Wait _       -> 12
  | About _      -> 13
  | Init _       -> 14
  | Interp _     -> 15
  | StopWorker _ -> 16
  | PrintAst _   -> 17
  | Annotate _   -> 18

let str_of_call c = pi1 calls.(id_of_call c)

type unknown_call = Unknown : 'a call -> unknown_call

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
let wait x        : wait_rty call        = Wait x
let interp x      : interp_rty call      = Interp x
let stop_worker x : stop_worker_rty call = StopWorker x
let print_ast   x : print_ast_rty call   = PrintAst x
let annotate   x : annotate_rty call    = Annotate x

let abstract_eval_call : type a. _ -> a call -> a value = fun handler c ->
  let mkGood : type a. a -> a value = fun x -> Good x in
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
    | Wait x       -> mkGood (handler.wait x)
    | About x      -> mkGood (handler.about x)
    | Init x       -> mkGood (handler.init x)
    | Interp x     -> mkGood (handler.interp x)
    | StopWorker x -> mkGood (handler.stop_worker x)
    | PrintAst x   -> mkGood (handler.print_ast x)
    | Annotate x   -> mkGood (handler.annotate x)
  with any ->
    let any = CErrors.push any in
    Fail (handler.handle_exn any)

(** brain dead code, edit if protocol messages are added/removed *)
let of_answer : type a. a call -> a value -> xml = function
  | Add _        -> of_value (of_value_type add_rty_t        )
  | Edit_at _    -> of_value (of_value_type edit_at_rty_t    )
  | Query _      -> of_value (of_value_type query_rty_t      )
  | Goal _       -> of_value (of_value_type goals_rty_t      )
  | Evars _      -> of_value (of_value_type evars_rty_t      )
  | Hints _      -> of_value (of_value_type hints_rty_t      )
  | Status _     -> of_value (of_value_type status_rty_t     )
  | Search _     -> of_value (of_value_type search_rty_t     )
  | GetOptions _ -> of_value (of_value_type get_options_rty_t)
  | SetOptions _ -> of_value (of_value_type set_options_rty_t)
  | MkCases _    -> of_value (of_value_type mkcases_rty_t    )
  | Quit _       -> of_value (of_value_type quit_rty_t       )
  | Wait _       -> of_value (of_value_type wait_rty_t       )
  | About _      -> of_value (of_value_type about_rty_t      )
  | Init _       -> of_value (of_value_type init_rty_t       )
  | Interp _     -> of_value (of_value_type interp_rty_t     )
  | StopWorker _ -> of_value (of_value_type stop_worker_rty_t)
  | PrintAst _   -> of_value (of_value_type print_ast_rty_t  )
  | Annotate _   -> of_value (of_value_type annotate_rty_t   )

let of_answer msg_fmt =
  msg_format := msg_fmt; of_answer

let to_answer : type a. a call -> xml -> a value = function
  | Add _        -> to_value (to_value_type add_rty_t        )
  | Edit_at _    -> to_value (to_value_type edit_at_rty_t    )
  | Query _      -> to_value (to_value_type query_rty_t      )
  | Goal _       -> to_value (to_value_type goals_rty_t      )
  | Evars _      -> to_value (to_value_type evars_rty_t      )
  | Hints _      -> to_value (to_value_type hints_rty_t      )
  | Status _     -> to_value (to_value_type status_rty_t     )
  | Search _     -> to_value (to_value_type search_rty_t     )
  | GetOptions _ -> to_value (to_value_type get_options_rty_t)
  | SetOptions _ -> to_value (to_value_type set_options_rty_t)
  | MkCases _    -> to_value (to_value_type mkcases_rty_t    )
  | Quit _       -> to_value (to_value_type quit_rty_t       )
  | Wait _       -> to_value (to_value_type wait_rty_t       )
  | About _      -> to_value (to_value_type about_rty_t      )
  | Init _       -> to_value (to_value_type init_rty_t       )
  | Interp _     -> to_value (to_value_type interp_rty_t     )
  | StopWorker _ -> to_value (to_value_type stop_worker_rty_t)
  | PrintAst _   -> to_value (to_value_type print_ast_rty_t  )
  | Annotate _   -> to_value (to_value_type annotate_rty_t   )

let of_call : type a. a call -> xml = fun q ->
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
  | Wait x       -> mkCall (of_value_type wait_sty_t        x)
  | About x      -> mkCall (of_value_type about_sty_t       x)
  | Init x       -> mkCall (of_value_type init_sty_t        x)
  | Interp x     -> mkCall (of_value_type interp_sty_t      x)
  | StopWorker x -> mkCall (of_value_type stop_worker_sty_t x)
  | PrintAst x   -> mkCall (of_value_type print_ast_sty_t   x)
  | Annotate x   -> mkCall (of_value_type annotate_sty_t    x)

let to_call : xml -> unknown_call =
  do_match "call" (fun s a ->
    let mkCallArg vt a = to_value_type vt (singleton a) in
    match s with
    | "Add"        -> Unknown (Add        (mkCallArg add_sty_t         a))
    | "Edit_at"    -> Unknown (Edit_at    (mkCallArg edit_at_sty_t     a))
    | "Query"      -> Unknown (Query      (mkCallArg query_sty_t       a))
    | "Goal"       -> Unknown (Goal       (mkCallArg goals_sty_t       a))
    | "Evars"      -> Unknown (Evars      (mkCallArg evars_sty_t       a))
    | "Hints"      -> Unknown (Hints      (mkCallArg hints_sty_t       a))
    | "Status"     -> Unknown (Status     (mkCallArg status_sty_t      a))
    | "Search"     -> Unknown (Search     (mkCallArg search_sty_t      a))
    | "GetOptions" -> Unknown (GetOptions (mkCallArg get_options_sty_t a))
    | "SetOptions" -> Unknown (SetOptions (mkCallArg set_options_sty_t a))
    | "MkCases"    -> Unknown (MkCases    (mkCallArg mkcases_sty_t     a))
    | "Quit"       -> Unknown (Quit       (mkCallArg quit_sty_t        a))
    | "Wait"       -> Unknown (Wait       (mkCallArg wait_sty_t        a))
    | "About"      -> Unknown (About      (mkCallArg about_sty_t       a))
    | "Init"       -> Unknown (Init       (mkCallArg init_sty_t        a))
    | "Interp"     -> Unknown (Interp     (mkCallArg interp_sty_t      a))
    | "StopWorker" -> Unknown (StopWorker (mkCallArg stop_worker_sty_t a))
    | "PrintAst"   -> Unknown (PrintAst   (mkCallArg print_ast_sty_t   a))
    | "Annotate"   -> Unknown (Annotate   (mkCallArg annotate_sty_t    a))
    | x -> raise (Marshal_error("call",PCData x)))

(** Debug printing *)

let pr_value_gen pr = function
  | Good v -> "GOOD " ^ pr v
  | Fail (id,None,str) -> "FAIL "^Stateid.to_string id^" ["^ Pp.string_of_ppcmds str ^ "]"
  | Fail (id,Some(i,j),str) ->
      "FAIL "^Stateid.to_string id^
        " ("^string_of_int i^","^string_of_int j^")["^Pp.string_of_ppcmds str^"]"
let pr_value v = pr_value_gen (fun _ -> "FIXME") v
let pr_full_value : type a. a call -> a value -> string = fun call value -> match call with
  | Add _        -> pr_value_gen (print add_rty_t        ) value
  | Edit_at _    -> pr_value_gen (print edit_at_rty_t    ) value
  | Query _      -> pr_value_gen (print query_rty_t      ) value
  | Goal _       -> pr_value_gen (print goals_rty_t      ) value
  | Evars _      -> pr_value_gen (print evars_rty_t      ) value
  | Hints _      -> pr_value_gen (print hints_rty_t      ) value
  | Status _     -> pr_value_gen (print status_rty_t     ) value
  | Search _     -> pr_value_gen (print search_rty_t     ) value
  | GetOptions _ -> pr_value_gen (print get_options_rty_t) value
  | SetOptions _ -> pr_value_gen (print set_options_rty_t) value
  | MkCases _    -> pr_value_gen (print mkcases_rty_t    ) value
  | Quit _       -> pr_value_gen (print quit_rty_t       ) value
  | Wait _       -> pr_value_gen (print wait_rty_t       ) value
  | About _      -> pr_value_gen (print about_rty_t      ) value
  | Init _       -> pr_value_gen (print init_rty_t       ) value
  | Interp _     -> pr_value_gen (print interp_rty_t     ) value
  | StopWorker _ -> pr_value_gen (print stop_worker_rty_t) value
  | PrintAst _   -> pr_value_gen (print print_ast_rty_t  ) value
  | Annotate _   -> pr_value_gen (print annotate_rty_t   ) value
let pr_call : type a. a call -> string = fun call ->
  let return what x = str_of_call call ^ " " ^ print what x in
  match call with
    | Add x        -> return add_sty_t x
    | Edit_at x    -> return edit_at_sty_t x
    | Query x      -> return query_sty_t x
    | Goal x       -> return goals_sty_t x
    | Evars x      -> return evars_sty_t x
    | Hints x      -> return hints_sty_t x
    | Status x     -> return status_sty_t x
    | Search x     -> return search_sty_t x
    | GetOptions x -> return get_options_sty_t x
    | SetOptions x -> return set_options_sty_t x
    | MkCases x    -> return mkcases_sty_t x
    | Quit x       -> return quit_sty_t x
    | Wait x       -> return wait_sty_t x
    | About x      -> return about_sty_t x
    | Init x       -> return init_sty_t x
    | Interp x     -> return interp_sty_t x
    | StopWorker x -> return stop_worker_sty_t x
    | PrintAst x   -> return print_ast_sty_t x
    | Annotate x   -> return annotate_sty_t x

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
      (Fail (Stateid.initial,Some (15,34), Pp.str "error message"))));
  document_type_encoding to_string_fmt

(* Moved from feedback.mli : This is IDE specific and we don't want to
   pollute the core with it *)

open Feedback

let of_message_level = function
  | Debug ->
      Serialize.constructor "message_level" "debug" []
  | Info -> Serialize.constructor "message_level" "info" []
  | Notice -> Serialize.constructor "message_level" "notice" []
  | Warning -> Serialize.constructor "message_level" "warning" []
  | Error -> Serialize.constructor "message_level" "error" []
let to_message_level =
  Serialize.do_match "message_level" (fun s args -> match s with
  | "debug" -> Debug
  | "info" -> Info
  | "notice" -> Notice
  | "warning" -> Warning
  | "error" -> Error
  | x -> raise Serialize.(Marshal_error("error level",PCData x)))

let of_message lvl loc msg =
  let lvl     = of_message_level lvl in
  let xloc    = of_option of_loc loc in
  let content = of_pp msg            in
  Xml_datatype.Element ("message", [], [lvl; xloc; content])

let to_message xml = match xml with
  | Xml_datatype.Element ("message", [], [lvl; xloc; content]) ->
      Message(to_message_level lvl, to_option to_loc xloc, to_pp content)
  | x -> raise (Marshal_error("message",x))

let to_feedback_content = do_match "feedback_content" (fun s a -> match s,a with
  | "addedaxiom", _ -> AddedAxiom
  | "processed", _ -> Processed
  | "processingin", [where] -> ProcessingIn (to_string where)
  | "incomplete", _ -> Incomplete
  | "complete", _ -> Complete
  | "globref", [loc; filepath; modpath; ident; ty] ->
       GlobRef(to_loc loc, to_string filepath,
         to_string modpath, to_string ident, to_string ty)
  | "globdef", [loc; ident; secpath; ty] ->
       GlobDef(to_loc loc, to_string ident, to_string secpath, to_string ty)
  | "inprogress", [n] -> InProgress (to_int n)
  | "workerstatus", [ns] ->
       let n, s = to_pair to_string to_string ns in
       WorkerStatus(n,s)
  | "custom", [loc;name;x]-> Custom (to_option to_loc loc, to_string name, x)
  | "filedependency", [from; dep] ->
      FileDependency (to_option to_string from, to_string dep)
  | "fileloaded", [dirpath; filename] ->
      FileLoaded (to_string dirpath, to_string filename)
  | "message", [x] -> to_message x
  | x,l -> raise (Marshal_error("feedback_content",PCData (x ^ " with attributes " ^ string_of_int (List.length l)))))

let of_feedback_content = function
  | AddedAxiom -> constructor "feedback_content" "addedaxiom" []
  | Processed -> constructor "feedback_content" "processed" []
  | ProcessingIn where ->
      constructor "feedback_content" "processingin" [of_string where]
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
  | InProgress n -> constructor "feedback_content" "inprogress" [of_int n]
  | WorkerStatus(n,s) ->
      constructor "feedback_content" "workerstatus"
        [of_pair of_string of_string (n,s)]
  | Custom (loc, name, x) ->
      constructor "feedback_content" "custom" [of_option of_loc loc; of_string name; x]
  | FileDependency (from, depends_on) ->
      constructor "feedback_content" "filedependency" [
        of_option of_string from;
        of_string depends_on]
  | FileLoaded (dirpath, filename) ->
      constructor "feedback_content" "fileloaded" [
        of_string dirpath;
        of_string filename ]
  | Message (l,loc,m) -> constructor "feedback_content" "message" [ of_message l loc m ]

let of_edit_or_state_id id = ["object","state"], of_stateid id

let of_feedback msg =
  let content = of_feedback_content msg.contents in
  let obj, id = of_edit_or_state_id msg.span_id in
  let route = string_of_int msg.route in
  Element ("feedback", obj @ ["route",route], [id;content])

let of_feedback msg_fmt =
  msg_format := msg_fmt; of_feedback

let to_feedback xml = match xml with
  | Element ("feedback", ["object","state";"route",route], [id;content]) -> {
      doc_id = 0;
      span_id = to_stateid id;
      route = int_of_string route;
      contents = to_feedback_content content }
  | x -> raise (Marshal_error("feedback",x))

let is_feedback = function
  | Element ("feedback", _, _) -> true
  | _ -> false

(* vim: set foldmethod=marker: *)

