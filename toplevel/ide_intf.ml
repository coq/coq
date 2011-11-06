(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Interface of calls to Coq by CoqIde *)

open Xml_parser

type xml = Xml_parser.xml

type 'a menu = 'a * (string * string) list

type goals =
  | Message of string
  | Goals of ((string menu) list * string menu) list

(** We use phantom types and GADT to protect ourselves against wild casts *)

type raw = bool
type verbose = bool

type 'a call =
  | Interp of raw * verbose * string
  | Rewind of int
  | Goal
  | Status
  | InLoadPath of string
  | MkCases of string

let interp (r,b,s) : string call = Interp (r,b,s)
let rewind i : int call = Rewind i
let goals : goals call = Goal
let status : string call = Status
let inloadpath s : bool call = InLoadPath s
let mkcases s : string list list call = MkCases s

(** * Coq answers to CoqIde *)

type location = (int * int) option (* start and end of the error *)

type 'a value =
  | Good of 'a
  | Fail of (location * string)

type handler = {
  interp : raw * verbose * string -> string;
  rewind : int -> int;
  goals : unit -> goals;
  status : unit -> string;
  inloadpath : string -> bool;
  mkcases : string -> string list list;
}

let abstract_eval_call handler explain_exn c =
  try
    let res = match c with
      | Interp (r,b,s) -> Obj.magic (handler.interp (r,b,s))
      | Rewind i -> Obj.magic (handler.rewind i)
      | Goal -> Obj.magic (handler.goals ())
      | Status -> Obj.magic (handler.status ())
      | InLoadPath s -> Obj.magic (handler.inloadpath s)
      | MkCases s -> Obj.magic (handler.mkcases s)
    in Good res
  with e ->
    let (l,str) = explain_exn e in
    Fail (l,str)

(** * XML data marshalling *)

exception Marshal_error

let massoc x l =
  try List.assoc x l
  with Not_found -> raise Marshal_error

let pcdata = function
| PCData s -> s
| _ -> raise Marshal_error

let singleton = function
| [x] -> x
| _ -> raise Marshal_error

let bool_arg tag b = if b then [tag, ""] else []

let of_bool b =
  if b then Element ("bool", ["val", "true"], [])
  else Element ("bool", ["val", "false"], [])

let to_bool = function
| Element ("bool", attrs, []) ->
  let ans = massoc "val" attrs in
  begin match ans with
  | "true" -> true
  | "false" -> false
  | _ -> raise Marshal_error
  end
| _ -> raise Marshal_error

let of_list f l =
  Element ("list", [], List.map f l)

let to_list f = function
| Element ("list", [], l) ->
  List.map f l
| _ -> raise Marshal_error

let of_value f = function
| Good x -> Element ("value", ["val", "good"], [f x])
| Fail (loc, msg) ->
  let loc = match loc with
  | None -> []
  | Some (s, e) -> [("loc_s", string_of_int s); ("loc_e", string_of_int e)]
  in
  Element ("value", ["val", "fail"] @ loc, [])

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
    let msg = pcdata (singleton l) in
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
| Status ->
  Element ("call", ["val", "status"], [])
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
    Interp (raw, vrb, pcdata (singleton l))
  | "rewind" ->
    let steps = int_of_string (massoc "steps" attrs) in
    Rewind steps
  | "goal" -> Goal
  | "status" -> Status
  | "inloadpath" -> InLoadPath (pcdata (singleton l))
  | "mkcases" -> MkCases (pcdata (singleton l))
  | _ -> raise Marshal_error
  end
| _ -> raise Marshal_error

(** * Debug printing *)

let pr_call = function
  | Interp (r,b,s) ->
    let raw = if r then "RAW" else "" in
    let verb = if b then "" else "SILENT" in
    "INTERP"^raw^verb^" ["^s^"]"
  | Rewind i -> "REWIND "^(string_of_int i)
  | Goal -> "GOALS"
  | Status -> "STATUS"
  | InLoadPath s -> "INLOADPATH "^s
  | MkCases s -> "MKCASES "^s

let pr_value_gen pr = function
  | Good v -> "GOOD " ^ pr v
  | Fail (_,str) -> "FAIL ["^str^"]"

let pr_value v = pr_value_gen (fun _ -> "") v

let pr_string s = "["^s^"]"
let pr_bool b = if b then "true" else "false"

let pr_mkcases l =
  let l = List.map (String.concat " ") l in
  "[" ^ String.concat " | " l ^ "]"

let pr_goals = function
| Message s -> "Message: " ^ s
| Goals gl ->
  let pr_menu (s, _) = s in
  let pr_goal (hyps, goal) =
    "[" ^ String.concat "; " (List.map pr_menu hyps) ^ " |- " ^ pr_menu goal ^ "]"
  in
  String.concat " " (List.map pr_goal gl)

let pr_full_value call value =
  match call with
    | Interp _ -> pr_value_gen pr_string (Obj.magic value)
    | Rewind i -> pr_value_gen string_of_int (Obj.magic value)
    | Goal -> pr_value_gen pr_goals (Obj.magic value)
    | Status -> pr_value_gen pr_string (Obj.magic value)
    | InLoadPath s -> pr_value_gen pr_bool (Obj.magic value)
    | MkCases s -> pr_value_gen pr_mkcases (Obj.magic value)
