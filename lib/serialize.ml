(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Xml_datatype

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

let of_union (f : 'a -> xml) (g : 'b -> xml) : ('a,'b) CSig.union -> xml = function
  | CSig.Inl x -> Element ("union", ["val","in_l"], [f x])
  | CSig.Inr x -> Element ("union", ["val","in_r"], [g x])
let to_union (f : xml -> 'a) (g : xml -> 'b) : xml -> ('a,'b) CSig.union = function
  | Element ("union", ["val","in_l"], [x]) -> CSig.Inl (f x)
  | Element ("union", ["val","in_r"], [x]) -> CSig.Inr (g x)
  | _ -> raise Marshal_error

(** More elaborate types *)

let of_edit_id i = Element ("edit_id",["val",string_of_int i],[])
let to_edit_id = function
  | Element ("edit_id",["val",i],[]) ->
      let id = int_of_string i in
      assert (id <= 0 );
      id
  | _ -> raise Marshal_error

let of_loc loc =
  let start, stop = Loc.unloc loc in
  Element ("loc",[("start",string_of_int start);("stop",string_of_int stop)],[])
let to_loc xml =
  match xml with
  | Element ("loc", l,[]) ->
      (try
        let start = massoc "start" l in
        let stop = massoc "stop" l in
        Loc.make_loc (int_of_string start, int_of_string stop)
      with Not_found | Invalid_argument _ -> raise Marshal_error)
  | _ -> raise Marshal_error

