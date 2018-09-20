(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Vernacexpr

let unsupported_attributes ?loc = function
  | [] -> ()
  | atts ->
    let keys = List.map fst atts in
    let keys = List.sort_uniq String.compare keys in
    let conj = match keys with [_] -> "this attribute: " | _ -> "these attributes: " in
    user_err ?loc Pp.(str "This command does not support " ++ str conj ++ prlist str keys ++ str".")

type 'a key_parser = 'a option -> Vernacexpr.vernac_flag_value -> 'a

type 'a attribute = ('a -> Vernacexpr.vernac_flag_value -> 'a) CString.Map.t * 'a

let parse_drop_extra (p,v:'a attribute) (atts:vernac_flags) : 'a =
  List.fold_left (fun v (k,args) ->
      match CString.Map.find k p with
      | exception Not_found -> v
      | parser -> parser v args)
    v atts

let parse_with_extra (p,v:'a attribute) (atts:vernac_flags) : 'a * vernac_flags =
  let v, extra = List.fold_left (fun (v,extra) (k,args as att) ->
      match CString.Map.find k p with
      | exception Not_found -> (v,att::extra)
      | parser -> (parser v args, extra))
      (v,[]) atts
  in
  v, List.rev extra

let parse (p:'a attribute) atts : 'a =
  let v, extra = parse_with_extra p atts in
  unsupported_attributes extra;
  v

module Notations = struct

  let (++) (p1,v1:'a attribute) (p2,v2:'b attribute) : ('a*'b) attribute =
    let p = CString.Map.merge (fun key p1 p2 -> match p1, p2 with
        | Some p1, None -> Some (fun (x,y) args -> (p1 x args, y))
        | None, Some p2 -> Some (fun (x,y) args -> (x, p2 y args))
        | None, None -> None
        | Some _, Some _ ->
          anomaly Pp.(str "Attribute collision on " ++ str key))
        p1 p2
    in
    p, (v1, v2)

end
open Notations

type deprecation = { since : string option ; note : string option }

let mk_deprecation ?(since=None) ?(note=None) () =
  { since ; note }

type t = {
  locality : bool option;
  polymorphic : bool;
  template : bool option;
  program : bool;
  deprecated : deprecation option;
}

let assert_empty k v =
  if v <> VernacFlagEmpty
  then user_err Pp.(str "Attribute " ++ str k ++ str " does not accept arguments")

let assert_once ~name prev =
  if Option.has_some prev then
    user_err Pp.(str "Attribute for " ++ str name ++ str " specified twice.")

let attribute_of_list (l:(string * 'a key_parser) list) : 'a option attribute =
  List.fold_left (fun acc (k,p) -> CString.Map.add k (fun prev args -> Some (p prev args)) acc)
    CString.Map.empty l, None

let single_key_parser ~name ~key v prev args =
  assert_empty key args;
  assert_once ~name prev;
  v

let bool_attribute ~name ~on ~off : bool option attribute =
  attribute_of_list [(on, single_key_parser ~name ~key:on true);
               (off, single_key_parser ~name ~key:off false)]

let polymorphic = bool_attribute ~name:"Polymorphism" ~on:"polymorphic" ~off:"monomorphic"

let program = bool_attribute ~name:"Program mode" ~on:"program" ~off:"noprogram"

let locality = bool_attribute ~name:"Locality" ~on:"local" ~off:"global"

let template = bool_attribute ~name:"Template" ~on:"template" ~off:"notemplate"

let deprecation_parser : deprecation key_parser = fun orig args ->
  assert_once ~name:"deprecation" orig;
  match args with
  | VernacFlagList [ "since", VernacFlagLeaf since ; "note", VernacFlagLeaf note ]
  | VernacFlagList [ "note", VernacFlagLeaf note ; "since", VernacFlagLeaf since ] ->
    let since = Some since and note = Some note in
    mk_deprecation ~since ~note ()
  | VernacFlagList [ "since", VernacFlagLeaf since ] ->
    let since = Some since in
    mk_deprecation ~since ()
  | VernacFlagList [ "note", VernacFlagLeaf note ] ->
    let note = Some note in
    mk_deprecation ~note ()
  |  _ -> CErrors.user_err (Pp.str "Ill formed “deprecated” attribute")

let deprecation = attribute_of_list ["deprecated",deprecation_parser]

let attributes_of_flags f =
  let (((locality, template), deprecated), polymorphic), program =
    parse (locality ++ template ++ deprecation ++ polymorphic ++ program) f
  in
  let polymorphic = Option.default (Flags.is_universe_polymorphism()) polymorphic in
  let program = Option.default (Flags.is_program_mode()) program in
  { polymorphic; program; locality; template; deprecated }

let only_locality atts = parse locality atts

let only_polymorphism atts =
  let att = parse polymorphic atts in
  Option.default (Flags.is_universe_polymorphism ()) att
