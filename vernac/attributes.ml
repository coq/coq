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

module Store = Store.Make()

type 'a flag_parser = 'a option -> ?loc:Loc.t -> vernac_flag_value -> 'a

type 'a attribute = 'a Store.field

type attr_parser =
    Parser : string (* name of the attribute *) * 'a attribute * 'a flag_parser -> attr_parser

let known_parsers : attr_parser CString.Map.t ref = ref CString.Map.empty

type t = Store.t

let read field atts = Store.get atts field

let check_parser_collision new_parsers =
  CString.Map.iter (fun key _ ->
      if CString.Map.mem key !known_parsers
      then anomaly ~label:"register_attribute"
          Pp.(str "Double registration for attribute key " ++ str key))
    new_parsers

let register_attribute ~name (parsers : 'a flag_parser CString.Map.t) =
  check_parser_collision parsers;
  let field : 'a Store.field = Store.field () in
  known_parsers := CString.Map.fold (fun key parser known_parsers ->
      CString.Map.add key (Parser (name,field,parser)) known_parsers)
      parsers !known_parsers;
  field

let once_parser ~name parser previous ?loc v =
  match previous with
  | Some _ -> user_err ?loc Pp.(str name ++ str " specified twice.")
  | None -> parser ?loc v

let assert_empty ?loc k v =
  if v <> VernacFlagEmpty
  then user_err ?loc Pp.(str "Attribute " ++ str k ++ str " does not accept arguments")

let empty_parser ~name x =
  once_parser ~name (fun ?loc v -> assert_empty ?loc name v; x)

let make_empty_parsers ~name assocs =
  List.fold_left (fun parsers (k,x) ->
      CString.Map.add k (empty_parser ~name x) parsers)
    CString.Map.empty assocs

let template =
  let name = "Templateness" in
  let parsers = make_empty_parsers ~name [("template", true) ; ("notemplate", false)] in
  read (register_attribute ~name parsers)

let locality =
  let name = "Locality" in
  let parsers = make_empty_parsers ~name [("local", true) ; ("global", false)] in
  read (register_attribute ~name parsers)

type deprecation = { since : string option ; note : string option }

let mk_deprecation ?(since=None) ?(note=None) () =
  { since ; note }

let deprecated =
  let parser ?loc =
    let open CAst in
    function
    | VernacFlagList [ {v="since", VernacFlagLeaf since} ; {v="note", VernacFlagLeaf note} ]
    | VernacFlagList [ {v="note", VernacFlagLeaf note} ; {v="since", VernacFlagLeaf since} ] ->
      let since = Some since and note = Some note in
      mk_deprecation ~since ~note ()
    | VernacFlagList [ {v="since", VernacFlagLeaf since} ] ->
      let since = Some since in
      mk_deprecation ~since ()
    | VernacFlagList [ {v="note", VernacFlagLeaf note} ] ->
      let note = Some note in
      mk_deprecation ~note ()
    |  _ -> CErrors.user_err ?loc (Pp.str "Ill formed “deprecated” attribute")
  in
  let name = "Deprecation" in
  read (register_attribute ~name (CString.Map.singleton "deprecated" (once_parser ~name parser)))

let program =
  let name = "Program mode" in
  let parsers = make_empty_parsers ~name [("program", true)] in
  read (register_attribute ~name parsers)

let polymorphic_att =
  let name = "Polymorphism" in
  let parsers = make_empty_parsers ~name [("polymorphic", true) ; ("monomorphic", false)] in
  register_attribute ~name parsers

let mk_atts ?(polymorphic=false) () =
  Store.set Store.empty polymorphic_att polymorphic

let set_polymorphic atts polymorphic = Store.set atts polymorphic_att polymorphic

let polymorphic atts =
  Option.get (read polymorphic_att atts)

let parse_one_attribute atts {CAst.v=k, v; loc} =
  match CString.Map.find k !known_parsers with
  | exception Not_found -> user_err ?loc Pp.(str "Unknown attribute " ++ str k)
  | Parser (name, field, parser) ->
    let v = parser (Store.get atts field) ?loc v in
    Store.set atts field v

let attributes_of_flags f atts =
  (* We need to do a small dance to detect the presence of a
     polymorphism flag despite always setting the attribute in
     [mk_atts]. *)
  let orig_poly = polymorphic atts in
  let atts = Store.remove atts polymorphic_att in
  let atts = List.fold_left parse_one_attribute atts f in
  let poly_attr = read polymorphic_att atts in
  let atts = Store.set atts polymorphic_att (Option.default orig_poly poly_attr) in
  poly_attr, atts
