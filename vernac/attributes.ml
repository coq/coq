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

let unsupported_attributes = function
  | [] -> ()
  | atts ->
    let keys = List.map fst atts in
    let keys = List.sort_uniq String.compare keys in
    let conj = match keys with [_] -> "this attribute: " | _ -> "these attributes: " in
    user_err Pp.(str "This command does not support " ++ str conj ++ prlist str keys ++ str".")

type 'a key_parser = 'a option -> vernac_flag_value -> 'a

type 'a attribute = vernac_flags -> vernac_flags * 'a

let parse_with_extra (p:'a attribute) (atts:vernac_flags) : vernac_flags * 'a =
  p atts

let parse_drop_extra att atts =
  snd (parse_with_extra att atts)

let parse (p:'a attribute) atts : 'a =
  let extra, v = parse_with_extra p atts in
  unsupported_attributes extra;
  v

let make_attribute x = x

module Notations = struct

  type 'a t = 'a attribute

  let return x = fun atts -> atts, x

  let (>>=) att f =
    fun atts ->
      let atts, v = att atts in
      f v atts

  let (>>) p1 p2 =
    fun atts ->
      let atts, () = p1 atts in
      p2 atts

  let map f att =
    fun atts ->
      let atts, v = att atts in
      atts, f v

  let (++) (p1:'a attribute) (p2:'b attribute) : ('a*'b) attribute =
    fun atts ->
      let atts, v1 = p1 atts in
      let atts, v2 = p2 atts in
      atts, (v1, v2)

end
open Notations

type deprecation = { since : string option ; note : string option }

let mk_deprecation ?(since=None) ?(note=None) () =
  { since ; note }

type t = {
  locality : bool option;
  (* check_guard : bool option; *)
  (* check_positivity : bool option; *)
  (* check_universes : bool option; *)
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
  let rec p extra v = function
    | [] -> List.rev extra, v
    | (key, attv as att) :: rem ->
      (match CList.assoc_f String.equal key l with
       | exception Not_found -> p (att::extra) v rem
       | parser ->
         let v = Some (parser v attv) in
         p extra v rem)
  in
  p [] None

let single_key_parser ~name ~key v prev args =
  assert_empty key args;
  assert_once ~name prev;
  v

let bool_attribute ~name ~on ~off : bool option attribute =
  attribute_of_list [(on, single_key_parser ~name ~key:on true);
               (off, single_key_parser ~name ~key:off false)]

let qualify_attribute qual (parser:'a attribute) : 'a attribute =
  fun atts ->
    let rec extract extra qualified = function
      | [] -> List.rev extra, List.flatten (List.rev qualified)
      | (key,attv) :: rem when String.equal key qual ->
        (match attv with
         | VernacFlagEmpty | VernacFlagLeaf _ ->
           CErrors.user_err ~hdr:"qualified_attribute"
             Pp.(str "Malformed attribute " ++ str qual ++ str ": attribute list expected.")
         | VernacFlagList atts ->
           extract extra (atts::qualified) rem)
      | att :: rem -> extract (att::extra) qualified rem
    in
    let extra, qualified = extract [] [] atts in
    let rem, v = parser qualified in
    let extra = if rem = [] then extra else (qual, VernacFlagList rem) :: extra in
    extra, v

let program_opt = bool_attribute ~name:"Program mode" ~on:"program" ~off:"noprogram"

let program = program_opt >>= function
  | Some b -> return b
  | None -> return (Flags.is_program_mode())

let locality = bool_attribute ~name:"Locality" ~on:"local" ~off:"global"

let check_guard = bool_attribute ~name:"Check Guard" ~on:"check_guarded" ~off:"assume_guarded"

let check_positivity = bool_attribute ~name:"Check Positivity" ~on:"check_positive" ~off:"assume_positive"

let check_universes = bool_attribute ~name:"Check Universes" ~on:"check_universes" ~off:"type_in_type"

let warn_unqualified_univ_attr =
  CWarnings.create ~name:"unqualified-univ-attr" ~category:"deprecated"
    (fun key -> Pp.(str "Attribute " ++ str key ++
                    str " should be qualified as \"universes("++str key++str")\"."))

let ukey = "universes"
let universe_transform ~warn_unqualified : unit attribute =
  fun atts ->
    let atts = List.map (fun (key,_ as att) ->
        match key with
        | "polymorphic" | "monomorphic"
        | "template" | "notemplate" ->
          if warn_unqualified then warn_unqualified_univ_attr key;
          ukey, VernacFlagList [att]
        | _ -> att) atts
    in
    atts, ()

let universe_polymorphism_option_name = ["Universe"; "Polymorphism"]
let is_universe_polymorphism =
  let b = ref false in
  let _ = let open Goptions in
    declare_bool_option
      { optdepr  = false;
        optname  = "universe polymorphism";
        optkey   = universe_polymorphism_option_name;
        optread  = (fun () -> !b);
        optwrite = ((:=) b) }
  in
  fun () -> !b

let polymorphic_base =
  bool_attribute ~name:"Polymorphism" ~on:"polymorphic" ~off:"monomorphic" >>= function
  | Some b -> return b
  | None -> return (is_universe_polymorphism())

let polymorphic_nowarn =
  universe_transform ~warn_unqualified:false >>
  qualify_attribute ukey polymorphic_base

let universe_poly_template =
  let template = bool_attribute ~name:"Template" ~on:"template" ~off:"notemplate" in
  universe_transform ~warn_unqualified:true >>
  qualify_attribute ukey (polymorphic_base ++ template)

let polymorphic =
  universe_transform ~warn_unqualified:true >>
  qualify_attribute ukey polymorphic_base

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
  let ((locality, deprecated), (polymorphic, template)), program =
    parse (locality ++ deprecation ++ universe_poly_template ++ program) f
  in
  { polymorphic; program; locality; template; deprecated }
  (* let (((((locality, check_guard), check_positivity), check_universes), deprecated), (polymorphic, template)), program = *)
  (*   parse (locality ++ check_guard ++ check_positivity ++ check_universes ++ deprecation ++ universe_poly_template ++ program) f *)
  (* in *)
  (* { locality; check_guard; check_positivity; check_universes; deprecated; polymorphic; template; program } *)

let only_locality atts = parse locality atts

let only_polymorphism atts = parse polymorphic atts


let vernac_polymorphic_flag = ukey, VernacFlagList ["polymorphic", VernacFlagEmpty]
let vernac_monomorphic_flag = ukey, VernacFlagList ["monomorphic", VernacFlagEmpty]
