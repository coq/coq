(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors

(** The type of parsing attribute data *)
type vernac_flags = vernac_flag list
and vernac_flag = string * vernac_flag_value
and vernac_flag_value =
  | VernacFlagEmpty
  | VernacFlagLeaf of string
  | VernacFlagList of vernac_flags

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

let assert_empty k v =
  if v <> VernacFlagEmpty
  then user_err Pp.(str "Attribute " ++ str k ++ str " does not accept arguments")

let error_twice ~name : 'a =
  user_err Pp.(str "Attribute for " ++ str name ++ str " specified twice.")

let assert_once ~name prev =
  if Option.has_some prev then
    error_twice ~name

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

(* Variant of the [bool] attribute with only two values (bool has three). *)
let get_bool_value ~key ~default =
  function
  | VernacFlagEmpty -> default
  | VernacFlagList [ "true", VernacFlagEmpty ] -> true
  | VernacFlagList [ "false", VernacFlagEmpty ] -> false
  | _ -> user_err Pp.(str "Attribute " ++ str key ++ str " only accepts boolean values.")

let enable_attribute ~key ~default : bool attribute =
  fun atts ->
  let default = default () in
  let this, extra = List.partition (fun (k, _) -> String.equal key k) atts in
  extra,
  match this with
  | [] -> default
  | [ _, value ] -> get_bool_value ~key ~default:true value
  | _ -> error_twice ~name:key

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

(** [program_mode] tells that Program mode has been activated, either
    globally via [Set Program] or locally via the Program command prefix. *)

let program_mode_option_name = ["Program";"Mode"]
let program_mode = ref false

let () = let open Goptions in
  declare_bool_option
    { optdepr  = false;
      optname  = "use of the program extension";
      optkey   = program_mode_option_name;
      optread  = (fun () -> !program_mode);
      optwrite = (fun b -> program_mode:=b) }

let program =
  enable_attribute ~key:"program" ~default:(fun () -> !program_mode)

let locality = bool_attribute ~name:"Locality" ~on:"local" ~off:"global"

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
  let () = let open Goptions in
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

let template =
  universe_transform ~warn_unqualified:true >>
  qualify_attribute ukey (bool_attribute ~name:"Template" ~on:"template" ~off:"notemplate")

let polymorphic =
  universe_transform ~warn_unqualified:true >>
  qualify_attribute ukey polymorphic_base

let deprecation_parser : Deprecation.t key_parser = fun orig args ->
  assert_once ~name:"deprecation" orig;
  match args with
  | VernacFlagList [ "since", VernacFlagLeaf since ; "note", VernacFlagLeaf note ]
  | VernacFlagList [ "note", VernacFlagLeaf note ; "since", VernacFlagLeaf since ] ->
    Deprecation.make ~since ~note ()
  | VernacFlagList [ "since", VernacFlagLeaf since ] ->
    Deprecation.make ~since ()
  | VernacFlagList [ "note", VernacFlagLeaf note ] ->
    Deprecation.make ~note ()
  |  _ -> CErrors.user_err (Pp.str "Ill formed “deprecated” attribute")

let deprecation = attribute_of_list ["deprecated",deprecation_parser]

let only_locality atts = parse locality atts

let only_polymorphism atts = parse polymorphic atts


let vernac_polymorphic_flag = ukey, VernacFlagList ["polymorphic", VernacFlagEmpty]
let vernac_monomorphic_flag = ukey, VernacFlagList ["monomorphic", VernacFlagEmpty]

let canonical =
  enable_attribute ~key:"canonical" ~default:(fun () -> true)
