(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors

(** The type of parsing attribute data *)
type vernac_flag_type =
  | FlagIdent of string
  | FlagString of string

type vernac_flags = vernac_flag list
and vernac_flag = (string * vernac_flag_value) CAst.t
and vernac_flag_value =
  | VernacFlagEmpty
  | VernacFlagLeaf of vernac_flag_type
  | VernacFlagList of vernac_flags

let pr_vernac_flag_leaf = function
  | FlagIdent b -> Pp.str b
  | FlagString s -> Pp.(quote (str s))

let rec pr_vernac_flag_value = let open Pp in function
  | VernacFlagEmpty -> mt ()
  | VernacFlagLeaf l -> str "=" ++ pr_vernac_flag_leaf l
  | VernacFlagList s -> surround (prlist_with_sep pr_comma pr_vernac_flag s)
and pr_vernac_flag_r (s, arguments) =
  let open Pp in
  str s ++ (pr_vernac_flag_value arguments)
and pr_vernac_flag {CAst.v} = pr_vernac_flag_r v

let warn_unsupported_attributes =
  CWarnings.create ~name:"unsupported-attributes" ~category:"parsing" ~default:CWarnings.AsError
    (fun atts ->
       let keys = List.map (fun x -> fst x.CAst.v) atts in
       let keys = List.sort_uniq String.compare keys in
       let conj = match keys with [_] -> "this attribute: " | _ -> "these attributes: " in
       Pp.(str "This command does not support " ++ str conj ++ prlist_with_sep (fun () -> strbrk ", ") str keys ++ str"."))

let unsupported_attributes = function
  | [] -> ()
  | atts ->
    let loc = List.fold_left (fun loc att -> Loc.merge_opt loc att.CAst.loc) None atts in
    warn_unsupported_attributes ?loc atts

type 'a key_parser = ?loc:Loc.t -> 'a option -> vernac_flag_value -> 'a

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

let assert_empty ?loc k v =
  if v <> VernacFlagEmpty
  then user_err ?loc Pp.(str "Attribute " ++ str k ++ str " does not accept arguments")

let error_twice ?loc ~name : 'a =
  user_err ?loc Pp.(str "Attribute for " ++ str name ++ str " specified twice.")

let assert_once ?loc ~name prev =
  if Option.has_some prev then
    error_twice ?loc ~name

let attribute_of_list (l:(string * 'a key_parser) list) : 'a option attribute =
  let rec p extra v = function
    | [] -> List.rev extra, v
    | ({CAst.v=key, attv; loc} as att) :: rem ->
      (match CList.assoc_f String.equal key l with
       | exception Not_found -> p (att::extra) v rem
       | parser ->
         let v = Some (parser ?loc v attv) in
         p extra v rem)
  in
  p [] None

let single_key_parser ~name ~key v ?loc prev args =
  assert_empty ?loc key args;
  assert_once ?loc ~name prev;
  v

let pr_possible_values ~values =
  Pp.(str "{" ++ prlist_with_sep pr_comma str (List.map fst values) ++ str "}")

(** [key_value_attribute ~key ~default ~values] parses a attribute [key=value]
  with possible [key] [value] in [values], [default] is for compatibility for users
  doing [qualif(key)] which is parsed as [qualif(key=default)] *)
let key_value_attribute ~key ~default ~(values : (string * 'a) list) : 'a option attribute =
  let parser ?loc = function
    | Some v ->
      CErrors.user_err ?loc Pp.(str "key '" ++ str key ++ str "' has been already set.")
    | None ->
      begin function
        | VernacFlagLeaf (FlagIdent b) ->
          begin match CList.assoc_f String.equal b values with
            | exception Not_found ->
              CErrors.user_err ?loc
                Pp.(str "Invalid value '" ++ str b ++ str "' for key " ++ str key ++ fnl () ++
                    str "use one of " ++ pr_possible_values ~values)
            | value -> value
          end
        | VernacFlagEmpty ->
          default
        | err ->
          CErrors.user_err ?loc
            Pp.(str "Invalid syntax " ++ pr_vernac_flag_r (key, err) ++ str ", try "
                ++ str key ++ str "=" ++ pr_possible_values ~values ++ str " instead.")
      end
  in
  attribute_of_list [key, parser]

let bool_attribute ~name : bool option attribute =
  let values = ["yes", true; "no", false] in
  key_value_attribute ~key:name ~default:true ~values

(* Variant of the [bool] attribute with only two values (bool has three). *)
let get_bool_value ?loc ~key ~default =
  function
  | VernacFlagEmpty -> default
  | VernacFlagLeaf (FlagIdent "yes") ->
    true
  | VernacFlagLeaf (FlagIdent "no") ->
    false
  | _ -> user_err ?loc Pp.(str "Attribute " ++ str key ++ str " only accepts boolean values.")

let enable_attribute ~key ~default : bool attribute =
  fun atts ->
  let this, extra = List.partition (fun {CAst.v=k, _} -> String.equal key k) atts in
  extra,
  match this with
  | [] -> default ()
  | [ {CAst.v=_, value; loc} ] -> get_bool_value ?loc ~key ~default:true value
  | _ :: {CAst.loc} :: _ ->
    (* We report the location of the 2nd item *)
    error_twice ?loc ~name:key

let qualify_attribute qual (parser:'a attribute) : 'a attribute =
  fun atts ->
    let rec extract extra qualified = function
      | [] -> List.rev extra, List.flatten (List.rev qualified)
      | {CAst.v=key,attv; loc} :: rem when String.equal key qual ->
        (match attv with
         | VernacFlagEmpty | VernacFlagLeaf _ ->
           CErrors.user_err ?loc
             Pp.(str "Malformed attribute " ++ str qual ++ str ": attribute list expected.")
         | VernacFlagList atts ->
           extract extra (atts::qualified) rem)
      | att :: rem -> extract (att::extra) qualified rem
    in
    let extra, qualified = extract [] [] atts in
    let rem, v = parser qualified in
    let rem = List.rev_map (fun rem -> CAst.make ?loc:rem.CAst.loc (qual, VernacFlagList [rem])) rem in
    let extra = List.rev_append rem extra in
    extra, v

(** [program_mode] tells that Program mode has been activated, either
    globally via [Set Program] or locally via the Program command prefix. *)

let program_mode_option_name = ["Program";"Mode"]
let program_mode = ref false

let () = let open Goptions in
  declare_bool_option
    { optdepr  = false;
      optkey   = program_mode_option_name;
      optread  = (fun () -> !program_mode);
      optwrite = (fun b -> program_mode:=b) }

let program =
  enable_attribute ~key:"program" ~default:(fun () -> !program_mode)

(* This is a bit complex as the grammar in g_vernac.mlg doesn't
   distingish between the boolean and ternary case.*)
let option_locality_parser =
  let name = "Locality" in
  attribute_of_list [
    ("local", single_key_parser ~name ~key:"local" Goptions.OptLocal);
    ("global", single_key_parser ~name ~key:"global" Goptions.OptGlobal);
    ("export", single_key_parser ~name ~key:"export" Goptions.OptExport);
  ]

let option_locality =
  option_locality_parser >>= function
  | None -> return Goptions.OptDefault
  | Some l -> return l

let hint_locality ~default =
  let open Hints in
  let name = "Locality" in
  attribute_of_list [
    ("local", single_key_parser ~name ~key:"local" Local);
    ("global", single_key_parser ~name ~key:"global" SuperGlobal);
    ("export", single_key_parser ~name ~key:"export" Export);
  ] >>= function
  | Some v -> return v
  | None -> let v = default () in return v

let really_hint_locality = hint_locality ~default:Hints.default_hint_locality

(* locality is supposed to be true when local, false when global *)
let locality =
  let name = "Locality" in
  attribute_of_list [
    ("local", single_key_parser ~name ~key:"local" true);
    ("global", single_key_parser ~name ~key:"global" false);
  ]

let ukey = "universes"

let universe_polymorphism_option_name = ["Universe"; "Polymorphism"]
let is_universe_polymorphism =
  let b = ref false in
  let () = let open Goptions in
    declare_bool_option
      { optdepr  = false;
        optkey   = universe_polymorphism_option_name;
        optread  = (fun () -> !b);
        optwrite = ((:=) b) }
  in
  fun () -> !b

let polymorphic =
  qualify_attribute ukey (bool_attribute ~name:"polymorphic") >>= function
  | Some b -> return b
  | None -> return (is_universe_polymorphism())

let template =
  qualify_attribute ukey
    (bool_attribute ~name:"template")

let deprecation_parser : Deprecation.t key_parser = fun ?loc orig args ->
  assert_once ?loc ~name:"deprecation" orig;
  match args with
  | VernacFlagList [ {CAst.v="since", VernacFlagLeaf (FlagString since)};
                     {CAst.v="note", VernacFlagLeaf (FlagString note)} ]
  | VernacFlagList [ {CAst.v="note", VernacFlagLeaf (FlagString note)};
                     {CAst.v="since", VernacFlagLeaf (FlagString since)} ] ->
    Deprecation.make ~since ~note ()
  | VernacFlagList [ {CAst.v="since", VernacFlagLeaf (FlagString since)} ] ->
    Deprecation.make ~since ()
  | VernacFlagList [ {CAst.v="note", VernacFlagLeaf (FlagString note)} ] ->
    Deprecation.make ~note ()
  |  _ -> CErrors.user_err ?loc (Pp.str "Ill formed “deprecated” attribute")

let deprecation = attribute_of_list ["deprecated",deprecation_parser]

let only_locality atts = parse locality atts

let only_polymorphism atts = parse polymorphic atts


let vernac_polymorphic_flag loc =
  CAst.make ?loc (ukey, VernacFlagList [CAst.make ?loc ("polymorphic", VernacFlagEmpty)])
let vernac_monomorphic_flag loc =
  CAst.make ?loc (ukey, VernacFlagList [CAst.make ?loc ("polymorphic", VernacFlagLeaf (FlagIdent "no"))])

let reversible = bool_attribute ~name:"reversible"

let canonical_field =
  enable_attribute ~key:"canonical" ~default:(fun () -> true)
let canonical_instance =
  enable_attribute ~key:"canonical" ~default:(fun () -> false)

let uses_parser : string key_parser = fun ?loc orig args ->
  assert_once ?loc ~name:"using" orig;
  match args with
  | VernacFlagLeaf (FlagString str) -> str
  |  _ -> CErrors.user_err ?loc (Pp.str "Ill formed \"using\" attribute")

let using = attribute_of_list ["using",uses_parser]

let process_typing_att ?loc ~typing_flags att disable =
  let enable = not disable in
  match att with
  | "universes" ->
    { typing_flags with
      Declarations.check_universes = enable
    }
  | "guard" ->
    { typing_flags with
      Declarations.check_guarded = enable
    }
  | "positivity" ->
    { typing_flags with
      Declarations.check_positive = enable
    }
  | att ->
    CErrors.user_err ?loc Pp.(str "Unknown “typing” attribute: " ++ str att)

let process_typing_disable ?loc ~key = function
  | VernacFlagEmpty | VernacFlagLeaf (FlagIdent "yes") ->
    true
  | VernacFlagLeaf (FlagIdent "no") ->
    false
  | _ ->
    CErrors.user_err ?loc Pp.(str "Ill-formed attribute value, must be " ++ str key ++ str "={yes, no}")

let typing_flags_parser : Declarations.typing_flags key_parser = fun ?loc orig args ->
  let rec flag_parser typing_flags = function
    | [] -> typing_flags
    | {CAst.v=typing_att, disable; loc} :: rest ->
      let disable = process_typing_disable ?loc ~key:typing_att disable in
      let typing_flags = process_typing_att ?loc ~typing_flags typing_att disable in
      flag_parser typing_flags rest
  in
  match args with
  | VernacFlagList atts ->
    let typing_flags = Global.typing_flags () in
    flag_parser typing_flags atts
  | att ->
    CErrors.user_err ?loc Pp.(str "Ill-formed “typing” attribute: " ++ pr_vernac_flag_value att)

let typing_flags =
  attribute_of_list ["bypass_check", typing_flags_parser]

let raw_attributes : _ attribute = fun flags -> [], flags
