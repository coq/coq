(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Libnames
open Tac2expr
open Tac2ffi

type global_data = {
  gdata_expr : glb_tacexpr;
  gdata_type : type_scheme;
  gdata_mutable : bool;
}

type constructor_data = {
  cdata_prms : int;
  cdata_type : type_constant;
  cdata_args : int glb_typexpr list;
  cdata_indx : int option;
}

type projection_data = {
  pdata_prms : int;
  pdata_type : type_constant;
  pdata_ptyp : int glb_typexpr;
  pdata_mutb : bool;
  pdata_indx : int;
}

type ltac_state = {
  ltac_tactics : global_data KNmap.t;
  ltac_constructors : constructor_data KNmap.t;
  ltac_projections : projection_data KNmap.t;
  ltac_types : glb_quant_typedef KNmap.t;
  ltac_aliases : raw_tacexpr KNmap.t;
}

let empty_state = {
  ltac_tactics = KNmap.empty;
  ltac_constructors = KNmap.empty;
  ltac_projections = KNmap.empty;
  ltac_types = KNmap.empty;
  ltac_aliases = KNmap.empty;
}

let ltac_state = Summary.ref empty_state ~name:"ltac2-state"

let define_global kn e =
  let state = !ltac_state in
  ltac_state := { state with ltac_tactics = KNmap.add kn e state.ltac_tactics }

let interp_global kn =
  let data = KNmap.find kn ltac_state.contents.ltac_tactics in
  data

let define_constructor kn t =
  let state = !ltac_state in
  ltac_state := { state with ltac_constructors = KNmap.add kn t state.ltac_constructors }

let interp_constructor kn = KNmap.find kn ltac_state.contents.ltac_constructors

let define_projection kn t =
  let state = !ltac_state in
  ltac_state := { state with ltac_projections = KNmap.add kn t state.ltac_projections }

let interp_projection kn = KNmap.find kn ltac_state.contents.ltac_projections

let define_type kn e =
  let state = !ltac_state in
  ltac_state := { state with ltac_types = KNmap.add kn e state.ltac_types }

let interp_type kn = KNmap.find kn ltac_state.contents.ltac_types

let define_alias kn tac =
  let state = !ltac_state in
  ltac_state := { state with ltac_aliases = KNmap.add kn tac state.ltac_aliases }

let interp_alias kn = KNmap.find kn ltac_state.contents.ltac_aliases

module ML =
struct
  type t = ml_tactic_name
  let compare n1 n2 =
    let c = String.compare n1.mltac_plugin n2.mltac_plugin in
    if Int.equal c 0 then String.compare n1.mltac_tactic n2.mltac_tactic
    else c
end

module MLMap = Map.Make(ML)

let primitive_map = ref MLMap.empty

let define_primitive name f = primitive_map := MLMap.add name f !primitive_map
let interp_primitive name = MLMap.find name !primitive_map

(** Name management *)

module FullPath =
struct
  type t = full_path
  let equal = eq_full_path
  let to_string = string_of_path
  let repr sp =
    let dir,id = repr_path sp in
    id, (DirPath.repr dir)
end

type tacref = Tac2expr.tacref =
| TacConstant of ltac_constant
| TacAlias of ltac_alias

module TacRef =
struct
type t = tacref
let compare r1 r2 = match r1, r2 with
| TacConstant c1, TacConstant c2 -> KerName.compare c1 c2
| TacAlias c1, TacAlias c2 -> KerName.compare c1 c2
| TacConstant _, TacAlias _ -> -1
| TacAlias _, TacConstant _ -> 1

let equal r1 r2 = compare r1 r2 == 0

end

module KnTab = Nametab.Make(FullPath)(KerName)
module RfTab = Nametab.Make(FullPath)(TacRef)
module RfMap = Map.Make(TacRef)

type nametab = {
  tab_ltac : RfTab.t;
  tab_ltac_rev : full_path RfMap.t;
  tab_cstr : KnTab.t;
  tab_cstr_rev : full_path KNmap.t;
  tab_type : KnTab.t;
  tab_type_rev : full_path KNmap.t;
  tab_proj : KnTab.t;
  tab_proj_rev : full_path KNmap.t;
}

let empty_nametab = {
  tab_ltac = RfTab.empty;
  tab_ltac_rev = RfMap.empty;
  tab_cstr = KnTab.empty;
  tab_cstr_rev = KNmap.empty;
  tab_type = KnTab.empty;
  tab_type_rev = KNmap.empty;
  tab_proj = KnTab.empty;
  tab_proj_rev = KNmap.empty;
}

let nametab = Summary.ref empty_nametab ~name:"ltac2-nametab"

let push_ltac vis sp kn =
  let tab = !nametab in
  let tab_ltac = RfTab.push vis sp kn tab.tab_ltac in
  let tab_ltac_rev = RfMap.add kn sp tab.tab_ltac_rev in
  nametab := { tab with tab_ltac; tab_ltac_rev }

let locate_ltac qid =
  let tab = !nametab in
  RfTab.locate qid tab.tab_ltac

let locate_extended_all_ltac qid =
  let tab = !nametab in
  RfTab.find_prefixes qid tab.tab_ltac

let shortest_qualid_of_ltac kn =
  let tab = !nametab in
  let sp = RfMap.find kn tab.tab_ltac_rev in
  RfTab.shortest_qualid Id.Set.empty sp tab.tab_ltac

let push_constructor vis sp kn =
  let tab = !nametab in
  let tab_cstr = KnTab.push vis sp kn tab.tab_cstr in
  let tab_cstr_rev = KNmap.add kn sp tab.tab_cstr_rev in
  nametab := { tab with tab_cstr; tab_cstr_rev }

let locate_constructor qid =
  let tab = !nametab in
  KnTab.locate qid tab.tab_cstr

let locate_extended_all_constructor qid =
  let tab = !nametab in
  KnTab.find_prefixes qid tab.tab_cstr

let shortest_qualid_of_constructor kn =
  let tab = !nametab in
  let sp = KNmap.find kn tab.tab_cstr_rev in
  KnTab.shortest_qualid Id.Set.empty sp tab.tab_cstr

let push_type vis sp kn =
  let tab = !nametab in
  let tab_type = KnTab.push vis sp kn tab.tab_type in
  let tab_type_rev = KNmap.add kn sp tab.tab_type_rev in
  nametab := { tab with tab_type; tab_type_rev }

let locate_type qid =
  let tab = !nametab in
  KnTab.locate qid tab.tab_type

let locate_extended_all_type qid =
  let tab = !nametab in
  KnTab.find_prefixes qid tab.tab_type

let shortest_qualid_of_type ?loc kn =
  let tab = !nametab in
  let sp = KNmap.find kn tab.tab_type_rev in
  KnTab.shortest_qualid ?loc Id.Set.empty sp tab.tab_type

let push_projection vis sp kn =
  let tab = !nametab in
  let tab_proj = KnTab.push vis sp kn tab.tab_proj in
  let tab_proj_rev = KNmap.add kn sp tab.tab_proj_rev in
  nametab := { tab with tab_proj; tab_proj_rev }

let locate_projection qid =
  let tab = !nametab in
  KnTab.locate qid tab.tab_proj

let locate_extended_all_projection qid =
  let tab = !nametab in
  KnTab.find_prefixes qid tab.tab_proj

let shortest_qualid_of_projection kn =
  let tab = !nametab in
  let sp = KNmap.find kn tab.tab_proj_rev in
  KnTab.shortest_qualid Id.Set.empty sp tab.tab_proj

type 'a or_glb_tacexpr =
| GlbVal of 'a
| GlbTacexpr of glb_tacexpr

type environment = {
  env_ist : valexpr Id.Map.t;
}

type ('a, 'b, 'r) intern_fun = Genintern.glob_sign -> 'a -> 'b * 'r glb_typexpr

type ('a, 'b) ml_object = {
  ml_intern : 'r. (raw_tacexpr, glb_tacexpr, 'r) intern_fun -> ('a, 'b or_glb_tacexpr, 'r) intern_fun;
  ml_subst : Mod_subst.substitution -> 'b -> 'b;
  ml_interp : environment -> 'b -> valexpr Proofview.tactic;
  ml_print : Environ.env -> 'b -> Pp.t;
}

module MLTypeObj =
struct
  type ('a, 'b) t = ('a, 'b) ml_object
end

module MLType = Tac2dyn.ArgMap(MLTypeObj)

let ml_object_table = ref MLType.empty

let define_ml_object t tpe =
  ml_object_table := MLType.add t (MLType.Pack tpe) !ml_object_table

let interp_ml_object t =
  try
    let MLType.Pack ans = MLType.find t !ml_object_table in
    ans
  with Not_found ->
    CErrors.anomaly Pp.(str "Unknown object type " ++ str (Tac2dyn.Arg.repr t))

(** Absolute paths *)

let coq_prefix =
  MPfile (DirPath.make (List.map Id.of_string ["Init"; "Ltac2"]))

let std_prefix =
  MPfile (DirPath.make (List.map Id.of_string ["Std"; "Ltac2"]))

let ltac1_prefix =
  MPfile (DirPath.make (List.map Id.of_string ["Ltac1"; "Ltac2"]))

(** Generic arguments *)

let wit_ltac2 = Genarg.make0 "ltac2:value"
let wit_ltac2_quotation = Genarg.make0 "ltac2:quotation"
let () = Geninterp.register_val0 wit_ltac2 None
let () = Geninterp.register_val0 wit_ltac2_quotation None

let is_constructor qid =
  let (_, id) = repr_qualid qid in
  let id = Id.to_string id in
  assert (String.length id > 0);
  match id with
  | "true" | "false" -> true (* built-in constructors *)
  | _ ->
    match id.[0] with
    | 'A'..'Z' -> true
    | _ -> false
