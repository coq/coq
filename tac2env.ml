(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open CErrors
open Util
open Genarg
open Names
open Libnames
open Tac2expr

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
  ltac_tactics : (glb_tacexpr * type_scheme) KNmap.t;
  ltac_constructors : constructor_data KNmap.t;
  ltac_projections : projection_data KNmap.t;
  ltac_types : glb_quant_typedef KNmap.t;
}

let empty_state = {
  ltac_tactics = KNmap.empty;
  ltac_constructors = KNmap.empty;
  ltac_projections = KNmap.empty;
  ltac_types = KNmap.empty;
}

let ltac_state = Summary.ref empty_state ~name:"ltac2-state"

(** Get a dynamic value from syntactical value *)
let rec eval_pure = function
| GTacAtm (AtmInt n) -> ValInt n
| GTacRef kn ->
  let (e, _) =
    try KNmap.find kn ltac_state.contents.ltac_tactics
    with Not_found -> assert false
  in
  eval_pure e
| GTacFun (na, e) ->
  ValCls { clos_env = Id.Map.empty; clos_var = na; clos_exp = e }
| GTacCst (_, n, []) -> ValInt n
| GTacCst (_, n, el) -> ValBlk (n, Array.map_of_list eval_pure el)
| GTacOpn (kn, el) -> ValOpn (kn, Array.map_of_list eval_pure el)
| GTacAtm (AtmStr _) | GTacArr _ | GTacLet _ | GTacVar _ | GTacSet _
| GTacApp _ | GTacCse _ | GTacPrj _ | GTacPrm _ | GTacExt _ | GTacWth _ ->
  anomaly (Pp.str "Term is not a syntactical value")

let define_global kn e =
  let state = !ltac_state in
  ltac_state := { state with ltac_tactics = KNmap.add kn e state.ltac_tactics }

let interp_global kn =
  let (e, t) = KNmap.find kn ltac_state.contents.ltac_tactics in
  (e, eval_pure e, t)

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
| TacConstructor of ltac_constructor

module TacRef =
struct
type t = tacref
let equal r1 r2 = match r1, r2 with
| TacConstant c1, TacConstant c2 -> KerName.equal c1 c2
| TacConstructor c1, TacConstructor c2 -> KerName.equal c1 c2
| _ -> false
end

module KnTab = Nametab.Make(FullPath)(KerName)
module RfTab = Nametab.Make(FullPath)(TacRef)

type nametab = {
  tab_ltac : RfTab.t;
  tab_ltac_rev : full_path KNmap.t * full_path KNmap.t;
  tab_type : KnTab.t;
  tab_type_rev : full_path KNmap.t;
  tab_proj : KnTab.t;
  tab_proj_rev : full_path KNmap.t;
}

let empty_nametab = {
  tab_ltac = RfTab.empty;
  tab_ltac_rev = (KNmap.empty, KNmap.empty);
  tab_type = KnTab.empty;
  tab_type_rev = KNmap.empty;
  tab_proj = KnTab.empty;
  tab_proj_rev = KNmap.empty;
}

let nametab = Summary.ref empty_nametab ~name:"ltac2-nametab"

let push_ltac vis sp kn =
  let tab = !nametab in
  let tab_ltac = RfTab.push vis sp kn tab.tab_ltac in
  let (constant_map, constructor_map) = tab.tab_ltac_rev in
  let tab_ltac_rev = match kn with
  | TacConstant c -> (KNmap.add c sp constant_map, constructor_map)
  | TacConstructor c -> (constant_map, KNmap.add c sp constructor_map)
  in
  nametab := { tab with tab_ltac; tab_ltac_rev }

let locate_ltac qid =
  let tab = !nametab in
  RfTab.locate qid tab.tab_ltac

let locate_extended_all_ltac qid =
  let tab = !nametab in
  RfTab.find_prefixes qid tab.tab_ltac

let shortest_qualid_of_ltac kn =
  let tab = !nametab in
  let sp = match kn with
  | TacConstant c -> KNmap.find c (fst tab.tab_ltac_rev)
  | TacConstructor c -> KNmap.find c (snd tab.tab_ltac_rev)
  in
  RfTab.shortest_qualid Id.Set.empty sp tab.tab_ltac

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

let shortest_qualid_of_type kn =
  let tab = !nametab in
  let sp = KNmap.find kn tab.tab_type_rev in
  KnTab.shortest_qualid Id.Set.empty sp tab.tab_type

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

type 'a ml_object = {
  ml_type : type_constant;
  ml_interp : environment -> 'a -> Geninterp.Val.t Proofview.tactic;
}

module MLTypeObj =
struct
  type ('a, 'b, 'c) obj = 'b ml_object
  let name = "ltac2_ml_type"
  let default _ = None
end

module MLType = Genarg.Register(MLTypeObj)

let define_ml_object t tpe = MLType.register0 t tpe
let interp_ml_object t = MLType.obj t

(** Absolute paths *)

let coq_prefix =
  MPfile (DirPath.make (List.map Id.of_string ["Init"; "ltac2"; "Coq"]))

(** Generic arguments *)

let wit_ltac2 = Genarg.make0 "ltac2"
