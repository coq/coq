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

type ltac_constant = KerName.t
type ltac_constructor = KerName.t
type type_constant = KerName.t

type constructor_data = {
  cdata_type : type_constant;
  cdata_args : int * int glb_typexpr list;
  cdata_indx : int;
}

type ltac_state = {
  ltac_tactics : (glb_tacexpr * type_scheme) KNmap.t;
  ltac_constructors : constructor_data KNmap.t;
  ltac_types : glb_quant_typedef KNmap.t;
}

let empty_state = {
  ltac_tactics = KNmap.empty;
  ltac_constructors = KNmap.empty;
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
| GTacTup el -> ValBlk (0, Array.map_of_list eval_pure el)
| GTacCst (_, n, []) -> ValInt n
| GTacCst (_, n, el) -> ValBlk (n, Array.map_of_list eval_pure el)
| GTacAtm (AtmStr _) | GTacArr _ | GTacLet _ | GTacVar _
| GTacApp _ | GTacCse _ | GTacPrm _ ->
  anomaly (Pp.str "Term is not a syntactical value")

let define_global kn e =
  let state = !ltac_state in
  ltac_state := { state with ltac_tactics = KNmap.add kn e state.ltac_tactics }

let interp_global kn =
  let (e, t) = KNmap.find kn ltac_state.contents.ltac_tactics in
  (eval_pure e, t)

let define_constructor kn t =
  let state = !ltac_state in
  ltac_state := { state with ltac_constructors = KNmap.add kn t state.ltac_constructors }

let interp_constructor kn = KNmap.find kn ltac_state.contents.ltac_constructors

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

module KnTab = Nametab.Make(FullPath)(KerName)

type nametab = {
  tab_ltac : KnTab.t;
  tab_type : KnTab.t;
}

let empty_nametab = { tab_ltac = KnTab.empty; tab_type = KnTab.empty }

let nametab = Summary.ref empty_nametab ~name:"ltac2-nametab"

let push_ltac vis sp kn =
  let tab = !nametab in
  nametab := { tab with tab_ltac = KnTab.push vis sp kn tab.tab_ltac }

let locate_ltac qid =
  let tab = !nametab in
  KnTab.locate qid tab.tab_ltac

let locate_extended_all_ltac qid =
  let tab = !nametab in
  KnTab.find_prefixes qid tab.tab_ltac

let push_type vis sp kn =
  let tab = !nametab in
  nametab := { tab with tab_type = KnTab.push vis sp kn tab.tab_type }

let locate_type qid =
  let tab = !nametab in
  KnTab.locate qid tab.tab_type

let locate_extended_all_type qid =
  let tab = !nametab in
  KnTab.find_prefixes qid tab.tab_type
