(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Libnames
open Tac2expr
open Tac2val

type global_data = {
  gdata_expr : glb_tacexpr;
  gdata_type : type_scheme;
  gdata_mutable : bool;
  gdata_deprecation : Deprecation.t option;
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

type alias_data = {
  alias_body : raw_tacexpr;
  alias_depr : Deprecation.t option;
}

type ltac_state = {
  ltac_tactics : global_data KNmap.t;
  constructors_warn : UserWarn.t KNmap.t;
  ltac_constructors : constructor_data KNmap.t;
  ltac_projections : projection_data KNmap.t;
  ltac_types : glb_quant_typedef KNmap.t;
  ltac_aliases : alias_data KNmap.t;
}

let empty_state = {
  ltac_tactics = KNmap.empty;
  constructors_warn = KNmap.empty;
  ltac_constructors = KNmap.empty;
  ltac_projections = KNmap.empty;
  ltac_types = KNmap.empty;
  ltac_aliases = KNmap.empty;
}

type compile_info = {
  source : string;
}

let ltac_state = Summary.ref empty_state ~name:"ltac2-state"

let compiled_tacs = Summary.ref ~local:true ~name:"ltac2-compiled-state" KNmap.empty

type notation_data =
  | UntypedNota of raw_tacexpr
  | TypedNota of {
      nota_prms : int;
      nota_argtys : int glb_typexpr Id.Map.t;
      nota_ty : int glb_typexpr;
      nota_body : glb_tacexpr;
    }

let ltac_notations = Summary.ref KNmap.empty ~name:"ltac2-notations"

let define_global kn e =
  let state = !ltac_state in
  ltac_state := { state with ltac_tactics = KNmap.add kn e state.ltac_tactics }

let interp_global kn =
  let data = KNmap.find kn ltac_state.contents.ltac_tactics in
  data

let set_compiled_global kn info v =
  assert (not (interp_global kn).gdata_mutable);
  compiled_tacs := KNmap.add kn (info,v) !compiled_tacs

let get_compiled_global kn = KNmap.find_opt kn !compiled_tacs

let globals () = (!ltac_state).ltac_tactics

let define_constructor ?warn kn t =
  let state = !ltac_state in
  ltac_state := {
    state with
    ltac_constructors = KNmap.add kn t state.ltac_constructors;
    constructors_warn = Option.fold_left (fun ctorwarn warn ->
        KNmap.add kn warn ctorwarn)
        state.constructors_warn
        warn;
  }

let interp_constructor kn = KNmap.find kn ltac_state.contents.ltac_constructors

let find_all_constructors_in_type kn =
  KNmap.filter (fun _ data -> KerName.equal kn data.cdata_type) (!ltac_state).ltac_constructors

let define_projection kn t =
  let state = !ltac_state in
  ltac_state := { state with ltac_projections = KNmap.add kn t state.ltac_projections }

let interp_projection kn = KNmap.find kn ltac_state.contents.ltac_projections

let define_type kn e =
  let state = !ltac_state in
  ltac_state := { state with ltac_types = KNmap.add kn e state.ltac_types }

let interp_type kn = KNmap.find kn ltac_state.contents.ltac_types

let define_alias ?deprecation kn tac =
  let state = !ltac_state in
  let data = { alias_body = tac; alias_depr = deprecation } in
  ltac_state := { state with ltac_aliases = KNmap.add kn data state.ltac_aliases }

let interp_alias kn = KNmap.find kn ltac_state.contents.ltac_aliases

let define_notation kn tac =
  ltac_notations := KNmap.add kn tac !ltac_notations

let interp_notation kn = KNmap.find kn !ltac_notations

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

let define_primitive name f =
  let f = match f with
    | ValCls f -> ValCls (annotate_closure (FrPrim name) f)
    | _ -> f
  in
  primitive_map := MLMap.add name f !primitive_map
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

let path_of_ltac kn = RfMap.find kn (!nametab).tab_ltac_rev

let shortest_qualid_of_ltac avoid kn =
  let tab = !nametab in
  let sp = RfMap.find kn tab.tab_ltac_rev in
  RfTab.shortest_qualid avoid sp tab.tab_ltac

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

let path_of_constructor kn = KNmap.find kn (!nametab).tab_cstr_rev

let shortest_qualid_of_constructor kn =
  let tab = !nametab in
  let sp = KNmap.find kn tab.tab_cstr_rev in
  KnTab.shortest_qualid Id.Set.empty sp tab.tab_cstr

let constructor_user_warning =
  UserWarn.create_depr_and_user_warnings
    ~object_name:"Ltac2 constructor"
    ~warning_name_base:"ltac2-constructor"
    (fun kn -> pr_qualid (shortest_qualid_of_constructor kn))
    ()

let constructor_user_warn ?loc kn =
  let warn = KNmap.find_opt kn (!ltac_state).constructors_warn in
  Option.iter (constructor_user_warning ?loc kn) warn

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

let path_of_type kn = KNmap.find kn (!nametab).tab_type_rev

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
  ml_intern : 'r. ('a, 'b or_glb_tacexpr, 'r) intern_fun;
  ml_subst : Mod_subst.substitution -> 'b -> 'b;
  ml_interp : environment -> 'b -> valexpr Proofview.tactic;
  ml_print : Environ.env -> Evd.evar_map -> 'b -> Pp.t;
  ml_raw_print : Environ.env -> Evd.evar_map -> 'a -> Pp.t;
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

let rocq_prefix =
  MPfile (DirPath.make (List.map Id.of_string ["Init"; "Ltac2"]))

let coq_prefix = rocq_prefix

let std_prefix =
  MPfile (DirPath.make (List.map Id.of_string ["Std"; "Ltac2"]))

let ltac1_prefix =
  MPfile (DirPath.make (List.map Id.of_string ["Ltac1"; "Ltac2"]))

(** Generic arguments *)

type var_quotation_kind =
  | ConstrVar
  | PretermVar
  | PatternVar

let wit_ltac2_constr = Genarg.make0 "ltac2:in-constr"
let wit_ltac2_var_quotation = Genarg.make0 "ltac2:quotation"

let is_constructor_id id =
  let id = Id.to_string id in
  assert (String.length id > 0);
  match id with
  | "true" | "false" -> true (* built-in constructors *)
  | _ ->
    match id.[0] with
    | 'A'..'Z' -> true
    | _ -> false

let is_constructor qid =
  let (_, id) = repr_qualid qid in
  is_constructor_id id
