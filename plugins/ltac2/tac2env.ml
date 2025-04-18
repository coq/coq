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
  ltac_constructors : constructor_data KNmap.t;
  ltac_projections : projection_data KNmap.t;
  ltac_types : glb_quant_typedef KNmap.t;
  ltac_aliases : alias_data KNmap.t;
}

let empty_state = {
  ltac_tactics = KNmap.empty;
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

let define_constructor kn t =
  let state = !ltac_state in
  ltac_state := {
    state with
    ltac_constructors = KNmap.add kn t state.ltac_constructors;
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

open Nametab

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

module DefV = struct
  include TacRef
  let is_var _ = None
  module Map = Map.Make(TacRef)
end
module DefTab = MakeTab(DefV)(NoWarn(DefV))()

module CtorV = struct
  include KerName
  let is_var _ = None
  module Map = KNmap
end
module CtorWarn = struct
  type t = CtorV.t
  let object_name = "Ltac2 constructor"
  let warning_name_base = "ltac2-constructor"
end
module CtorTab = MakeTab(CtorV)(SimpleWarn(CtorWarn))()

module TypV = struct
  include KerName
  let is_var _ = None
  module Map = KNmap
end
module TypTab = MakeTab(TypV)(NoWarn(TypV))()

module ProjV = struct
  include KerName
  let is_var _ = None
  module Map = KNmap
end
module ProjTab = MakeTab(ProjV)(NoWarn(ProjV))()

type nametab = {
  tab_ltac : DefTab.t;
  tab_cstr : CtorTab.t;
  tab_type : TypTab.t;
  tab_proj : ProjTab.t;
}

let empty_nametab = {
  tab_ltac = DefTab.empty;
  tab_cstr = CtorTab.empty;
  tab_type = TypTab.empty;
  tab_proj = ProjTab.empty;
}

let nametab = Summary.ref empty_nametab ~name:"ltac2-nametab"

let push_ltac vis sp kn =
  let tab = !nametab in
  let tab_ltac = DefTab.push vis sp kn tab.tab_ltac in
  nametab := { tab with tab_ltac }

let locate_ltac qid =
  let tab = !nametab in
  DefTab.locate qid tab.tab_ltac

let locate_extended_all_ltac qid =
  let tab = !nametab in
  DefTab.locate_all qid tab.tab_ltac

let path_of_ltac kn = DefTab.to_path kn (!nametab).tab_ltac

let shortest_qualid_of_ltac avoid kn =
  let tab = !nametab in
  DefTab.shortest_qualid avoid kn tab.tab_ltac

let push_constructor ?user_warns vis sp kn =
  let tab = !nametab in
  (* XXX support qf *)
  let user_warns = Option.map UserWarn.with_empty_qf user_warns in
  let tab_cstr = CtorTab.push ?user_warns vis sp kn tab.tab_cstr in
  nametab := { tab with tab_cstr; }

let locate_constructor qid =
  let tab = !nametab in
  CtorTab.locate qid tab.tab_cstr

let locate_extended_all_constructor qid =
  let tab = !nametab in
  CtorTab.locate_all qid tab.tab_cstr

let path_of_constructor kn = CtorTab.to_path kn (!nametab).tab_cstr

let shortest_qualid_of_constructor kn =
  let tab = !nametab in
  CtorTab.shortest_qualid Id.Set.empty kn tab.tab_cstr

let push_type vis sp kn =
  let tab = !nametab in
  let tab_type = TypTab.push vis sp kn tab.tab_type in
  nametab := { tab with tab_type; }

let locate_type qid =
  let tab = !nametab in
  TypTab.locate qid tab.tab_type

let locate_extended_all_type qid =
  let tab = !nametab in
  TypTab.locate_all qid tab.tab_type

let path_of_type kn = TypTab.to_path kn (!nametab).tab_type

let shortest_qualid_of_type ?loc kn =
  let tab = !nametab in
  TypTab.shortest_qualid Id.Set.empty ?loc kn tab.tab_type

let push_projection vis sp kn =
  let tab = !nametab in
  let tab_proj = ProjTab.push vis sp kn tab.tab_proj in
  nametab := { tab with tab_proj; }

let locate_projection qid =
  let tab = !nametab in
  ProjTab.locate qid tab.tab_proj

let locate_extended_all_projection qid =
  let tab = !nametab in
  ProjTab.locate_all qid tab.tab_proj

let shortest_qualid_of_projection kn =
  let tab = !nametab in
  ProjTab.shortest_qualid Id.Set.empty kn tab.tab_proj

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
let wit_ltac2_tac = Genarg.make0 "ltac2:tactic"

let () = Geninterp.register_val0 wit_ltac2_tac
    (Some (Geninterp.val_tag (Genarg.topwit Stdarg.wit_unit)))

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
