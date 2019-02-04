(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Abstract representations of values in a vo *)

(** NB: This needs updating when the types in declarations.ml and
   their dependencies are changed. *)

(** We reify here the types of values present in a vo.
    in order to validate its structure. Maybe this reification
    could become automatically generated someday ?

    See values.mli for the meaning of each constructor.
*)

type value =
  | Any
  | Fail of string
  | Tuple of string * value array
  | Sum of string * int * value array array
  | Array of value
  | List of value
  | Opt of value
  | Int
  | String
  | Annot of string * value
  | Dyn

  | Proxy of value ref
  | Uint63

let fix (f : value -> value) : value =
  let self = ref Any in
  let ans = f (Proxy self) in
  let () = self := ans in
  ans

(** Some pseudo-constructors *)

let v_tuple name v = Tuple(name,v)
let v_sum name cc vv = Sum(name,cc,vv)
let v_enum name n = Sum(name,n,[||])

(** Ocaml standard library *)

let v_pair v1 v2 = v_tuple "*" [|v1; v2|]
let v_bool = v_enum "bool" 2
let v_unit = v_enum "unit" 1
let v_ref v = v_tuple "ref" [|v|]

let v_set v =
  let rec s = Sum ("Set.t",1,
    [|[|s; Annot("elem",v); s; Annot("bal",Int)|]|])
  in s

let v_map vk vd =
  let rec m = Sum ("Map.t",1,
    [|[|m; Annot("key",vk); Annot("data",vd); m; Annot("bal",Int)|]|])
  in m

let v_hset v = v_map Int (v_set v)
let v_hmap vk vd = v_map Int (v_map vk vd)

let v_pred v = v_pair v_bool (v_set v)

(* lib/future *)
let v_computation f =
  Annot ("Future.computation",
  v_ref
    (v_sum "Future.comput" 0
      [| [| Fail "Future.ongoing" |]; [| f |] |]))

(** kernel/names *)

let v_id = String
let v_dp = Annot ("dirpath", List v_id)
let v_name = v_sum "name" 1 [|[|v_id|]|]
let v_uid = v_tuple "uniq_ident" [|Int;String;v_dp|]
let rec v_mp = Sum("module_path",0,
  [|[|v_dp|];
    [|v_uid|];
    [|v_mp;v_id|]|])
let v_kn = v_tuple "kernel_name" [|v_mp;v_id;Int|]
let v_cst = v_sum "cst|mind" 0 [|[|v_kn|];[|v_kn;v_kn|]|]
let v_ind = v_tuple "inductive" [|v_cst;Int|]
let v_cons = v_tuple "constructor" [|v_ind;Int|]


(** kernel/univ *)
let v_level_global = v_tuple "Level.Global.t" [|v_dp;Int|]
let v_raw_level = v_sum "raw_level" 2 (* Prop, Set *) 
  [|(*Level*)[|v_level_global|]; (*Var*)[|Int|]|]
let v_level = v_tuple "level" [|Int;v_raw_level|] 
let v_expr = v_tuple "levelexpr" [|v_level;Int|]
let v_univ = List v_expr

let v_cstrs =
  Annot
    ("Univ.constraints",
     v_set
       (v_tuple "univ_constraint"
          [|v_level;v_enum "order_request" 3;v_level|]))

let v_variance = v_enum "variance" 3

let v_instance = Annot ("instance", Array v_level)
let v_abs_context = v_tuple "abstract_universe_context" [|Array v_name; v_cstrs|]
let v_abs_cum_info = v_tuple "cumulativity_info" [|v_abs_context; Array v_variance|]
let v_context_set = v_tuple "universe_context_set" [|v_hset v_level;v_cstrs|]

(** kernel/term *)

let v_sort = v_sum "sort" 2 (*Prop, Set*) [|[|v_univ(*Type*)|]|]
let v_sortfam = v_enum "sorts_family" 3

let v_puniverses v = v_tuple "punivs" [|v;v_instance|]

let v_boollist = List v_bool  

let v_caseinfo =
  let v_cstyle = v_enum "case_style" 5 in
  let v_cprint = v_tuple "case_printing" [|v_boollist;Array v_boollist;v_cstyle|] in
  v_tuple "case_info" [|v_ind;Int;Array Int;Array Int;v_cprint|]

let v_cast = v_enum "cast_kind" 4

let v_proj_repr = v_tuple "projection_repr" [|v_ind;Int;Int;v_id|]
let v_proj = v_tuple "projection" [|v_proj_repr; v_bool|]

let rec v_constr =
  Sum ("constr",0,[|
    [|Int|]; (* Rel *)
    [|Fail "Var"|]; (* Var *)
    [|Fail "Meta"|]; (* Meta *)
    [|Fail "Evar"|]; (* Evar *)
    [|v_sort|]; (* Sort *)
    [|v_constr;v_cast;v_constr|]; (* Cast *)
    [|v_name;v_constr;v_constr|]; (* Prod *)
    [|v_name;v_constr;v_constr|]; (* Lambda *)
    [|v_name;v_constr;v_constr;v_constr|]; (* LetIn *)
    [|v_constr;Array v_constr|]; (* App *)
    [|v_puniverses v_cst|]; (* Const *)
    [|v_puniverses v_ind|]; (* Ind *)
    [|v_puniverses v_cons|]; (* Construct *)
    [|v_caseinfo;v_constr;v_constr;Array v_constr|]; (* Case *)
    [|v_fix|]; (* Fix *)
    [|v_cofix|]; (* CoFix *)
    [|v_proj;v_constr|]; (* Proj *)
    [|Uint63|] (* Int *)
  |])

and v_prec = Tuple ("prec_declaration",
                    [|Array v_name; Array v_constr; Array v_constr|])
and v_fix = Tuple ("pfixpoint", [|Tuple ("fix2",[|Array Int;Int|]);v_prec|])
and v_cofix = Tuple ("pcofixpoint",[|Int;v_prec|])

let v_rdecl = v_sum "rel_declaration" 0 [| [|v_name; v_constr|];               (* LocalAssum *)
                                           [|v_name; v_constr; v_constr|] |]   (* LocalDef *)
let v_rctxt = List v_rdecl

let v_section_ctxt = v_enum "emptylist" 1


(** kernel/mod_subst *)

let v_univ_abstracted v = v_tuple "univ_abstracted" [|v;v_abs_context|]

let v_delta_hint =
  v_sum "delta_hint" 0 [|[|Int; Opt (v_univ_abstracted v_constr)|];[|v_kn|]|]

let v_resolver =
  v_tuple "delta_resolver"
    [|v_map v_mp v_mp;
      v_hmap v_kn v_delta_hint|]

let v_mp_resolver = v_tuple "" [|v_mp;v_resolver|]

let v_subst =
  Annot ("substitution", v_map v_mp v_mp_resolver)

(** kernel/lazyconstr *)

let v_substituted v_a =
  v_tuple "substituted" [|v_a; List v_subst|]

let v_cstr_subst = v_substituted v_constr

(** NB: Second constructor [Direct] isn't supposed to appear in a .vo *)
let v_lazy_constr =
  v_sum "lazy_constr" 0 [|[|List v_subst;v_dp;Int|]|]


(** kernel/declarations *)

let v_impredicative_set = v_enum "impr-set" 2
let v_engagement = v_impredicative_set

let v_conv_level =
  v_sum "conv_level" 2 [|[|Int|]|]

let v_oracle =
  v_tuple "oracle" [|
    v_map v_id v_conv_level;
    v_hmap v_cst v_conv_level;
    v_pred v_id;
    v_pred v_cst;
  |]

let v_pol_arity =
  v_tuple "polymorphic_arity" [|List(Opt v_level);v_univ|]

let v_primitive =
  v_enum "primitive" 25

let v_cst_def =
  v_sum "constant_def" 0
    [|[|Opt Int|]; [|v_cstr_subst|]; [|v_lazy_constr|]; [|v_primitive|]|]

let v_typing_flags =
  v_tuple "typing_flags" [|v_bool; v_bool; v_oracle; v_bool; v_bool; v_bool; v_bool|]

let v_const_univs = v_sum "constant_universes" 0 [|[|v_context_set|]; [|v_abs_context|]|]

let v_cb = v_tuple "constant_body"
  [|v_section_ctxt;
    v_cst_def;
    v_constr;
    Any;
    v_const_univs;
    Opt v_context_set;
    v_bool;
    v_typing_flags|]

let v_recarg = v_sum "recarg" 1 (* Norec *)
  [|[|v_ind|] (* Mrec *);[|v_ind|] (* Imbr *)|]

let rec v_wfp = Sum ("wf_paths",0,
    [|[|Int;Int|]; (* Rtree.Param *)
      [|v_recarg;Array v_wfp|]; (* Rtree.Node *)
      [|Int;Array v_wfp|] (* Rtree.Rec *)
    |])

let v_mono_ind_arity =
  v_tuple "monomorphic_inductive_arity" [|v_constr;v_sort|]

let v_ind_arity = v_sum "inductive_arity" 0
  [|[|v_mono_ind_arity|];[|v_pol_arity|]|]

let v_one_ind = v_tuple "one_inductive_body"
  [|v_id;
    v_rctxt;
    v_ind_arity;
    Array v_id;
    Array v_constr;
    Int;
    Int;
    List v_sortfam;
    Array v_constr;
    Array Int;
    Array Int;
    v_wfp;
    Int;
    Int;
    Any|]

let v_finite = v_enum "recursivity_kind" 3

let v_record_info =
  v_sum "record_info" 2
    [| [| Array (v_tuple "record" [| v_id; Array v_id; Array v_constr |]) |] |]

let v_ind_pack_univs = 
  v_sum "abstract_inductive_universes" 0
    [|[|v_context_set|]; [|v_abs_context|]; [|v_abs_cum_info|]|]

let v_ind_pack = v_tuple "mutual_inductive_body"
  [|Array v_one_ind;
    v_record_info;
    v_finite;
    Int;
    v_section_ctxt;
    Int;
    Int;
    v_rctxt;
    v_ind_pack_univs; (* universes *)
    Opt v_bool;
    v_typing_flags|]

let v_prim_ind = v_enum "prim_ind" 4

let v_prim_type = v_enum "prim_type" 1

let v_retro_action =
  v_sum "retro_action" 0 [|
    [|v_prim_ind; v_ind|];
    [|v_prim_type; v_cst|];
    [|v_cst|];
  |]

let v_retroknowledge =
  v_sum "module_retroknowledge" 1 [|[|List v_retro_action|]|]

let rec v_mae =
  Sum ("module_alg_expr",0,
  [|[|v_mp|];         (* SEBident *)
    [|v_mae;v_mp|];   (* SEBapply *)
    [|v_mae; Any|]  (* SEBwith *)
  |])

let rec v_sfb =
  Sum ("struct_field_body",0,
  [|[|v_cb|];       (* SFBconst *)
    [|v_ind_pack|]; (* SFBmind *)
    [|v_module|];   (* SFBmodule *)
    [|v_modtype|]   (* SFBmodtype *)
  |])
and v_struc = List (Tuple ("label*sfb",[|v_id;v_sfb|]))
and v_sign =
  Sum ("module_sign",0,
  [|[|v_struc|];                   (* NoFunctor *)
    [|v_uid;v_modtype;v_sign|]|])  (* MoreFunctor *)
and v_mexpr =
  Sum ("module_expr",0,
  [|[|v_mae|];                     (* NoFunctor *)
    [|v_uid;v_modtype;v_mexpr|]|]) (* MoreFunctor *)
and v_impl =
  Sum ("module_impl",2, (* Abstract, FullStruct *)
  [|[|v_mexpr|];  (* Algebraic *)
    [|v_sign|]|])  (* Struct *)
and v_noimpl = v_unit
and v_module =
  Tuple ("module_body",
         [|v_mp;v_impl;v_sign;Opt v_mexpr;v_context_set;v_resolver;v_retroknowledge|])
and v_modtype =
  Tuple ("module_type_body",
         [|v_mp;v_noimpl;v_sign;Opt v_mexpr;v_context_set;v_resolver;v_unit|])

(** kernel/safe_typing *)

let v_vodigest = Sum ("module_impl",0, [| [|String|]; [|String;String|] |])
let v_deps = Array (v_tuple "dep" [|v_dp;v_vodigest|])
let v_compiled_lib =
  v_tuple "compiled" [|v_dp;v_module;v_deps;v_engagement;Any|]

(** Library objects *)

let v_obj = Dyn
let v_libobj = Tuple ("libobj", [|v_id;v_obj|])
let v_libobjs = List v_libobj
let v_libraryobjs = Tuple ("library_objects",[|v_libobjs;v_libobjs|])

(** STM objects *)

let v_frozen = Tuple ("frozen", [|List (v_pair Int Dyn); Opt Dyn|])
let v_states = v_pair Any v_frozen
let v_state = Tuple ("state", [|v_states; Any; v_bool|])

let v_vcs =
  let vcs self =
    Tuple ("vcs",
      [|Any; Any;
        Tuple ("dag",
          [|Any; Any; v_map Any (Tuple ("state_info",
            [|Any; Any; Opt v_state; v_pair (Opt self) Any|]))
          |])
      |])
  in
  fix vcs

let v_uuid = Any
let v_request id doc =
  Tuple ("request", [|Any; Any; doc; Any; id; String|])
let v_tasks = List (v_pair (v_request v_uuid v_vcs) v_bool)
let v_counters = Any
let v_stm_seg = v_pair v_tasks v_counters

(** Toplevel structures in a vo (see Cic.mli) *)

let v_libsum =
  Tuple ("summary", [|v_dp;Array v_dp;v_deps|])

let v_lib =
  Tuple ("library",[|v_compiled_lib;v_libraryobjs|])

let v_opaques = Array (v_computation v_constr)
let v_univopaques =
  Opt (Tuple ("univopaques",[|Array (v_computation v_context_set);v_context_set;v_bool|]))
