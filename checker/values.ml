(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
  | Int64
  | Float64

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
let v_level_global = v_tuple "Level.Global.t" [|v_dp;String;Int|]
let v_raw_level = v_sum "raw_level" 3 (* SProp, Prop, Set *)
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
let v_context_set = v_tuple "universe_context_set" [|v_hset v_level;v_cstrs|]

(** kernel/term *)

let v_sort = v_sum "sort" 3 (*SProp, Prop, Set*) [|[|v_univ(*Type*)|]|]
let v_sortfam = v_enum "sorts_family" 4

let v_relevance = v_sum "relevance" 2 [||]
let v_binder_annot x = v_tuple "binder_annot" [|x;v_relevance|]

let v_puniverses v = v_tuple "punivs" [|v;v_instance|]

let v_boollist = List v_bool

let v_caseinfo =
  let v_cstyle = v_enum "case_style" 5 in
  let v_cprint = v_tuple "case_printing" [|v_boollist;Array v_boollist;v_cstyle|] in
  v_tuple "case_info" [|v_ind;Int;Array Int;Array Int;v_relevance;v_cprint|]

let v_cast = v_enum "cast_kind" 3

let v_proj_repr = v_tuple "projection_repr" [|v_ind;v_bool;Int;Int;v_id|]
let v_proj = v_tuple "projection" [|v_proj_repr; v_bool|]

let v_uint63 =
  if Sys.word_size == 64 then Int else Int64

let rec v_constr =
  Sum ("constr",0,[|
    [|Int|]; (* Rel *)
    [|v_id|]; (* Var *)
    [|Fail "Meta"|]; (* Meta *)
    [|Fail "Evar"|]; (* Evar *)
    [|v_sort|]; (* Sort *)
    [|v_constr;v_cast;v_constr|]; (* Cast *)
    [|v_binder_annot v_name;v_constr;v_constr|]; (* Prod *)
    [|v_binder_annot v_name;v_constr;v_constr|]; (* Lambda *)
    [|v_binder_annot v_name;v_constr;v_constr;v_constr|]; (* LetIn *)
    [|v_constr;Array v_constr|]; (* App *)
    [|v_puniverses v_cst|]; (* Const *)
    [|v_puniverses v_ind|]; (* Ind *)
    [|v_puniverses v_cons|]; (* Construct *)
    [|v_caseinfo;v_instance; Array v_constr; v_case_return; v_case_invert; v_constr; Array v_case_branch|]; (* Case *)
    [|v_fix|]; (* Fix *)
    [|v_cofix|]; (* CoFix *)
    [|v_proj;v_constr|]; (* Proj *)
    [|v_uint63|]; (* Int *)
    [|Float64|]; (* Float *)
    [|v_instance;Array v_constr;v_constr;v_constr|] (* Array *)
  |])

and v_prec = Tuple ("prec_declaration",
                    [|Array (v_binder_annot v_name); Array v_constr; Array v_constr|])
and v_fix = Tuple ("pfixpoint", [|Tuple ("fix2",[|Array Int;Int|]);v_prec|])
and v_cofix = Tuple ("pcofixpoint",[|Int;v_prec|])
and v_case_invert = Sum ("case_inversion", 1, [|[|Array v_constr|]|])

and v_case_branch = Tuple ("case_branch", [|Array (v_binder_annot v_name); v_constr|])

and v_case_return = Tuple ("case_return", [|Array (v_binder_annot v_name); v_constr|])

let v_rdecl = v_sum "rel_declaration" 0
    [| [|v_binder_annot v_name; v_constr|];               (* LocalAssum *)
       [|v_binder_annot v_name; v_constr; v_constr|] |]   (* LocalDef *)
let v_rctxt = List v_rdecl

let v_ndecl = v_sum "named_declaration" 0
    [| [|v_binder_annot v_id; v_constr|];               (* LocalAssum *)
       [|v_binder_annot v_id; v_constr; v_constr|] |]   (* LocalDef *)
let v_nctxt = List v_ndecl

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

let v_abstr_info =
  Tuple ("abstr_info", [|v_nctxt; v_abs_context; v_instance|])

let v_abstr_inst_info =
  Tuple ("abstr_inst_info", [|List v_id; v_instance|])

let v_expand_info =
  Tuple ("expand_info", [|v_hmap v_cst v_abstr_inst_info; v_hmap v_cst v_abstr_inst_info|])

let v_cooking_info =
  Tuple ("cooking_info", [|v_expand_info; v_abstr_info|])

let v_opaque =
  v_sum "opaque" 0 [|[|List v_subst; List v_cooking_info; v_dp; Int|]|]

(** kernel/declarations *)

let v_conv_level =
  v_sum "conv_level" 2 [|[|Int|]|]

let v_oracle =
  v_tuple "oracle" [|
    v_map v_id v_conv_level;
    v_hmap v_cst v_conv_level;
    v_pred v_id;
    v_pred v_cst;
  |]

let v_template_arity =
  v_tuple "template_arity" [|v_sort|]

let v_template_universes =
  v_tuple "template_universes" [|List(Opt v_level);v_context_set|]

let v_primitive =
  v_enum "primitive" 55 (* Number of constructors of the CPrimitives.t type *)

let v_cst_def =
  v_sum "constant_def" 0
    [|[|Opt Int|]; [|v_constr|]; [|v_opaque|]; [|v_primitive|]|]

let v_typing_flags =
  v_tuple "typing_flags"
    [|v_bool; v_bool; v_bool;
      v_oracle; v_bool; v_bool;
      v_bool; v_bool; v_bool; v_bool; v_bool|]

let v_univs = v_sum "universes" 1 [|[|v_abs_context|]|]

let v_cb = v_tuple "constant_body"
  [|v_section_ctxt;
    v_instance;
    v_cst_def;
    v_constr;
    v_relevance;
    Any;
    v_univs;
    v_bool;
    v_typing_flags|]

let v_nested = v_sum "nested" 0
  [|[|v_ind|] (* NestedInd *);[|v_cst|] (* NestedPrimitive *)|]

let v_recarg = v_sum "recarg" 1 (* Norec *)
  [|[|v_ind|] (* Mrec *);[|v_nested|] (* Nested *)|]

let rec v_wfp = Sum ("wf_paths",0,
    [|[|Int;Int|]; (* Rtree.Param *)
      [|v_recarg;Array (Array v_wfp)|]; (* Rtree.Node *)
      [|Int;Array v_wfp|] (* Rtree.Rec *)
    |])

let v_mono_ind_arity =
  v_tuple "monomorphic_inductive_arity" [|v_constr;v_sort|]

let v_ind_arity = v_sum "inductive_arity" 0
  [|[|v_mono_ind_arity|];[|v_template_arity|]|]

let v_one_ind = v_tuple "one_inductive_body"
  [|v_id;
    v_rctxt;
    v_ind_arity;
    Array v_id;
    Array v_constr;
    Int;
    Int;
    v_sortfam;
    Array (v_pair v_rctxt v_constr);
    Array Int;
    Array Int;
    v_wfp;
    v_relevance;
    Int;
    Int;
    Any|]

let v_finite = v_enum "recursivity_kind" 3

let v_record_info =
  v_sum "record_info" 2
    [| [| Array (v_tuple "record" [| v_id; Array v_id; Array v_relevance; Array v_constr |]) |] |]

let v_ind_pack = v_tuple "mutual_inductive_body"
  [|Array v_one_ind;
    v_record_info;
    v_finite;
    Int;
    v_section_ctxt;
    v_instance;
    Int;
    Int;
    v_rctxt;
    v_univs; (* universes *)
    Opt v_template_universes;
    Opt (Array v_variance);
    Opt (Array v_variance);
    Opt v_bool;
    v_typing_flags|]

let v_prim_ind = v_enum "prim_ind" 6
(* Number of "Register ... as kernel.ind_..." in PrimInt63.v and PrimFloat.v *)

let v_prim_type = v_enum "prim_type" 3
(* Number of constructors of prim_type in "kernel/cPrimitives.ml" *)

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
  [|[|v_mae|];                     (* MENoFunctor *)
    [|v_mexpr|]|])                 (* MEMoreFunctor *)
and v_impl =
  Sum ("module_impl",2, (* Abstract, FullStruct *)
  [|[|v_mexpr|];  (* Algebraic *)
    [|v_struc|]|])  (* Struct *)
and v_noimpl = v_unit
and v_module =
  Tuple ("module_body",
         [|v_mp;v_impl;v_sign;Opt v_mexpr;v_resolver;v_retroknowledge|])
and v_modtype =
  Tuple ("module_type_body",
         [|v_mp;v_noimpl;v_sign;Opt v_mexpr;v_resolver;v_unit|])

(** kernel/safe_typing *)

let v_vodigest = Sum ("module_impl",0, [| [|String|]; [|String;String|] |])
let v_deps = Array (v_tuple "dep" [|v_dp;v_vodigest|])
let v_compiled_lib =
  v_tuple "compiled" [|v_dp;v_module;v_context_set;v_deps|]

(** Library objects *)

let v_obj = Dyn

let v_open_filter = Sum ("open_filter",1,[|[|v_pred String|]|])

let rec v_aobjs = Sum("algebraic_objects", 0,
  [| [|v_libobjs|];
     [|v_mp;v_subst|]
  |])
and v_substobjs =
  Tuple("*", [|List v_uid;v_aobjs|])
and v_libobjt = Sum("Libobject.t",0,
  [| [| v_id; v_substobjs |];
     [| v_id; v_substobjs |];
     [| v_aobjs |];
     [| v_id; v_libobjs |];
     [| List (v_pair v_open_filter v_mp)|];
     [| v_obj |]
  |])

and v_libobjs = List v_libobjt

let v_libraryobjs = Tuple ("library_objects",[|v_libobjs;v_libobjs|])

let v_librarysyntaxobjs = Tuple ("library_syntax_objects",[|v_libobjs;v_libobjs|])

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
  Tuple ("summary", [|v_dp;v_deps;String|])

let v_lib =
  Tuple ("library",[|v_compiled_lib;v_librarysyntaxobjs;v_libraryobjs|])

let v_delayed_universes =
  Sum ("delayed_universes", 0, [| [| v_unit |]; [| v_context_set |] |])

let v_opaquetable = Array (Opt (v_pair v_constr v_delayed_universes))
let v_univopaques =
  Opt (Tuple ("univopaques",[|v_context_set;v_bool|]))
