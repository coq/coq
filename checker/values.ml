(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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

type 'v kind =
  | Any
  | Fail of string
  | Tuple of string * 'v array
  | Sum of string * int * 'v array array
  | Array of 'v
  | List of 'v
  | Opt of 'v
  | Int
  | String
  | Annot of string * 'v
  | Int64
  | Float64

module Vector = struct

type ('a,_) t =
  | [] : ('a, [`O]) t
  | (::) : 'a * ('a, 's) t -> ('a, [`S of 's]) t

type 'n size = (unit,'n) t

let rec vmap : 'n 'a 'b. ('a -> 'b) -> ('a,'n) t -> ('b, 'n) t =
  fun (type n) f (v:(_,n) t) : (_,n) t ->
  match v with
  | [] -> []
  | x :: tl ->
    let x = f x in
    x :: vmap f tl

let rec viter2 : 'n 'a 'b. ('a -> 'b -> unit) -> ('a,'n) t -> ('b,'n) t -> unit =
  fun (type n) f (v1:(_,n) t) (v2:(_,n) t) ->
  match v1, v2 with
  | [], []-> ()
  | x1 :: tl1, x2 :: tl2 ->
    let () = f x1 x2 in
    viter2 f tl1 tl2
end

module Internal : sig
  type value

  val equal : value -> value -> bool

  val kind : value -> value kind

  val of_kind : value kind -> value

  val mfix : 'n Vector.size -> ((value,'n) Vector.t -> (value,'n) Vector.t) -> (value,'n) Vector.t
  end = struct
type value =
  | V of value kind
  | Proxy of value kind ref

let kind = function
  | V v -> v
  | Proxy v -> !v

(* Proxy is equal to its contents *)
let equal a b = kind a == kind b

let of_kind v = V v

let check_productive = function
  | Proxy _ -> assert false
  | V v -> v

let mfix (type n) (n:n Vector.size) (f : (value,n) Vector.t -> (value,n) Vector.t) : (value,n) Vector.t =
  let open Vector in
  let self = vmap (fun () -> Proxy (ref Any)) n in
  let ans = f self in
  let () = viter2 (fun self ans ->
      let ans = check_productive ans in
      match self with
      | Proxy self -> self := ans
      | _ -> assert false)
      self ans
  in
  ans

end

type nonrec value = Internal.value

let equal = Internal.equal

let kind = Internal.kind

let of_kind = Internal.of_kind

let mfix = Internal.mfix

let fix f =
  let [v] : _ Vector.t = mfix [()] (fun [v] -> [f v]) in
  v

(** Some pseudo-constructors *)

let v_tuple name v = of_kind @@ Tuple(name,v)
let v_sum name cc vv = of_kind @@ Sum(name,cc,vv)
let v_enum name n = of_kind @@ Sum(name,n,[||])
let v_annot a v = of_kind @@ Annot (a, v)
let v_fail f = of_kind @@ Fail f

(* uncurried forms *)

let v_tuple_c (name,v) = v_tuple name v
let v_sum_c (name,cc,vv) = v_sum name cc vv
let v_annot_c (a, v) = v_annot a v

(** Ocaml standard library *)

let v_any = of_kind Any
let v_int = of_kind Int
let v_int64 = of_kind Int64
let v_float64 = of_kind Float64
let v_string = of_kind String
let v_opt v = of_kind @@ Opt v
let v_list v = of_kind @@ List v
let v_array v = of_kind @@ Array v
let v_pair v1 v2 = v_tuple "*" [|v1; v2|]
let v_bool = v_enum "bool" 2
let v_unit = v_enum "unit" 1

let v_set v =
  fix (fun s ->
      v_sum_c ("Set.t",1,
           [|[|s; v_annot_c ("elem", v); s; v_annot_c ("bal", v_int)|]|]))

let v_map vk vd =
  fix (fun m ->
      v_sum_c ("Map.t",1,
           [|[|m; v_annot_c("key",vk); v_annot_c("data",vd); m; v_annot_c("bal",v_int)|]|]))

let v_hset v = v_map v_int (v_set v)
let v_hmap vk vd = v_map v_int (v_map vk vd)

let v_pred v = v_pair v_bool (v_set v)

(** kernel/names *)

let v_id = v_string
let v_dp = v_annot_c ("dirpath", v_list v_id)
let v_name = v_sum "name" 1 [|[|v_id|]|]
let v_uid = v_tuple "uniq_ident" [|v_int;v_string;v_dp|]
let v_mp =
  fix (fun v_mp ->
      v_sum_c("module_path",0,
          [|[|v_dp|];
            [|v_uid|];
            [|v_mp;v_id|]|]))
let v_kn = v_tuple "kernel_name" [|v_mp;v_id;v_int|]
let v_cst = v_sum "cst|mind" 0 [|[|v_kn|];[|v_kn;v_kn|]|]
let v_ind = v_tuple "inductive" [|v_cst;v_int|]
let v_cons = v_tuple "constructor" [|v_ind;v_int|]


(** kernel/univ *)
let v_level_global = v_tuple "Level.Global.t" [|v_dp;v_string;v_int|]
let v_raw_level = v_sum "raw_level" 1 (* Set *)
  [|(*Level*)[|v_level_global|]; (*Var*)[|v_int|]|]
let v_level = v_tuple "level" [|v_int;v_raw_level|]
let v_expr = v_tuple "levelexpr" [|v_level;v_int|]
let v_univ = v_list v_expr

let v_qvar = v_sum "qvar" 0 [|[|v_int|];[|v_string;v_int|]|]

let v_constant_quality = v_enum "constant_quality" 3

let v_quality = v_sum "quality" 0 [|[|v_qvar|];[|v_constant_quality|]|]

let v_cstrs =
  v_annot_c
    ("Univ.constraints",
     v_set
       (v_tuple "univ_constraint"
          [|v_level;v_enum "order_request" 3;v_level|]))

let v_variance = v_enum "variance" 3

let v_instance = v_annot_c ("instance", v_pair (v_array v_quality) (v_array v_level))
let v_abs_context = v_tuple "abstract_universe_context" [|v_pair (v_array v_name) (v_array v_name); v_cstrs|]
let v_context_set = v_tuple "universe_context_set" [|v_hset v_level;v_cstrs|]

(** kernel/term *)

let v_sort = v_sum "sort" 3 (*SProp, Prop, Set*) [|[|v_univ(*Type*)|];[|v_qvar;v_univ(*QSort*)|]|]

let v_relevance = v_sum "relevance" 2 [|[|v_qvar|]|]
let v_binder_annot x = v_tuple "binder_annot" [|x;v_relevance|]

let v_puniverses v = v_tuple "punivs" [|v;v_instance|]

let v_caseinfo =
  let v_cstyle = v_enum "case_style" 5 in
  let v_cprint = v_tuple "case_printing" [|v_cstyle|] in
  v_tuple "case_info" [|v_ind;v_int;v_array v_int;v_array v_int;v_cprint|]

let v_cast = v_enum "cast_kind" 3

let v_proj_repr = v_tuple "projection_repr" [|v_ind;v_int;v_int;v_cst|]
let v_proj = v_tuple "projection" [|v_proj_repr; v_bool|]

let v_uint63 =
  if Sys.word_size == 64 then v_int else v_int64

let v_constr =
  fix (fun v_constr ->
let v_prec =
  v_tuple_c ("prec_declaration",
         [|v_array (v_binder_annot v_name); v_array v_constr; v_array v_constr|])
in
let v_fix = v_tuple_c ("pfixpoint", [|v_tuple_c ("fix2",[|v_array v_int;v_int|]);v_prec|]) in
let v_cofix = v_tuple_c ("pcofixpoint",[|v_int;v_prec|]) in
let v_case_invert = v_sum_c ("case_inversion", 1, [|[|v_array v_constr|]|]) in
let v_case_branch = v_tuple_c ("case_branch", [|v_array (v_binder_annot v_name); v_constr|]) in
let v_case_return = v_tuple_c ("case_return", [|v_tuple_c ("case_return'", [|v_array (v_binder_annot v_name); v_constr|]); v_relevance|]) in
  v_sum_c ("constr",0,[|
    [|v_int|]; (* Rel *)
    [|v_id|]; (* Var *)
    [|v_fail "Meta"|]; (* Meta *)
    [|v_fail "Evar"|]; (* Evar *)
    [|v_sort|]; (* Sort *)
    [|v_constr;v_cast;v_constr|]; (* Cast *)
    [|v_binder_annot v_name;v_constr;v_constr|]; (* Prod *)
    [|v_binder_annot v_name;v_constr;v_constr|]; (* Lambda *)
    [|v_binder_annot v_name;v_constr;v_constr;v_constr|]; (* LetIn *)
    [|v_constr;v_array v_constr|]; (* App *)
    [|v_puniverses v_cst|]; (* Const *)
    [|v_puniverses v_ind|]; (* Ind *)
    [|v_puniverses v_cons|]; (* Construct *)
    [|v_caseinfo;v_instance; v_array v_constr; v_case_return; v_case_invert; v_constr; v_array v_case_branch|]; (* Case *)
    [|v_fix|]; (* Fix *)
    [|v_cofix|]; (* CoFix *)
    [|v_proj;v_relevance;v_constr|]; (* Proj *)
    [|v_uint63|]; (* v_int *)
    [|v_float64|]; (* Float *)
    [|v_string|]; (* v_string *)
    [|v_instance;v_array v_constr;v_constr;v_constr|] (* v_array *)
  |]))

let v_rdecl = v_sum "rel_declaration" 0
    [| [|v_binder_annot v_name; v_constr|];               (* LocalAssum *)
       [|v_binder_annot v_name; v_constr; v_constr|] |]   (* LocalDef *)
let v_rctxt = v_list v_rdecl

let v_ndecl = v_sum "named_declaration" 0
    [| [|v_binder_annot v_id; v_constr|];               (* LocalAssum *)
       [|v_binder_annot v_id; v_constr; v_constr|] |]   (* LocalDef *)
let v_nctxt = v_list v_ndecl

let v_section_ctxt = v_enum "emptylist" 1


(** kernel/mod_subst *)

let v_univ_abstracted v = v_tuple "univ_abstracted" [|v;v_abs_context|]

let v_delta_hint =
  v_sum "delta_hint" 0 [|[|v_int; v_opt (v_univ_abstracted v_constr)|];[|v_kn|]|]

let v_resolver =
  v_tuple "delta_resolver"
    [|v_mp; v_map v_mp v_mp;
      v_hmap v_kn v_delta_hint|]

let v_subst =
  v_annot_c ("substitution", v_map v_mp v_resolver)

(** kernel/lazyconstr *)

let v_abstr_info =
  v_tuple_c ("abstr_info", [|v_nctxt; v_abs_context; v_instance|])

let v_abstr_inst_info =
  v_tuple_c ("abstr_inst_info", [|v_list v_id; v_instance|])

let v_expand_info =
  v_tuple_c ("expand_info", [|v_hmap v_cst v_abstr_inst_info; v_hmap v_cst v_abstr_inst_info|])

let v_cooking_info =
  v_tuple_c ("cooking_info", [|v_expand_info; v_abstr_info|])

let v_opaque =
  v_sum "opaque" 0 [|[|v_list v_subst; v_list v_cooking_info; v_dp; v_int|]|]

(** kernel/declarations *)

let v_conv_level =
  v_sum "conv_level" 2 [|[|v_int|]|]

let v_oracle =
  v_tuple "oracle" [|
    v_map v_id v_conv_level;
    v_hmap v_cst v_conv_level;
    v_hmap v_proj_repr v_conv_level;
    v_pred v_id;
    v_pred v_cst;
    v_pred v_proj_repr;
  |]

let v_template_universes =
  v_tuple "template_universes" [|
    v_list (v_opt v_sort);
    v_sort;
    v_abs_context;
    v_instance;
  |]

let v_primitive =
  v_enum "primitive" 63 (* Number of constructors of the CPrimitives.t type *)

let v_cst_def =
  v_sum "constant_def" 0
    [|[|v_opt v_int|]; [|v_constr|]; [|v_opaque|]; [|v_primitive|]; [|v_bool|]|]

let v_typing_flags =
  v_tuple "typing_flags"
    [|v_bool; v_bool; v_bool;
      v_oracle; v_bool; v_bool;
      v_bool; v_bool; v_bool; v_bool; v_bool|]

let v_univs = v_sum "universes" 1 [|[|v_abs_context|]|]

let v_vm_reloc_table = v_array (v_pair v_int v_int)

let v_vm_annot_switch = v_tuple "vm_annot_switch" [|v_vm_reloc_table; v_bool; v_int|]

let v_vm_caml_prim = v_enum "vm_caml_prim" 6

let v_non_subst_reloc = v_sum "vm_non_subst_reloc" 0 [|
  [|v_sort|];
  [|v_fail "Evar"|];
  [|v_int|];
  [|v_instance|];
  [|v_any|]; (* contains a Vmvalues.value *)
  [|v_uint63|];
  [|v_float64|];
  [|v_string|];
  [|v_vm_annot_switch|];
  [|v_vm_caml_prim|];
|]

let v_reloc = v_sum "vm_reloc" 0 [|
    [|v_ind|];
    [|v_cst|];
    [|v_int|];
  |]

let v_vm_patches = v_tuple "vm_patches" [|v_array v_reloc|]

let v_vm_pbody_code index =
  v_sum "pbody_code" 1 [|
    [|v_array v_bool; index; v_vm_patches|];
    [|v_cst|];
  |]

let v_vm_index = v_pair v_dp v_int

let v_vm_indirect_code = v_vm_pbody_code v_vm_index

let v_vm_emitcodes = v_string

let v_vm_fv_elem = v_sum "vm_fv_elem" 0 [|
    [|v_id|];
    [|v_int|]
  |]

let v_vm_fv = v_array v_vm_fv_elem

let v_vm_positions = v_string

let v_vm_to_patch = v_tuple "vm_to_patch" [|v_vm_emitcodes; v_vm_fv; v_vm_positions; v_array v_non_subst_reloc|]

let v_cb = v_tuple "constant_body"
  [|v_section_ctxt;
    v_instance;
    v_cst_def;
    v_constr;
    v_relevance;
    v_opt v_vm_indirect_code;
    v_univs;
    v_bool;
    v_typing_flags|]

let v_recarg_type = v_sum "recarg_type" 0
  [|[|v_ind|] (* Mrec *);[|v_cst|] (* NestedPrimitive *)|]

let v_recarg = v_sum "recarg" 1 (* Norec *)
  [|[|v_recarg_type|] (* Mrec *)|]

let v_wfp =
  fix (fun v_wfp ->
  v_sum_c ("wf_paths",0,
    [|[|v_int;v_int|]; (* Rtree.Param *)
      [|v_recarg;v_array (v_array v_wfp)|]; (* Rtree.Node *)
      [|v_int;v_array v_wfp|] (* Rtree.Rec *)
    |]))

let v_squash_info = v_sum "squash_info" 1 [|[|v_set v_quality|]|]

let v_one_ind = v_tuple "one_inductive_body"
  [|v_id;
    v_rctxt;
    v_sort;
    v_constr;
    v_array v_id;
    v_array v_constr;
    v_int;
    v_int;
    v_opt v_squash_info;
    v_array (v_pair v_rctxt v_constr);
    v_array v_int;
    v_array v_int;
    v_wfp;
    v_relevance;
    v_int;
    v_int;
    v_vm_reloc_table|]

let v_finite = v_enum "recursivity_kind" 3

let v_record_info =
  v_sum "record_info" 2
    [| [| v_array (v_tuple "record" [| v_id; v_array v_id; v_array v_relevance; v_array v_constr |]) |] |]

let v_ind_pack = v_tuple "mutual_inductive_body"
  [|v_array v_one_ind;
    v_record_info;
    v_finite;
    v_int;
    v_section_ctxt;
    v_instance;
    v_int;
    v_int;
    v_rctxt;
    v_univs; (* universes *)
    v_opt v_template_universes;
    v_opt (v_array v_variance);
    v_opt (v_array v_variance);
    v_opt v_bool;
    v_typing_flags|]

let v_prim_ind = v_enum "prim_ind" 6
(* Number of "Register ... as kernel.ind_..." in Primv_int63.v and PrimFloat.v *)

let v_prim_type = v_enum "prim_type" 4
(* Number of constructors of prim_type in "kernel/cPrimitives.ml" *)

let v_retro_action =
  v_sum "retro_action" 0 [|
    [|v_prim_ind; v_ind|];
    [|v_prim_type; v_cst|];
  |]

let v_retroknowledge =
  v_sum "module_retroknowledge" 0 [|[|v_list v_retro_action|]|]

let v_puniv = v_opt v_int

let v_pqvar = v_opt v_int
let v_quality_pattern = v_sum "quality_pattern" 0 [|[|v_pqvar|];[|v_constant_quality|]|]

let v_instance_mask = v_pair (v_array v_quality_pattern) (v_array v_puniv)

let v_sort_pattern = v_sum_c ("sort_pattern", 3,
  [|[|v_puniv|];         (* PSType *)
    [|v_pqvar; v_puniv|] (* PSQSort *)
  |])

let [_v_hpattern;v_elimination;_v_head_elim;_v_patarg] : _ Vector.t =
  mfix [();();();()] (fun [v_hpattern;v_elimination;v_head_elim;v_patarg] ->
  let v_hpattern =
    v_sum_c ("head_pattern", 0,
         [|[|v_int|];                      (* PHRel *)
           [|v_sort_pattern|];           (* PHSort *)
           [|v_cst; v_instance_mask|];   (* PHSymbol *)
           [|v_ind; v_instance_mask|];   (* PHInd *)
           [|v_cons; v_instance_mask|];  (* PHConstr *)
           [|v_uint63|];                 (* PHv_int *)
           [|v_float64|];                  (* PHFloat *)
           [|v_string|];                   (* PHv_string *)
           [|v_array v_patarg; v_patarg|]; (* PHLambda *)
           [|v_array v_patarg; v_patarg|]; (* PHProd *)
         |])

  and v_elimination =
    v_sum_c ("pattern_elimination", 0,
         [|[|v_array v_patarg|];                                   (* PEApp *)
           [|v_ind; v_instance_mask; v_patarg; v_array v_patarg|]; (* PECase *)
           [|v_proj|];                                           (* PEProj *)
         |])

  and v_head_elim = v_tuple_c ("head*elims", [|v_hpattern; v_list v_elimination|])

  and v_patarg =
    v_sum_c ("pattern_argument", 1,
         [|[|v_int|];         (* EHole *)
           [|v_head_elim|]; (* ERigid *)
         |])
  in
  [v_hpattern;v_elimination;v_head_elim;v_patarg])

let v_rewrule = v_tuple "rewrite_rule"
  [| v_tuple "nvars" [| v_int; v_int; v_int |]; v_pair v_instance_mask (v_list v_elimination); v_constr |]
let v_rrb = v_tuple "rewrite_rules_body"
  [| v_list (v_pair v_cst v_rewrule) |]

let v_module_with_decl = v_sum "with_declaration" 0 [|
    [|v_list v_id; v_mp|];
    [|v_list v_id; v_pair v_constr (v_opt v_abs_context)|];
  |]

let v_mae =
  fix (fun v_mae ->
  v_sum_c ("module_alg_expr",0,
  [|[|v_mp|];         (* SEBident *)
    [|v_mae;v_mp|];   (* SEBapply *)
    [|v_mae; v_module_with_decl|]  (* SEBwith *)
  |]))

let [_v_sfb;_v_struc;_v_sign;_v_mexpr;_v_impl;v_module;_v_modtype] : _ Vector.t =
  mfix [();();();();();();()] (fun [v_sfb;v_struc;v_sign;v_mexpr;v_impl;v_module;v_modtype] ->
  let v_noimpl = v_unit in
  let v_sfb =
    v_sum_c ("struct_field_body",0,
         [|[|v_cb|];       (* SFBconst *)
           [|v_ind_pack|]; (* SFBmind *)
           [|v_rrb|];      (* SFBrules *)
           [|v_module|];   (* SFBmodule *)
           [|v_modtype|]   (* SFBmodtype *)
         |])
  and v_struc = v_list (v_tuple_c ("label*sfb",[|v_id;v_sfb|]))
  and v_sign =
    v_sum_c ("module_sign",0,
         [|[|v_struc|];                   (* NoFunctor *)
           [|v_uid;v_modtype;v_sign|]|])  (* MoreFunctor *)
  and v_mexpr =
    v_sum_c ("module_expr",0,
         [|[|v_mae|];                     (* MENoFunctor *)
           [|v_mexpr|]|])                 (* MEMoreFunctor *)
  and v_impl =
    v_sum_c ("module_impl",2, (* Abstract, FullStruct *)
         [|[|v_mexpr|];  (* Algebraic *)
           [|v_struc|]|])  (* Struct *)
  and v_module =
    v_tuple_c ("module_body",
           [|v_sum_c ("when_mod_body", 0, [|[|v_impl|]|]);v_sign;v_opt v_mexpr;v_resolver;v_retroknowledge|])
  and v_modtype =
    v_tuple_c ("module_type_body",
           [|v_noimpl;v_sign;v_opt v_mexpr;v_resolver;v_unit|])
  in
  [v_sfb;v_struc;v_sign;v_mexpr;v_impl;v_module;v_modtype])

(** kernel/safe_typing *)

let v_vodigest = v_sum_c ("module_impl",0, [| [|v_string|]; [|v_string;v_string|] |])
let v_deps = v_array (v_tuple "dep" [|v_dp;v_vodigest|])
let v_flags = v_tuple "flags" [|v_bool|] (* Allow Rewrite Rules *)
let v_compiled_lib =
  v_tuple "compiled" [|v_dp;v_module;v_context_set;v_deps; v_flags|]

(** Toplevel structures in a vo (see Cic.mli) *)

let v_libsum =
  v_tuple_c ("summary", [|v_dp;v_deps;v_string;v_any|])

let v_lib =
  v_tuple_c ("library",[|v_compiled_lib;v_any;v_any|])

let v_delayed_universes =
  v_sum_c ("delayed_universes", 0, [| [| v_unit |]; [| v_context_set |] |])

let v_opaquetable = v_array (v_opt (v_pair v_constr v_delayed_universes))

let v_vmlib = v_tuple "vmlibrary" [|v_dp; v_array v_vm_to_patch|]
