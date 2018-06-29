(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i*)
open Names
open Globnames
open Decl_kinds
open Term
open Constr
open Vars
open Evd
open Util
open Typeclasses_errors
open Libobject
open Context.Rel.Declaration

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration
(*i*)

(* Core typeclasses hints *)
type 'a hint_info_gen =
    { hint_priority : int option;
      hint_pattern : 'a option }

type hint_info = (Pattern.patvar list * Pattern.constr_pattern) hint_info_gen

let typeclasses_unique_solutions = ref false
let set_typeclasses_unique_solutions d = (:=) typeclasses_unique_solutions d
let get_typeclasses_unique_solutions () = !typeclasses_unique_solutions

open Goptions

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "check that typeclasses proof search returns unique solutions";
      optkey   = ["Typeclasses";"Unique";"Solutions"];
      optread  = get_typeclasses_unique_solutions;
      optwrite = set_typeclasses_unique_solutions; }

let (add_instance_hint, add_instance_hint_hook) = Hook.make ()
let add_instance_hint id = Hook.get add_instance_hint id

let (remove_instance_hint, remove_instance_hint_hook) = Hook.make ()
let remove_instance_hint id = Hook.get remove_instance_hint id

let (set_typeclass_transparency, set_typeclass_transparency_hook) = Hook.make ()
let set_typeclass_transparency gr local c = Hook.get set_typeclass_transparency gr local c

let (classes_transparent_state, classes_transparent_state_hook) = Hook.make ()
let classes_transparent_state () = Hook.get classes_transparent_state ()

let get_solve_one_instance, solve_one_instance_hook = Hook.make ()

let resolve_one_typeclass ?(unique=get_typeclasses_unique_solutions ()) env evm t =
  Hook.get get_solve_one_instance env evm t unique

type direction = Forward | Backward

(* This module defines type-classes *)
type typeclass = {
  (* Universe quantification *)
  cl_univs : Univ.AUContext.t;

  (* The class implementation *)
  cl_impl : GlobRef.t;

  (* Context in which the definitions are typed. Includes both typeclass parameters and superclasses. *)
  cl_context : GlobRef.t option list * Constr.rel_context;

  (* Context of definitions and properties on defs, will not be shared *)
  cl_props : Constr.rel_context;

  (* The method implementaions as projections. *)
  cl_projs : (Name.t * (direction * hint_info) option
	      * Constant.t option) list;
  
  cl_strict : bool;

  cl_unique : bool;
}

type typeclasses = typeclass Refmap.t

type instance = {
  is_class: GlobRef.t;
  is_info: hint_info;
  (* Sections where the instance should be redeclared,
     None for discard, Some 0 for none. *)
  is_global: int option;
  is_impl: GlobRef.t;
}

type instances = (instance Refmap.t) Refmap.t

let instance_impl is = is.is_impl

let hint_priority is = is.is_info.hint_priority

let new_instance cl info glob impl =
  let global =
    if glob then Some (Lib.sections_depth ())
    else None
  in
  if match global with Some n -> n>0 && isVarRef impl | _ -> false then
    CErrors.user_err (Pp.str "Cannot set Global an instance referring to a section variable.");
    { is_class = cl.cl_impl;
      is_info = info ;
      is_global = global ;
      is_impl = impl }

(*
 * states management
 *)

let classes : typeclasses ref = Summary.ref Refmap.empty ~name:"classes"
let instances : instances ref = Summary.ref Refmap.empty ~name:"instances"

let typeclass_univ_instance (cl, u) =
  assert (Univ.AUContext.size cl.cl_univs == Univ.Instance.length u);
  let subst_ctx c = Context.Rel.map (subst_instance_constr u) c in
    { cl with cl_context = on_snd subst_ctx cl.cl_context;
      cl_props = subst_ctx cl.cl_props}

let class_info c =
  try Refmap.find c !classes
  with Not_found -> not_a_class (Global.env()) (EConstr.of_constr (printable_constr_of_global c))

let global_class_of_constr env sigma c =
  try let gr, u = Termops.global_of_constr sigma c in
	class_info gr, u
  with Not_found -> not_a_class env c

let dest_class_app env sigma c =
  let cl, args = EConstr.decompose_app sigma c in
    global_class_of_constr env sigma cl, (List.map EConstr.Unsafe.to_constr args)

let dest_class_arity env sigma c =
  let open EConstr in
  let rels, c = decompose_prod_assum sigma c in
    rels, dest_class_app env sigma c

let class_of_constr sigma c =
  try Some (dest_class_arity (Global.env ()) sigma c)
  with e when CErrors.noncritical e -> None

let is_class_constr sigma c = 
  try let gr, u = Termops.global_of_constr sigma c in
	Refmap.mem gr !classes
  with Not_found -> false

let rec is_class_type evd c =
  let c, _ = Termops.decompose_app_vect evd c in
    match EConstr.kind evd c with
    | Prod (_, _, t) -> is_class_type evd t
    | Cast (t, _, _) -> is_class_type evd t
    | _ -> is_class_constr evd c
      
let is_class_evar evd evi =
  is_class_type evd evi.Evd.evar_concl

(*
 * classes persistent object
 *)

let load_class (_, cl) =
  classes := Refmap.add cl.cl_impl cl !classes

let cache_class = load_class

let subst_class (subst,cl) =
  let do_subst_con c = Mod_subst.subst_constant subst c
  and do_subst c = Mod_subst.subst_mps subst c
  and do_subst_gr gr = fst (subst_global subst gr) in
  let do_subst_ctx = List.Smart.map (RelDecl.map_constr do_subst) in
  let do_subst_context (grs,ctx) =
    List.Smart.map (Option.Smart.map do_subst_gr) grs,
    do_subst_ctx ctx in
  let do_subst_projs projs = List.Smart.map (fun (x, y, z) ->
    (x, y, Option.Smart.map do_subst_con z)) projs in
  { cl_univs = cl.cl_univs;
    cl_impl = do_subst_gr cl.cl_impl;
    cl_context = do_subst_context cl.cl_context;
    cl_props = do_subst_ctx cl.cl_props;
    cl_projs = do_subst_projs cl.cl_projs;
    cl_strict = cl.cl_strict;
    cl_unique = cl.cl_unique }

let discharge_class (_,cl) =
  let repl = Lib.replacement_context () in
  let rel_of_variable_context ctx = List.fold_right
    ( fun (decl,_) (ctx', subst) ->
        let decl' = decl |> NamedDecl.map_constr (substn_vars 1 subst) |> NamedDecl.to_rel_decl in
	(decl' :: ctx', NamedDecl.get_id decl :: subst)
    ) ctx ([], []) in
  let discharge_rel_context (subst, usubst) n rel =
    let rel = Context.Rel.map (Cooking.expmod_constr repl) rel in
    let fold decl (ctx, k) =
      let map c = subst_univs_level_constr usubst (substn_vars k subst c) in
      RelDecl.map_constr map decl :: ctx, succ k
    in
    let ctx, _ = List.fold_right fold rel ([], n) in
    ctx
  in
  let abs_context cl =
    match cl.cl_impl with
      | VarRef _ | ConstructRef _ -> assert false
      | ConstRef cst -> Lib.section_segment_of_constant cst
      | IndRef (ind,_) -> Lib.section_segment_of_mutual_inductive ind in
  let discharge_context ctx' subst (grs, ctx) =
    let grs' =
      let newgrs = List.map (fun decl ->
			     match decl |> RelDecl.get_type |> EConstr.of_constr |> class_of_constr Evd.empty with
			     | None -> None
                             | Some (_, ((tc,_), _)) -> Some tc.cl_impl)
			    ctx'
      in
      List.Smart.map (Option.Smart.map Lib.discharge_global) grs
      @ newgrs
    in grs', discharge_rel_context subst 1 ctx @ ctx' in
  let cl_impl' = Lib.discharge_global cl.cl_impl in
  if cl_impl' == cl.cl_impl then cl else
    let info = abs_context cl in
    let ctx = info.Lib.abstr_ctx in
    let ctx, subst = rel_of_variable_context ctx in
    let usubst, cl_univs' = Lib.discharge_abstract_universe_context info cl.cl_univs in
    let context = discharge_context ctx (subst, usubst) cl.cl_context in
    let props = discharge_rel_context (subst, usubst) (succ (List.length (fst cl.cl_context))) cl.cl_props in
    let discharge_proj (x, y, z) = x, y, Option.Smart.map Lib.discharge_con z in
      { cl_univs = cl_univs';
        cl_impl = cl_impl';
	cl_context = context;
	cl_props = props;
        cl_projs = List.Smart.map discharge_proj cl.cl_projs;
	cl_strict = cl.cl_strict;
	cl_unique = cl.cl_unique
      }

let rebuild_class cl = 
  try 
    let cst = Tacred.evaluable_of_global_reference (Global.env ()) cl.cl_impl in
      set_typeclass_transparency cst false false; cl
  with e when CErrors.noncritical e -> cl

let class_input : typeclass -> obj =
  declare_object
    { (default_object "type classes state") with
      cache_function = cache_class;
      load_function = (fun _ -> load_class);
      open_function = (fun _ -> load_class);
      classify_function = (fun x -> Substitute x);
      discharge_function = (fun a -> Some (discharge_class a));
      rebuild_function = rebuild_class;
      subst_function = subst_class }

let add_class cl =
  Lib.add_anonymous_leaf (class_input cl)

(** Build the subinstances hints. *)

let check_instance env sigma c =
  try 
    let (evd, c) = resolve_one_typeclass env sigma
      (Retyping.get_type_of env sigma c) in
      not (Evd.has_undefined evd)
  with e when CErrors.noncritical e -> false

let build_subclasses ~check env sigma glob { hint_priority = pri } =
  let _id = Nametab.basename_of_global glob in
  let _next_id = 
    let i = ref (-1) in 
      (fun () -> incr i;
        Nameops.add_suffix _id ("_subinstance_" ^ string_of_int !i))
  in
  let ty, ctx = Global.type_of_global_in_context env glob in
  let inst, ctx = UnivGen.fresh_instance_from ctx None in
  let ty = Vars.subst_instance_constr inst ty in
  let ty = EConstr.of_constr ty in
  let sigma = Evd.merge_context_set Evd.univ_rigid sigma ctx in
  let rec aux pri c ty path =
      match class_of_constr sigma ty with
      | None -> []
      | Some (rels, ((tc,u), args)) ->
	let instapp = 
	  Reductionops.whd_beta sigma (EConstr.of_constr (appvectc c (Context.Rel.to_extended_vect mkRel 0 rels)))
	in
	let instapp = EConstr.Unsafe.to_constr instapp in
	let projargs = Array.of_list (args @ [instapp]) in
	let projs = List.map_filter 
	  (fun (n, b, proj) ->
	   match b with 
	   | None -> None
	   | Some (Backward, _) -> None
	   | Some (Forward, info) ->
	     let proj = Option.get proj in
	     let rels = List.map (fun d -> Termops.map_rel_decl EConstr.Unsafe.to_constr d) rels in
	     let u = EConstr.EInstance.kind sigma u in
	     let body = it_mkLambda_or_LetIn (mkApp (mkConstU (proj,u), projargs)) rels in
	       if check && check_instance env sigma (EConstr.of_constr body) then None
	       else 
		 let newpri =
		   match pri, info.hint_priority with
		   | Some p, Some p' -> Some (p + p')
		   | Some p, None -> Some (p + 1)
		   | _, _ -> None
		 in
		   Some (ConstRef proj, { info with hint_priority = newpri }, body)) tc.cl_projs
	in
	let declare_proj hints (cref, info, body) =
	  let path' = cref :: path in
	  let ty = Retyping.get_type_of env sigma (EConstr.of_constr body) in
	  let rest = aux pri body ty path' in
	    hints @ (path', info, body) :: rest
	in List.fold_left declare_proj [] projs 
  in
  let term = UnivGen.constr_of_global_univ (glob, inst) in
    (*FIXME subclasses should now get substituted for each particular instance of
      the polymorphic superclass *)
    aux pri term ty [glob]

(*
 * instances persistent object
 *)

type instance_action = 
  | AddInstance
  | RemoveInstance

let load_instance inst = 
  let insts = 
    try Refmap.find inst.is_class !instances
    with Not_found -> Refmap.empty in
  let insts = Refmap.add inst.is_impl inst insts in
  instances := Refmap.add inst.is_class insts !instances

let remove_instance inst =
  let insts = 
    try Refmap.find inst.is_class !instances
    with Not_found -> assert false in
  let insts = Refmap.remove inst.is_impl insts in
  instances := Refmap.add inst.is_class insts !instances

let cache_instance (_, (action, i)) =
  match action with 
  | AddInstance -> load_instance i
  | RemoveInstance -> remove_instance i      

let subst_instance (subst, (action, inst)) = action,
  { inst with 
      is_class = fst (subst_global subst inst.is_class);
      is_impl = fst (subst_global subst inst.is_impl) }

let discharge_instance (_, (action, inst)) =
  match inst.is_global with
  | None -> None
  | Some n ->
    assert (not (isVarRef inst.is_impl));
    Some (action,
    { inst with 
      is_global = Some (pred n);
      is_class = Lib.discharge_global inst.is_class;
      is_impl = Lib.discharge_global inst.is_impl })
    

let is_local i = (i.is_global == None)

let is_local_for_hint i =
  match i.is_global with
  | None -> true  (* i.e. either no Global keyword not in section, or in section *)
  | Some n -> n <> 0 (* i.e. in a section, declare the hint as local
     since discharge is managed by rebuild_instance which calls again
     add_instance_hint; don't ask hints to take discharge into account
     itself *)

let add_instance check inst =
  let poly = Global.is_polymorphic inst.is_impl in
  let local = is_local_for_hint inst in
  add_instance_hint (IsGlobal inst.is_impl) [inst.is_impl] local
    inst.is_info poly;
  List.iter (fun (path, pri, c) -> add_instance_hint (IsConstr c) path
    local pri poly)
    (build_subclasses ~check:(check && not (isVarRef inst.is_impl))
       (Global.env ()) (Evd.from_env (Global.env ())) inst.is_impl inst.is_info)

let rebuild_instance (action, inst) =
  let () = match action with
  | AddInstance -> add_instance true inst
  | _ -> ()
  in
  (action, inst)

let classify_instance (action, inst) =
  if is_local inst then Dispose
  else Substitute (action, inst)

let instance_input : instance_action * instance -> obj =
  declare_object
    { (default_object "type classes instances state") with
      cache_function = cache_instance;
      load_function = (fun _ x -> cache_instance x);
      open_function = (fun _ x -> cache_instance x);
      classify_function = classify_instance;
      discharge_function = discharge_instance;
      rebuild_function = rebuild_instance;
      subst_function = subst_instance }

let add_instance i =
  Lib.add_anonymous_leaf (instance_input (AddInstance, i));
  add_instance true i

let remove_instance i =
  Lib.add_anonymous_leaf (instance_input (RemoveInstance, i));
  remove_instance_hint i.is_impl

let declare_instance info local glob =
  let ty, _ = Global.type_of_global_in_context (Global.env ()) glob in
  let info = Option.default {hint_priority = None; hint_pattern = None} info in
    match class_of_constr Evd.empty (EConstr.of_constr ty) with
    | Some (rels, ((tc,_), args) as _cl) ->
      assert (not (isVarRef glob) || local);
      add_instance (new_instance tc info (not local) glob)
    | None -> ()

let add_class cl =
  add_class cl;
  List.iter (fun (n, inst, body) ->
	     match inst with
	     | Some (Backward, info) ->
	       (match body with
	       | None -> CErrors.user_err Pp.(str "Non-definable projection can not be declared as a subinstance")
	       | Some b -> declare_instance (Some info) false (ConstRef b))
	     | _ -> ())
  cl.cl_projs


      
(*
 * interface functions
 *)

let instance_constructor (cl,u) args =
  let lenpars = List.count is_local_assum (snd cl.cl_context) in
  let open EConstr in
  let pars = fst (List.chop lenpars args) in
    match cl.cl_impl with
      | IndRef ind -> 
        let ind = ind, u in
          (Some (applist (mkConstructUi (ind, 1), args)),
           applist (mkIndU ind, pars))
      | ConstRef cst -> 
        let cst = cst, u in
	let term = match args with
	  | [] -> None
	  | _ -> Some (List.last args)
	in
          (term, applist (mkConstU cst, pars))
      | _ -> assert false

let typeclasses () = Refmap.fold (fun _ l c -> l :: c) !classes []

let cmap_elements c = Refmap.fold (fun k v acc -> v :: acc) c []

let instances_of c =
  try cmap_elements (Refmap.find c.cl_impl !instances) with Not_found -> []

let all_instances () = 
  Refmap.fold (fun k v acc ->
    Refmap.fold (fun k v acc -> v :: acc) v acc)
    !instances []

let instances r = 
  let cl = class_info r in instances_of cl    

let is_class gr = 
  Refmap.exists (fun _ v -> GlobRef.equal v.cl_impl gr) !classes

let is_instance = function
  | ConstRef c ->
      (match Decls.constant_kind c with
      | IsDefinition Instance -> true
      | _ -> false)
  | VarRef v ->
      (match Decls.variable_kind v with
      | IsDefinition Instance -> true
      | _ -> false)
  | ConstructRef (ind,_) -> 
      is_class (IndRef ind)
  | _ -> false

(* To embed a boolean for resolvability status.
   This is essentially a hack to mark which evars correspond to
   goals and do not need to be resolved when we have nested [resolve_all_evars]
   calls (e.g. when doing apply in an External hint in typeclass_instances).
   Would be solved by having real evars-as-goals.

   Nota: we will only check the resolvability status of undefined evars.
 *)

let resolvable = Proofview.Unsafe.typeclass_resolvable

let set_resolvable s b =
  if b then Store.remove s resolvable
  else Store.set s resolvable ()

let is_resolvable evi =
  assert (match evi.evar_body with Evar_empty -> true | _ -> false);
  Option.is_empty (Store.get evi.evar_extra resolvable)

let mark_resolvability_undef b evi =
  if is_resolvable evi == (b : bool) then evi
  else
    let t = set_resolvable evi.evar_extra b in
    { evi with evar_extra = t }

let mark_resolvability b evi =
  assert (match evi.evar_body with Evar_empty -> true | _ -> false);
  mark_resolvability_undef b evi

let mark_unresolvable evi = mark_resolvability false evi
let mark_resolvable evi = mark_resolvability true evi

open Evar_kinds
type evar_filter = Evar.t -> Evar_kinds.t -> bool

let all_evars _ _ = true
let all_goals _ = function VarInstance _ | GoalEvar -> true | _ -> false
let no_goals ev evi = not (all_goals ev evi)
let no_goals_or_obligations _ = function
  | VarInstance _ | GoalEvar | QuestionMark _ -> false
  | _ -> true

let mark_resolvability filter b sigma =
  let map ev evi =
    if filter ev (snd evi.evar_source) then mark_resolvability_undef b evi
    else evi
  in
  Evd.raw_map_undefined map sigma

let mark_unresolvables ?(filter=all_evars) sigma = mark_resolvability filter false sigma
let mark_resolvables ?(filter=all_evars) sigma = mark_resolvability filter true sigma

let has_typeclasses filter evd =
  let check ev evi =
    filter ev (snd evi.evar_source) && is_resolvable evi && is_class_evar evd evi
  in
  Evar.Map.exists check (Evd.undefined_map evd)

let get_solve_all_instances, solve_all_instances_hook = Hook.make ()

let solve_all_instances env evd filter unique split fail =
  Hook.get get_solve_all_instances env evd filter unique split fail

(** Profiling resolution of typeclasses *)
(* let solve_classeskey = CProfile.declare_profile "solve_typeclasses" *)
(* let solve_problem = CProfile.profile5 solve_classeskey solve_problem *)

let resolve_typeclasses ?(fast_path = true) ?(filter=no_goals) ?(unique=get_typeclasses_unique_solutions ())
    ?(split=true) ?(fail=true) env evd =
  if fast_path && not (has_typeclasses filter evd) then evd
  else solve_all_instances env evd filter unique split fail
