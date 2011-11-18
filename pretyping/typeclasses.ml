(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Names
open Libnames
open Decl_kinds
open Term
open Sign
open Evd
open Environ
open Nametab
open Mod_subst
open Util
open Typeclasses_errors
open Libobject
(*i*)


let add_instance_hint_ref = ref (fun id local pri -> assert false)
let register_add_instance_hint =
  (:=) add_instance_hint_ref
let add_instance_hint id = !add_instance_hint_ref id

let remove_instance_hint_ref = ref (fun id -> assert false)
let register_remove_instance_hint =
  (:=) remove_instance_hint_ref
let remove_instance_hint id = !remove_instance_hint_ref id

let set_typeclass_transparency_ref = ref (fun id local c -> assert false)
let register_set_typeclass_transparency =
  (:=) set_typeclass_transparency_ref
let set_typeclass_transparency gr local c = !set_typeclass_transparency_ref gr local c

let classes_transparent_state_ref = ref (fun () -> assert false)
let register_classes_transparent_state = (:=) classes_transparent_state_ref
let classes_transparent_state () = !classes_transparent_state_ref ()

let solve_instanciation_problem = ref (fun _ _ _ -> assert false)

let resolve_one_typeclass env evm t =
  !solve_instanciation_problem env evm t

type rels = constr list
type direction = Forward | Backward

(* This module defines type-classes *)
type typeclass = {
  (* The class implementation *)
  cl_impl : global_reference;

  (* Context in which the definitions are typed. Includes both typeclass parameters and superclasses. *)
  cl_context : (global_reference * bool) option list * rel_context;

  (* Context of definitions and properties on defs, will not be shared *)
  cl_props : rel_context;

  (* The method implementaions as projections. *)
  cl_projs : (name * (direction * int option) option * constant option) list;
}

module Gmap = Fmap.Make(RefOrdered)

type typeclasses = typeclass Gmap.t

type instance = {
  is_class: global_reference;
  is_pri: int option;
  (* Sections where the instance should be redeclared,
     -1 for discard, 0 for none, mutable to avoid redeclarations
     when multiple rebuild_object happen. *)
  is_global: int;
  is_impl: global_reference;
}

type instances = (instance Gmap.t) Gmap.t

let instance_impl is = is.is_impl

let new_instance cl pri glob impl =
  let global =
    if glob then Lib.sections_depth ()
    else -1
  in
    { is_class = cl.cl_impl;
      is_pri = pri ;
      is_global = global ;
      is_impl = impl }

(*
 * states management
 *)

let classes : typeclasses ref = ref Gmap.empty

let instances : instances ref = ref Gmap.empty

let freeze () = !classes, !instances

let unfreeze (cl,is) =
  classes:=cl;
  instances:=is

let init () =
  classes:= Gmap.empty;
  instances:= Gmap.empty

let _ =
  Summary.declare_summary "classes_and_instances"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init }

let class_info c =
  try Gmap.find c !classes
  with _ -> not_a_class (Global.env()) (constr_of_global c)

let global_class_of_constr env c =
  try class_info (global_of_constr c)
  with Not_found -> not_a_class env c

let dest_class_app env c =
  let cl, args = decompose_app c in
    global_class_of_constr env cl, args

let dest_class_arity env c =
  let rels, c = Term.decompose_prod_assum c in
    rels, dest_class_app env c

let class_of_constr c = try Some (dest_class_arity (Global.env ()) c) with _ -> None

let rec is_class_type evd c =
  match kind_of_term c with
  | Prod (_, _, t) -> is_class_type evd t
  | Evar (e, _) when is_defined evd e -> is_class_type evd (Evarutil.nf_evar evd c)
  | _ -> class_of_constr c <> None

let is_class_evar evd evi =
  is_class_type evd evi.Evd.evar_concl

(*
 * classes persistent object
 *)

let load_class (_, cl) =
  classes := Gmap.add cl.cl_impl cl !classes

let cache_class = load_class

let subst_class (subst,cl) =
  let do_subst_con c = fst (Mod_subst.subst_con subst c)
  and do_subst c = Mod_subst.subst_mps subst c
  and do_subst_gr gr = fst (subst_global subst gr) in
  let do_subst_ctx ctx = list_smartmap
    (fun (na, b, t) -> (na, Option.smartmap do_subst b, do_subst t))
    ctx in
  let do_subst_context (grs,ctx) =
    list_smartmap (Option.smartmap (fun (gr,b) -> do_subst_gr gr, b)) grs,
    do_subst_ctx ctx in
  let do_subst_projs projs = list_smartmap (fun (x, y, z) -> (x, y, Option.smartmap do_subst_con z)) projs in
  { cl_impl = do_subst_gr cl.cl_impl;
    cl_context = do_subst_context cl.cl_context;
    cl_props = do_subst_ctx cl.cl_props;
    cl_projs = do_subst_projs cl.cl_projs; }

let discharge_class (_,cl) =
  let repl = Lib.replacement_context () in
  let rel_of_variable_context ctx = List.fold_right
    ( fun (n,_,b,t) (ctx', subst) ->
	let decl = (Name n, Option.map (substn_vars 1 subst) b, substn_vars 1 subst t) in
	(decl :: ctx', n :: subst)
    ) ctx ([], []) in
  let discharge_rel_context subst n rel =
    let rel = map_rel_context (Cooking.expmod_constr repl) rel in
    let ctx, _ =
      List.fold_right
	(fun (id, b, t) (ctx, k) ->
	   (id, Option.smartmap (substn_vars k subst) b, substn_vars k subst t) :: ctx, succ k)
	rel ([], n)
    in ctx
  in
  let abs_context cl =
    match cl.cl_impl with
      | VarRef _ | ConstructRef _ -> assert false
      | ConstRef cst -> Lib.section_segment_of_constant cst
      | IndRef (ind,_) -> Lib.section_segment_of_mutual_inductive ind in
  let discharge_context ctx' subst (grs, ctx) =
    let grs' = 
      let newgrs = List.map (fun (_, _, t) -> 
	match class_of_constr t with
	| None -> None
	| Some (_, (tc, _)) -> Some (tc.cl_impl, true))
	ctx' 
      in
	list_smartmap (Option.smartmap (fun (gr, b) -> Lib.discharge_global gr, b)) grs
	  @ newgrs
    in grs', discharge_rel_context subst 1 ctx @ ctx' in
  let cl_impl' = Lib.discharge_global cl.cl_impl in
  if cl_impl' == cl.cl_impl then cl else
    let ctx = abs_context cl in
    let ctx, subst = rel_of_variable_context ctx in
    let context = discharge_context ctx subst cl.cl_context in
    let props = discharge_rel_context subst (succ (List.length (fst cl.cl_context))) cl.cl_props in
    { cl_impl = cl_impl';
      cl_context = context;
      cl_props = props;
      cl_projs = list_smartmap (fun (x, y, z) -> x, y, Option.smartmap Lib.discharge_con z) cl.cl_projs }

let rebuild_class cl = 
  try 
    let cst = Tacred.evaluable_of_global_reference (Global.env ()) cl.cl_impl in
      set_typeclass_transparency cst false false; cl
  with _ -> cl

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
      Evd.is_empty (Evd.undefined_evars evd)
  with _ -> false

let build_subclasses ~check env sigma glob pri =
  let rec aux pri c =
    let ty = Evarutil.nf_evar sigma (Retyping.get_type_of env sigma c) in
      match class_of_constr ty with
      | None -> []
      | Some (rels, (tc, args)) ->
	let instapp = Reductionops.whd_beta sigma (appvectc c (Termops.extended_rel_vect 0 rels)) in
	let projargs = Array.of_list (args @ [instapp]) in
	let projs = list_map_filter 
	  (fun (n, b, proj) ->
	   match b with 
	   | None -> None
	   | Some (Backward, _) -> None
	   | Some (Forward, pri') ->
	     let proj = Option.get proj in
	     let body = it_mkLambda_or_LetIn (mkApp (mkConst proj, projargs)) rels in
	       if check && check_instance env sigma body then None
	       else 
		 let pri = 
		   match pri, pri' with
		   | Some p, Some p' -> Some (p + p')
		   | Some p, None -> Some (p + 1)
		   | _, _ -> None
		 in
		   Some (ConstRef proj, pri, body)) tc.cl_projs 
	in
	let declare_proj hints (cref, pri, body) =
	  let rest = aux pri body in
	    hints @ (pri, body) :: rest
	in List.fold_left declare_proj [] projs 
  in aux pri (constr_of_global glob)

(*
 * instances persistent object
 *)

type instance_action = 
  | AddInstance
  | RemoveInstance

let load_instance inst = 
  let insts = 
    try Gmap.find inst.is_class !instances 
    with Not_found -> Gmap.empty in
  let insts = Gmap.add inst.is_impl inst insts in
  instances := Gmap.add inst.is_class insts !instances

let remove_instance inst =
  let insts = 
    try Gmap.find inst.is_class !instances 
    with Not_found -> assert false in
  let insts = Gmap.remove inst.is_impl insts in
  instances := Gmap.add inst.is_class insts !instances

let cache_instance (_, (action, i)) =
  match action with 
  | AddInstance -> load_instance i
  | RemoveInstance -> remove_instance i      

let subst_instance (subst, (action, inst)) = action,
  { inst with 
      is_class = fst (subst_global subst inst.is_class);
      is_impl = fst (subst_global subst inst.is_impl) }

let discharge_instance (_, (action, inst)) =
  if inst.is_global <= 0 then None
  else Some (action,
    { inst with 
      is_global = pred inst.is_global;
      is_class = Lib.discharge_global inst.is_class;
      is_impl = Lib.discharge_global inst.is_impl })
    

let is_local i = i.is_global = -1

let add_instance check inst =
  add_instance_hint (constr_of_global inst.is_impl) (is_local inst) inst.is_pri;
  List.iter (fun (pri, c) -> add_instance_hint c (is_local inst) pri) 
    (build_subclasses ~check:(check && not (isVarRef inst.is_impl))
       (Global.env ()) Evd.empty inst.is_impl inst.is_pri)

let rebuild_instance (action, inst) =
  if action = AddInstance then add_instance true inst;
  (action, inst)

let classify_instance (action, inst) =
  if is_local inst then Dispose
  else Substitute (action, inst)

let load_instance (_, (action, inst) as ai) =
  cache_instance ai;
  if action = AddInstance then
    add_instance_hint (constr_of_global inst.is_impl) (is_local inst) inst.is_pri

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

let declare_instance pri local glob =
  let c = constr_of_global glob in
  let ty = Retyping.get_type_of (Global.env ()) Evd.empty c in
    match class_of_constr ty with
    | Some (rels, (tc, args) as _cl) ->
      add_instance (new_instance tc pri (not local) glob)
(*       let path, hints = build_subclasses (not local) (Global.env ()) Evd.empty glob in *)
(*       let entries = List.map (fun (path, pri, c) -> (pri, local, path, c)) hints in *)
(* 	Auto.add_hints local [typeclasses_db] (Auto.HintsResolveEntry entries); *)
(* 	Auto.add_hints local [typeclasses_db]  *)
(* 	(Auto.HintsCutEntry (PathSeq (PathStar (PathAtom PathAny), path))) *)
    | None -> ()

let add_class cl =
  add_class cl;
  List.iter (fun (n, inst, body) ->
	     match inst with
	     | Some (Backward, pri) ->
	       declare_instance pri false (ConstRef (Option.get body))
	     | _ -> ())
  cl.cl_projs


open Declarations

let add_constant_class cst =
  let ty = Typeops.type_of_constant (Global.env ()) cst in
  let ctx, arity = decompose_prod_assum ty in
  let tc = 
    { cl_impl = ConstRef cst;
      cl_context = (List.map (const None) ctx, ctx);
      cl_props = [(Anonymous, None, arity)];
      cl_projs = []
    }
  in add_class tc;
    set_typeclass_transparency (EvalConstRef cst) false false
      
let add_inductive_class ind =
  let mind, oneind = Global.lookup_inductive ind in
  let k =
    let ctx = oneind.mind_arity_ctxt in
    let ty = Inductive.type_of_inductive_knowing_parameters
      (push_rel_context ctx (Global.env ()))
	  oneind (Termops.extended_rel_vect 0 ctx)
    in
      { cl_impl = IndRef ind;
	cl_context = List.map (const None) ctx, ctx;
	cl_props = [Anonymous, None, ty];
	cl_projs = [] }
  in add_class k
      
(*
 * interface functions
 *)

let instance_constructor cl args =
  let lenpars = List.length (List.filter (fun (na, b, t) -> b = None) (snd cl.cl_context)) in
  let pars = fst (list_chop lenpars args) in
    match cl.cl_impl with
      | IndRef ind -> Some (applistc (mkConstruct (ind, 1)) args),
	  applistc (mkInd ind) pars
      | ConstRef cst -> 
	let term = if args = [] then None else Some (list_last args) in
	  term, applistc (mkConst cst) pars
      | _ -> assert false

let typeclasses () = Gmap.fold (fun _ l c -> l :: c) !classes []

let cmap_elements c = Gmap.fold (fun k v acc -> v :: acc) c []

let instances_of c =
  try cmap_elements (Gmap.find c.cl_impl !instances) with Not_found -> []

let all_instances () = 
  Gmap.fold (fun k v acc -> 
    Gmap.fold (fun k v acc -> v :: acc) v acc)
    !instances []

let instances r = 
  let cl = class_info r in instances_of cl    
      
let is_class gr = 
  Gmap.fold (fun k v acc -> acc || v.cl_impl = gr) !classes false

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

let is_implicit_arg k =
  match k with
      ImplicitArg (ref, (n, id), b) -> true
    | InternalHole -> true
    | _ -> false


(* To embed a boolean for resolvability status.
   This is essentially a hack to mark which evars correspond to
   goals and do not need to be resolved when we have nested [resolve_all_evars]
   calls (e.g. when doing apply in an External hint in typeclass_instances).
   Would be solved by having real evars-as-goals.

   Nota: we will only check the resolvability status of undefined evars.
 *)

let resolvable = Store.field ()
open Store.Field

let is_resolvable evi =
  assert (evi.evar_body = Evar_empty);
  Option.default true (resolvable.get evi.evar_extra)

let mark_unresolvable_undef evi =
  let t = resolvable.set false evi.evar_extra in
  { evi with evar_extra = t }

let mark_unresolvable evi =
  assert (evi.evar_body = Evar_empty);
  mark_unresolvable_undef evi

let mark_unresolvables sigma =
  Evd.fold_undefined (fun ev evi evs ->
    Evd.add evs ev (mark_unresolvable_undef evi))
    sigma (Evd.defined_evars sigma)

let has_typeclasses evd =
  Evd.fold_undefined (fun ev evi has -> has ||
    (is_class_evar evd evi && is_resolvable evi))
    evd false

let solve_instanciations_problem = ref (fun _ _ _ _ _ -> assert false)

let resolve_typeclasses ?(onlyargs=false) ?(split=true) ?(fail=true) env evd =
  if not (has_typeclasses evd) then evd
  else !solve_instanciations_problem env evd onlyargs split fail
