(* -*- compile-command: "make -C .. bin/coqtop.byte" -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

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

let mismatched_params env n m = mismatched_ctx_inst env Parameters n m
(* let mismatched_defs env n m = mismatched_ctx_inst env Definitions n m *)
let mismatched_props env n m = mismatched_ctx_inst env Properties n m

type rels = constr list

(* This module defines type-classes *)
type typeclass = {
  (* The class implementation *)
  cl_impl : global_reference; 

  (* Context in which the definitions are typed. Includes both typeclass parameters and superclasses. *)
  cl_context : (global_reference * bool) option list * rel_context; 

  (* Context of definitions and properties on defs, will not be shared *)
  cl_props : rel_context;
  
  (* The method implementaions as projections. *)
  cl_projs : (identifier * constant option) list;
}

type typeclasses = (global_reference, typeclass) Gmap.t

type instance = {
  is_class: global_reference;
  is_pri: int option;
  (* Sections where the instance should be redeclared, 
     -1 for discard, 0 for none, mutable to avoid redeclarations 
     when multiple rebuild_object happen. *)
  is_global: int ref;
  is_impl: constant; 
}

type instances = (global_reference, instance Cmap.t) Gmap.t

let instance_impl is = is.is_impl

let new_instance cl pri glob impl = 
  let global =
    if Lib.sections_are_opened () then 
      if glob then Lib.sections_depth ()
      else -1
    else 0
  in
    { is_class = cl.cl_impl;
      is_pri = pri ;
      is_global = ref global ;
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
      Summary.init_function = init;
      Summary.survive_module = false;
      Summary.survive_section = true }

let add_instance_hint_ref = ref (fun id pri -> assert false)
let register_add_instance_hint =
  (:=) add_instance_hint_ref
let add_instance_hint id = !add_instance_hint_ref id

(*
 * classes persistent object
 *)

let load_class (_, cl) =
  classes := Gmap.add cl.cl_impl cl !classes

let cache_class = load_class

let subst_class (_,subst,cl) =
  let do_subst_con c = fst (Mod_subst.subst_con subst c)
  and do_subst c = Mod_subst.subst_mps subst c
  and do_subst_gr gr = fst (subst_global subst gr) in
  let do_subst_ctx ctx = list_smartmap 
    (fun (na, b, t) -> (na, Option.smartmap do_subst b, do_subst t))
    ctx in
  let do_subst_context (grs,ctx) = 
    list_smartmap (Option.smartmap (fun (gr,b) -> do_subst_gr gr, b)) grs,
    do_subst_ctx ctx in
  let do_subst_projs projs = list_smartmap (fun (x, y) -> (x, Option.smartmap do_subst_con y)) projs in
  { cl_impl = do_subst_gr cl.cl_impl;
    cl_context = do_subst_context cl.cl_context;
    cl_props = do_subst_ctx cl.cl_props;
    cl_projs = do_subst_projs cl.cl_projs; }

let discharge_class (_,cl) =
  let rel_of_variable_context ctx = List.fold_right 
    ( fun (n,_,b,t) (ctx', subst) ->
	let decl = (Name n, Option.map (substn_vars 1 subst) b, substn_vars 1 subst t) in
	(decl :: ctx', n :: subst) 
    ) ctx ([], []) in
  let discharge_rel_context subst n rel =
    let ctx, _ =
      List.fold_right
	(fun (id, b, t) (ctx, k) -> 
	   (id, Option.smartmap (substn_vars k subst) b, substn_vars k subst t) :: ctx, succ k)
	rel ([], n)
    in ctx in
  let abs_context cl =
    match cl.cl_impl with
      | VarRef _ | ConstructRef _ -> assert false
      | ConstRef cst -> Lib.section_segment_of_constant cst
      | IndRef (ind,_) -> Lib.section_segment_of_mutual_inductive ind in
  let discharge_context ctx' subst (grs, ctx) =
    let grs' = List.map (fun _ -> None) subst @ 
      list_smartmap (Option.smartmap (fun (gr, b) -> Lib.discharge_global gr, b)) grs
    in grs', discharge_rel_context subst 1 ctx @ ctx' in
  let cl_impl' = Lib.discharge_global cl.cl_impl in
  if cl_impl' == cl.cl_impl then cl else
    let ctx = abs_context cl in
    let ctx, subst = rel_of_variable_context ctx in
    { cl_impl = cl_impl';
      cl_context = discharge_context ctx subst cl.cl_context;
      cl_props = discharge_rel_context subst (succ (List.length (fst cl.cl_context))) cl.cl_props;
      cl_projs = list_smartmap (fun (x, y) -> x, Option.smartmap Lib.discharge_con y) cl.cl_projs }

let rebuild_class cl = cl

let (class_input,class_output) = 
  declare_object
    { (default_object "type classes state") with
      cache_function = cache_class;
      load_function = (fun _ -> load_class);
      open_function = (fun _ -> load_class);
      classify_function = (fun (_,x) -> Substitute x);
      discharge_function = (fun a -> Some (discharge_class a));
      rebuild_function = rebuild_class;
      subst_function = subst_class;
      export_function = (fun x -> Some x) }

let add_class cl =
  Lib.add_anonymous_leaf (class_input cl)


(*
 * instances persistent object
 *)

let load_instance (_,inst) = 
  let insts = 
    try Gmap.find inst.is_class !instances 
    with Not_found -> Cmap.empty in
  let insts = Cmap.add inst.is_impl inst insts in
  instances := Gmap.add inst.is_class insts !instances

let cache_instance = load_instance
let subst_instance (_,subst,inst) = 
  { inst with 
      is_class = fst (subst_global subst inst.is_class);
      is_impl = fst (Mod_subst.subst_con subst inst.is_impl) }

let discharge_instance (_,inst) = 
  { inst with 
      is_class = Lib.discharge_global inst.is_class;
      is_impl = Lib.discharge_con inst.is_impl}

let rebuild_instance inst = 
  match !(inst.is_global) with
    | -1 | 0 -> inst (* TODO : probably a bug here *)
    | n -> add_instance_hint inst.is_impl inst.is_pri;
	inst.is_global := pred n; inst

let (instance_input,instance_output) = 
  declare_object
    { (default_object "type classes instances state") with
      cache_function = cache_instance;
      load_function = (fun _ -> load_instance);
      open_function = (fun _ -> load_instance);
      classify_function = (fun (_,x) -> Substitute x);
      discharge_function = (fun a -> Some (discharge_instance a));
      rebuild_function = rebuild_instance;
      subst_function = subst_instance;
      export_function = (fun x -> Some x) }

let add_instance i =
  Lib.add_anonymous_leaf (instance_input i);
  add_instance_hint i.is_impl i.is_pri

(*
 * interface functions
 *)

let class_info c = 
  try Gmap.find c !classes
  with _ -> not_a_class (Global.env()) (constr_of_global c)

let instance_constructor cl args = 
  let pars = fst (list_chop (List.length (fst cl.cl_context)) args) in
    match cl.cl_impl with
      | IndRef ind -> applistc (mkConstruct (ind, 1)) args,
	  applistc (mkInd ind) pars
      | ConstRef cst -> list_last args, applistc (mkConst cst) pars
      | _ -> assert false
	  
let typeclasses () = Gmap.fold (fun _ l c -> l :: c) !classes []

let cmapl_add x y m =
  try
    let l = Gmap.find x m in
    Gmap.add x (Cmap.add y.is_impl y l) m
  with Not_found ->
    Gmap.add x (Cmap.add y.is_impl y Cmap.empty) m

let cmap_elements c = Cmap.fold (fun k v acc -> v :: acc) c []

let instances_of c = 
  try cmap_elements (Gmap.find c.cl_impl !instances) with Not_found -> []

let all_instances () = 
  Gmap.fold (fun k v acc -> 
    Cmap.fold (fun k v acc -> v :: acc) v acc)
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
  | _ -> false

let is_implicit_arg k = 
  match k with
      ImplicitArg (ref, (n, id), b) -> true
    | InternalHole -> true
    | _ -> false

let global_class_of_constr env c = 
  try class_info (global_of_constr c)
  with Not_found -> not_a_class env c
      
let dest_class_app env c =
  let cl, args = decompose_app c in
    global_class_of_constr env cl, args

let class_of_constr c = try Some (fst (dest_class_app (Global.env ()) c)) with _ -> None

(* To embed a boolean for resolvability status.
   This is essentially a hack to mark which evars correspond to 
   goals and do not need to be resolved when we have nested [resolve_all_evars] 
   calls (e.g. when doing apply in an External hint in typeclass_instances).
   Would be solved by having real evars-as-goals. *)

let ((bool_in : bool -> Dyn.t),
    (bool_out : Dyn.t -> bool)) = Dyn.create "bool"
  
let bool_false = bool_in false

let is_resolvable evi =
  match evi.evar_extra with
      Some t -> if Dyn.tag t = "bool" then bool_out t else true
    | None -> true
	
let mark_unresolvable evi = 
  { evi with evar_extra = Some bool_false }
    
let mark_unresolvables sigma =
  Evd.fold (fun ev evi evs ->
    Evd.add evs ev (mark_unresolvable evi))
    sigma Evd.empty
    
let rec is_class_type evd c =
  match kind_of_term c with
  | Prod (_, _, t) -> is_class_type evd t
  | Evar (e, _) when is_defined evd e -> is_class_type evd (Evarutil.nf_evar evd c)
  | _ -> class_of_constr c <> None

let is_class_evar evd evi = 
  is_class_type evd evi.Evd.evar_concl
    
let has_typeclasses evd =
  Evd.fold (fun ev evi has -> has || 
    (evi.evar_body = Evar_empty && is_class_evar evd evi && is_resolvable evi))
    evd false

let solve_instanciations_problem = ref (fun _ _ _ _ _ -> assert false)
let solve_instanciation_problem = ref (fun _ _ _ -> assert false)

let resolve_typeclasses ?(onlyargs=false) ?(split=true) ?(fail=true) env evd =
  if not (has_typeclasses evd) then evd
  else !solve_instanciations_problem env evd onlyargs split fail

let resolve_one_typeclass env evm t =
  !solve_instanciation_problem env evm t
