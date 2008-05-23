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
  cl_context : ((global_reference * bool) option * named_declaration) list; 

  cl_params: int;

  (* Context of definitions and properties on defs, will not be shared *)
  cl_props : named_context;
  
  (* The method implementaions as projections. *)
  cl_projs : constant list;
}

type typeclasses = (global_reference, typeclass) Gmap.t

type globality = int option

type instance = {
  is_class: global_reference;
  is_pri: int option;
  is_global: globality;
  (* Sections where the instance should be redeclared, 
     Some n for n sections, None for discard at end of section. *)
  is_impl: constant; 
}

type instances = (global_reference, instance Cmap.t) Gmap.t

let instance_impl is = is.is_impl

let new_instance cl pri glob impl = 
  let global =
    if Lib.sections_are_opened () then 
      if glob then Some (Lib.sections_depth ())
      else None
    else Some 0
  in
    { is_class = cl.cl_impl;
      is_pri = pri ;
      is_global = global ;
      is_impl = impl }
	
let classes : typeclasses ref = ref Gmap.empty

let methods : (constant, global_reference) Gmap.t ref = ref Gmap.empty
  
let instances : instances ref = ref Gmap.empty
  
let freeze () = !classes, !methods, !instances

let unfreeze (cl,m,is) = 
  classes:=cl;
  methods:=m;
  instances:=is
    
let init () =
  classes:= Gmap.empty; 
  methods:= Gmap.empty;
  instances:= Gmap.empty
    
let _ = 
  Summary.declare_summary "classes_and_instances"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_module = false;
      Summary.survive_section = true }

let gmap_merge old ne =
  Gmap.fold (fun k v acc -> Gmap.add k v acc) old ne

let cmap_union = Cmap.fold Cmap.add

let gmap_cmap_merge old ne =
  Gmap.fold (fun cl insts acc -> 
    let oldinsts = try Gmap.find cl old with Not_found -> Cmap.empty in
      Gmap.add cl (cmap_union oldinsts insts) acc)
    Gmap.empty ne
    
let add_instance_hint_ref = ref (fun id pri -> assert false)
let register_add_instance_hint =
  (:=) add_instance_hint_ref
let add_instance_hint id = !add_instance_hint_ref id

let cache (_, (cl, m, inst)) =
  classes := cl;
  methods := m;
  instances := inst
    
let load (_, (cl, m, inst)) =
  classes := gmap_merge !classes cl;
  methods := gmap_merge !methods m;
  instances := gmap_cmap_merge !instances inst

open Libobject

let subst (_,subst,(cl,m,inst)) = 
  let do_subst_con c = fst (Mod_subst.subst_con subst c)
  and do_subst c = Mod_subst.subst_mps subst c
  and do_subst_gr gr = fst (subst_global subst gr)
  in
  let do_subst_named ctx = 
    list_smartmap (fun (na, b, t) ->
      (na, Option.smartmap do_subst b, do_subst t))
      ctx
  in
  let do_subst_ctx ctx = 
    list_smartmap (fun (cl, (na, b, t)) ->
      (Option.smartmap (fun (gr,b) -> do_subst_gr gr, b) cl,
      (na, Option.smartmap do_subst b, do_subst t)))
      ctx
  in
  let do_subst_projs projs = list_smartmap do_subst_con projs in
  let subst_class k cl classes = 
    let k = do_subst_gr k in
    let cl' = { cl with cl_impl = k;
		cl_context = do_subst_ctx cl.cl_context;
		cl_props = do_subst_named cl.cl_props;
		cl_projs = do_subst_projs cl.cl_projs; }
    in 
    let cl' = if cl' = cl then cl else cl' in
      Gmap.add k cl' classes
  in
  let classes = Gmap.fold subst_class cl Gmap.empty in
  let subst_inst k insts instances =
    let k = do_subst_gr k in
    let insts' = 
      Cmap.fold (fun cst is acc -> 
	let cst = do_subst_con cst in
	let is' = { is with is_class = k; is_impl = cst } in
	  Cmap.add cst (if is' = is then is else is') acc) insts Cmap.empty
    in Gmap.add k insts' instances
  in
  let instances = Gmap.fold subst_inst inst Gmap.empty in
    (classes, m, instances)

let discharge (_,(cl,m,inst)) =
  let discharge_named (cl, r) =
    Option.smartmap (fun (gr, b) -> Lib.discharge_global gr, b) cl, r
  in
  let subst_class cl = 
    { cl with cl_impl = Lib.discharge_global cl.cl_impl;
      cl_context = list_smartmap discharge_named cl.cl_context;
      cl_projs = list_smartmap Lib.discharge_con cl.cl_projs }
  in
  let classes = Gmap.map subst_class cl in
  let subst_inst insts =
    Cmap.fold (fun k is acc ->
      let impl = Lib.discharge_con is.is_impl in
      let is = { is with is_class = Lib.discharge_global is.is_class; is_impl = impl } in
	Cmap.add impl is acc)
      insts Cmap.empty;
  in
  let instances = Gmap.map subst_inst inst in
    Some (classes, m, instances)
      
let rebuild (_,(cl,m,inst)) =
  let inst = 
    Gmap.map (fun insts -> 
      Cmap.fold (fun k is insts -> 
	match is.is_global with
	  | None -> insts
	  | Some 0 -> Cmap.add k is insts
	  | Some n -> 
	      add_instance_hint is.is_impl is.is_pri;
	      let is' = { is with is_global = Some (pred n) }
	      in Cmap.add k is' insts) insts Cmap.empty)
      inst
  in (cl, m, inst)

let (input,output) = 
  declare_object
    { (default_object "type classes state") with
      cache_function = cache;
      load_function = (fun _ -> load);
      open_function = (fun _ -> load);
      classify_function = (fun (_,x) -> Substitute x);
      discharge_function = discharge;
      rebuild_function = rebuild;
      subst_function = subst;
      export_function = (fun x -> Some x) }

let update () = 
  Lib.add_anonymous_leaf (input (!classes, !methods, !instances))

let add_class c = 
  classes := Gmap.add c.cl_impl c !classes;
  methods := List.fold_left (fun acc x -> Gmap.add x c.cl_impl acc) !methods c.cl_projs;
  update ()
    
let class_info c = 
  try Gmap.find c !classes
  with _ -> not_a_class (Global.env()) (constr_of_global c)

let instance_constructor cl args = 
  let pars = fst (list_chop (List.length cl.cl_context) args) in
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

let add_instance i =
  let cl = class_info i.is_class in
  instances := cmapl_add cl.cl_impl i !instances;
  add_instance_hint i.is_impl i.is_pri;
  update ()

let instances r = 
  let cl = class_info r in instances_of cl

let solve_instanciation_problem = ref (fun _ _ _ _ -> assert false)
let solve_instanciations_problem = ref (fun _ _ _ _ -> assert false)

let resolve_typeclass env ev evi (evd, defined as acc) =
  try
    assert(evi.evar_body = Evar_empty);
    !solve_instanciation_problem env evd ev evi
  with Exit -> acc

let resolve_one_typeclass env types =
  try
    let evi = Evd.make_evar (Environ.named_context_val env) types in
    let ev = 1 in
    let evm = Evd.add Evd.empty ev evi in
    let evd = Evd.create_evar_defs evm in
    let evd', b = !solve_instanciation_problem env evd ev evi in
      if b then 
	let evm' = Evd.evars_of evd' in
	  match Evd.evar_body (Evd.find evm' ev) with
	      Evar_empty -> raise Not_found
	    | Evar_defined c -> c
      else raise Not_found
  with Exit -> raise Not_found

let resolve_one_typeclass_evd env evd types =
  try
    let ev = Evarutil.e_new_evar evd env types in
    let (ev,_) = destEvar ev in
    let evd', b =
	!solve_instanciation_problem env !evd ev (Evd.find (Evd.evars_of !evd) ev)
    in
      evd := evd';
      if b then 
	let evm' = Evd.evars_of evd' in
	  match Evd.evar_body (Evd.find evm' ev) with
	      Evar_empty -> raise Not_found
	    | Evar_defined c -> Evarutil.nf_evar evm' c
      else raise Not_found
  with Exit -> raise Not_found

let method_typeclass ref = 
  match ref with 
    | ConstRef c -> 
	class_info (Gmap.find c !methods)
    | _ -> raise Not_found
      
let is_class gr = 
  Gmap.fold (fun k v acc -> acc || v.cl_impl = gr) !classes false
  
let is_implicit_arg k = 
  match k with
      ImplicitArg (ref, (n, id)) -> true
    | InternalHole -> true
    | _ -> false

let destClassApp c = 
  match kind_of_term c with
    | App (ki, args) when isInd ki -> 
	Some (destInd ki, args)
    | _ when isInd c -> Some (destInd c, [||])
    | _ -> None

let is_independent evm ev = 
  Evd.fold (fun ev' evi indep -> indep && 
    (ev = ev' || 
	evi.evar_body <> Evar_empty ||
	not (Termops.occur_evar ev evi.evar_concl)))
    evm true
    

(*   try !solve_instanciations_problem env (Evarutil.nf_evar_defs evd) *)
(*   with _ -> *)
(*   let evm = Evd.evars_of evd in *)
(*   let tc_evars =  *)
(*     let f ev evi acc = *)
(*       let (l, k) = Evd.evar_source ev evd in *)
(* 	if not check || is_implicit_arg k then *)
(* 	  match destClassApp evi.evar_concl with *)
(* 	    | Some (i, args) when is_class i ->  *)
(* 		Evd.add acc ev evi *)
(* 	    | _ -> acc *)
(* 	else acc *)
(*     in Evd.fold f evm Evd.empty *)
(*   in *)
(*   let rec sat evars = *)
(*     let evm = Evd.evars_of evars in *)
(*     let (evars', progress) =  *)
(*       Evd.fold  *)
(* 	(fun ev evi acc ->  *)
(* 	  if (Evd.mem tc_evars ev || not (Evd.mem evm ev))  *)
(* 	    && evi.evar_body = Evar_empty then *)
(* 	    resolve_typeclass env ev evi acc  *)
(* 	  else acc) *)
(* 	evm (evars, false)  *)
(*     in *)
(*       if not progress then evars' *)
(*       else *)
(* 	sat (Evarutil.nf_evar_defs evars') *)
(*   in sat (Evarutil.nf_evar_defs evd) *)
  
let class_of_constr c = 
  let extract_cl c =
    try Some (class_info (global_of_constr c)) with _ -> None
  in
    match kind_of_term c with
	App (c, _) -> extract_cl c
      | _ -> extract_cl c

let dest_class_app c =
  let cl c = class_info (global_of_constr c) in
    match kind_of_term c with
	App (c, args) -> cl c, args
      | _ -> cl c, [||]

(* To embed a boolean for resolvability status.
   This is essentially a hack to mark which evars correspond to 
   goals and do not need to be resolved when we have nested [resolve_all_evars] 
   calls (e.g. when doing apply in an External hint in typeclass_instances).
   Would be solved by having real evars-as-goals. *)

let ((bool_in : bool -> Dyn.t),
    (bool_out : Dyn.t -> bool)) = Dyn.create "bool"
  
let is_resolvable evi =
  match evi.evar_extra with
      Some t -> if Dyn.tag t = "bool" then bool_out t else true
    | None -> true
	
let mark_unresolvable evi = 
  { evi with evar_extra = Some (bool_in false) }

let has_typeclasses evd =
  Evd.fold (fun ev evi has -> has || 
    (evi.evar_body = Evar_empty && class_of_constr evi.evar_concl <> None 
	&& is_resolvable evi))
    evd false

let resolve_typeclasses ?(onlyargs=false) ?(fail=true) env sigma evd =
  if not (has_typeclasses sigma) then evd
  else
    !solve_instanciations_problem env (Evarutil.nf_evar_defs evd) onlyargs fail

type substitution = (identifier * constr) list

let substitution_of_named_context isevars env id n subst l = 
  List.fold_right
    (fun (na, _, t) subst -> 
      let t' = replace_vars subst t in
      let b = Evarutil.e_new_evar isevars env ~src:(dummy_loc, ImplicitArg (VarRef id, (n, Some na))) t' in
	(na, b) :: subst)
    l subst

let nf_substitution sigma subst = 
  List.map (function (na, c) -> na, Reductionops.nf_evar sigma c) subst
