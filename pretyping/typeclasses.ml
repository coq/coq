(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: classes.ml 6748 2005-02-18 22:17:50Z herbelin $ i*)

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
  (* Name of the class. FIXME: should not necessarily be globally unique. *)
  cl_name : identifier;

  (* Context in which the definitions are typed. Includes both typeclass parameters and superclasses. *)
  cl_context : ((identifier * bool) option * named_declaration) list; 

  cl_params: int;

  (* Context of definitions and properties on defs, will not be shared *)
  cl_props : named_context;

  (* The class implementation: a record parameterized by the context with defs in it. *)
  cl_impl : inductive; 
}

type typeclasses = (identifier, typeclass) Gmap.t

type instance = {
  is_class: typeclass;
  is_pri: int option;
  is_impl: constant; 
}

type instances = (identifier, instance list) Gmap.t
    
let classes : typeclasses ref = ref Gmap.empty

let methods : (identifier, identifier) Gmap.t ref = ref Gmap.empty
  
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
  Gmap.fold (fun k v acc -> Gmap.add k v acc) ne old

let gmap_list_merge old upd ne =
  let ne = 
    Gmap.fold (fun k v acc -> 
      let oldv = try Gmap.find k old with Not_found -> [] in
      let v' = 
	List.fold_left (fun acc x -> 
	  if not (List.exists (fun y -> y.is_impl = x.is_impl) v) then
	    (x :: acc) else acc)
	v oldv
      in Gmap.add k v' acc)
      ne Gmap.empty
  in
    Gmap.fold (fun k v acc -> 
      let newv = try Gmap.find k ne with Not_found -> [] in
      let v' = 
	List.fold_left (fun acc x -> 
	  if not (List.exists (fun y -> y.is_impl = x.is_impl) acc) then x :: acc else acc)
	  newv v
      in Gmap.add k v' acc)
      old ne

let add_instance_hint_ref = ref (fun id pri -> assert false)
let register_add_instance_hint = (:=) add_instance_hint_ref
let add_instance_hint id = !add_instance_hint_ref id

let qualid_of_con c = 
  Qualid (dummy_loc, shortest_qualid_of_global Idset.empty (ConstRef c))

let cache (_, (cl, m, inst)) =
  classes := gmap_merge !classes cl;
  methods := gmap_merge !methods m;
  instances := gmap_list_merge !instances 
    (fun i -> add_instance_hint (qualid_of_con i.is_impl))
    inst

open Libobject

let subst (_,subst,(cl,m,inst)) = 
  let do_subst_con c = fst (Mod_subst.subst_con subst c)
  and do_subst c = Mod_subst.subst_mps subst c
  and do_subst_ind (kn,i) = (Mod_subst.subst_kn subst kn,i)
  in
  let do_subst_named ctx = 
    List.map (fun (na, b, t) ->
      (na, Option.smartmap do_subst b, do_subst t))
      ctx
  in
  let do_subst_ctx ctx = 
    List.map (fun (cl, (na, b, t)) ->
      (cl, (na, Option.smartmap do_subst b, do_subst t)))
      ctx
  in
  let subst_class cl = 
    let cl' = { cl with cl_impl = do_subst_ind cl.cl_impl;
		cl_context = do_subst_ctx cl.cl_context;
		cl_props = do_subst_named cl.cl_props; }
    in if cl' = cl then cl else cl'
  in
  let subst_inst classes insts =
    List.map (fun is -> 
      let is' = 
	{ is_class = Gmap.find is.is_class.cl_name classes; 
	  is_pri = is.is_pri;
	  is_impl = do_subst_con is.is_impl }
      in if is' = is then is else is') insts
  in
  let classes = Gmap.map subst_class cl in
  let instances = Gmap.map (subst_inst classes) inst in
    (classes, m, instances)

let discharge (_,(cl,m,inst)) =
  let subst_class cl = 
    { cl with cl_impl = Lib.discharge_inductive cl.cl_impl }
  in
  let subst_inst classes insts =
    List.map (fun is -> { is_impl = Lib.discharge_con is.is_impl;
			  is_pri = is.is_pri;
			  is_class = Gmap.find is.is_class.cl_name classes; }) insts
  in
  let classes = Gmap.map subst_class cl in
  let instances = Gmap.map (subst_inst classes) inst in
    Some (classes, m, instances)
  
let (input,output) = 
  declare_object
    { (default_object "type classes state") with
      cache_function = cache;
      load_function = (fun _ -> cache);
      open_function = (fun _ -> cache);
      classify_function = (fun (_,x) -> Substitute x);
      discharge_function = discharge;
      subst_function = subst;
      export_function = (fun x -> Some x) }

let update () = 
  Lib.add_anonymous_leaf (input (!classes, !methods, !instances))

let class_methods cl =
  List.map (function (x, _, _) -> x) cl.cl_props

let add_class c = 
  classes := Gmap.add c.cl_name c !classes;
  methods := List.fold_left (fun acc x -> Gmap.add x c.cl_name acc) !methods (class_methods c);
  update ()
    
let class_info c = 
  Gmap.find c !classes

let class_of_inductive ind = 
  let res = Gmap.fold 
    (fun k v acc -> match acc with None -> if v.cl_impl = ind then Some v else acc | _ -> acc)
    !classes None
  in match res with
      None -> raise Not_found
    | Some cl -> cl

let typeclasses () = Gmap.fold (fun _ l c -> l :: c) !classes []

let gmapl_add x y m =
  try
    let l = Gmap.find x m in
    Gmap.add x (y::Util.list_except y l) m
  with Not_found ->
    Gmap.add x [y] m

let instances_of c = 
  try Gmap.find c.cl_name !instances with Not_found -> []

let add_instance i =
  try
    let cl = Gmap.find i.is_class.cl_name !classes in
      instances := gmapl_add cl.cl_name { i with is_class = cl } !instances;
      add_instance_hint (qualid_of_con i.is_impl) i.is_pri;
      update ()
  with Not_found -> unbound_class (Global.env ()) (dummy_loc, i.is_class.cl_name)

open Libnames
      
let id_of_reference r = 
  let (_, id) = repr_qualid (snd (qualid_of_reference r)) in id

let instances r = 
  let id = id_of_reference r in
    try let cl = class_info id in instances_of cl
    with Not_found -> unbound_class (Global.env()) (loc_of_reference r, id)

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
	let (_, _, l) = Names.repr_con c in
	  class_info (Gmap.find (Names.id_of_label l) !methods)
    | _ -> raise Not_found
      
let is_class ind = 
  Gmap.fold (fun k v acc -> acc || v.cl_impl = ind) !classes false
  
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
  let extract_ind c =
    match kind_of_term c with
	Ind ind -> (try Some (class_of_inductive ind) with Not_found -> None)
      | _ -> None
  in
    match kind_of_term c with
	App (c, _) -> extract_ind c
      | _ -> extract_ind c

let has_typeclasses evd =
  Evd.fold (fun ev evi has -> has || 
    (evi.evar_body = Evar_empty && class_of_constr evi.evar_concl <> None))
    evd false

let resolve_typeclasses ?(onlyargs=false) ?(all=true) env sigma evd =
  if not (has_typeclasses sigma) then evd
  else
    !solve_instanciations_problem env (Evarutil.nf_evar_defs evd) onlyargs all

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
