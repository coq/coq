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
  cl_name : identifier; (* Name of the class *)
  cl_params : named_context; (* Context of the parameters (usually types) *)
  cl_super : named_context; (* Superclasses applied to some of the params *)
(*   cl_defs : named_context; (\* Context of the definitions (usually functions), which may be shared *\) *)
  cl_props : named_context; (* Context of the properties on defs, in Prop, will not be shared *)
  cl_impl : inductive; (* The class implementation: a record parameterized by params and defs *)
}

type typeclasses = (identifier, typeclass) Gmap.t

type instance = {
  is_class: typeclass;
  is_name: identifier; (* Name of the instance *)
(*   is_params: named_context; (\* Context of the parameters, instanciated *\) *)
(*   is_super: named_context; (\* The corresponding superclasses *\) *)
(*   is_defs: named_context; (\* Context of the definitions, instanciated *\) *)
  is_impl: constant; 
(*   is_add_hint : unit -> unit; (\* Hook to add an hint for the instance *\) *)
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
      Summary.survive_module = true;
      Summary.survive_section = true }

let gmap_merge old ne =
  Gmap.fold (fun k v acc -> Gmap.add k v acc) ne old

let gmap_list_merge old ne =
  Gmap.fold (fun k v acc -> 
    let oldv = try Gmap.find k acc with Not_found -> [] in
    let v' = 
      List.fold_left (fun acc x -> 
	if not (List.exists (fun y -> y.is_name = x.is_name) v) then x :: acc else acc)
	v oldv
    in Gmap.add k v' acc)
    ne Gmap.empty

let cache (_, (cl, m, inst)) =
  classes := gmap_merge !classes cl;
  methods := gmap_merge !methods m;
  instances := gmap_list_merge !instances inst

open Libobject

let subst (_,subst,(cl,m,inst)) = 
  let do_subst_con c = fst (Mod_subst.subst_con subst c)
  and do_subst_ind (kn,i) = (Mod_subst.subst_kn subst kn,i)
  in
  let subst_class cl = 
    { cl with cl_impl = do_subst_ind cl.cl_impl }
  in
  let subst_inst insts =
    List.map (fun is -> { is with is_impl = do_subst_con is.is_impl }) insts
  in
  let classes = Gmap.map subst_class cl in
  let instances = Gmap.map subst_inst inst in
    (classes, m, instances)

let discharge (_,(cl,m,inst)) =
  let subst_class cl = 
    { cl with cl_impl = Lib.discharge_inductive cl.cl_impl }
  in
  let subst_inst insts =
    List.map (fun is -> { is with is_impl = Lib.discharge_con is.is_impl }) insts
  in
  let classes = Gmap.map subst_class cl in
  let instances = Gmap.map subst_inst inst in
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
  instances := gmapl_add i.is_class.cl_name i !instances;
  update ()

open Libnames
      
let id_of_reference r = 
  let (_, id) = repr_qualid (snd (qualid_of_reference r)) in id

let instances r = 
  let id = id_of_reference r in
    try let cl = class_info id in instances_of cl
    with Not_found -> unbound_class (Global.env()) (loc_of_reference r, id)

let solve_instanciation_problem = ref (fun _ _ _ _ -> assert false)

let resolve_typeclass env ev evi (evd, defined as acc) =
  if evi.evar_body = Evar_empty then
    try
      !solve_instanciation_problem env evd ev evi
    with Exit -> acc
  else acc

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

let method_typeclass ref = 
  match ref with 
    | ConstRef c -> 
	let (_, _, l) = Names.repr_con c in
	  class_info (Gmap.find (Names.id_of_label l) !methods)
    | _ -> raise Not_found
      
let is_class ind = 
  Gmap.fold (fun k v acc -> acc || v.cl_impl = ind) !classes false
  
let resolve_typeclasses env sigma evd =
  let evm = Evd.evars_of evd in
  let tc_evars = 
    let f ev evi acc =
      let (l, k) = Evd.evar_source ev evd in
	match k with
	    ImplicitArg (ref, (n, id)) ->
	      (try 
		  (* 		  let cl = method_typeclass ref in 
				  if destInd ki = cl.cl_impl then*)
		  match kind_of_term evi.evar_concl with
		    | App(ki, args) -> 
			if is_class (destInd ki) then Evd.add acc ev evi
			else acc
		    | _ -> acc
		with _ -> acc)
	  | _ -> acc
    in Evd.fold f evm Evd.empty
  in
  let rec sat evars =
    let (evars', progress) = 
      Evd.fold 
	(fun ev evi acc -> 
	  if Evd.mem tc_evars ev then resolve_typeclass env ev evi acc else acc) 
	(Evd.evars_of evars) (evars, false) 
    in
      if not progress then evars'
      else
	sat (Evarutil.nf_evar_defs evars')
  in sat evd
