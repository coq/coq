(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Names
open Globnames
open Decl_kinds
open Term
open Vars
open Context
open Evd
open Environ
open Util
open Typeclasses_errors
open Libobject
(*i*)

let typeclasses_unique_solutions = ref false
let set_typeclasses_unique_solutions d = (:=) typeclasses_unique_solutions d
let get_typeclasses_unique_solutions () = !typeclasses_unique_solutions

open Goptions

let set_typeclasses_unique_solutions =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
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

let solve_instantiation_problem = ref (fun _ _ _ _ -> assert false)

let resolve_one_typeclass ?(unique=get_typeclasses_unique_solutions ()) env evm t =
  !solve_instantiation_problem env evm t unique

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
  cl_projs : (Name.t * (direction * int option) option * constant option) list;
  
  cl_strict : bool;

  cl_unique : bool;
}

type typeclasses = typeclass Refmap.t

type instance = {
  is_class: global_reference;
  is_pri: int option;
  (* Sections where the instance should be redeclared,
     -1 for discard, 0 for none, mutable to avoid redeclarations
     when multiple rebuild_object happen. *)
  is_global: int;
  is_poly: bool;
  is_impl: global_reference;
}

type instances = (instance Refmap.t) Refmap.t

let instance_impl is = is.is_impl

let instance_priority is = is.is_pri

let new_instance cl pri glob poly impl =
  let global =
    if glob then Lib.sections_depth ()
    else -1
  in
    { is_class = cl.cl_impl;
      is_pri = pri ;
      is_global = global ;
      is_poly = poly;
      is_impl = impl }

(*
 * states management
 *)

let classes : typeclasses ref = Summary.ref Refmap.empty ~name:"classes"
let instances : instances ref = Summary.ref Refmap.empty ~name:"instances"

open Declarations

let typeclass_univ_instance (cl,u') =
  let subst = 
    let u = 
      match cl.cl_impl with
      | ConstRef c -> 
        let cb = Global.lookup_constant c in
	  if cb.const_polymorphic then Univ.UContext.instance cb.const_universes
	  else Univ.Instance.empty
      | IndRef c ->
         let mib,oib = Global.lookup_inductive c in
	  if mib.mind_polymorphic then Univ.UContext.instance mib.mind_universes
	  else Univ.Instance.empty
      | _ -> Univ.Instance.empty
    in Array.fold_left2 (fun subst u u' -> Univ.LMap.add u u' subst) 
      Univ.LMap.empty (Univ.Instance.to_array u) (Univ.Instance.to_array u')
  in
  let subst_ctx = Context.map_rel_context (subst_univs_level_constr subst) in
    { cl with cl_context = fst cl.cl_context, subst_ctx (snd cl.cl_context);
      cl_props = subst_ctx cl.cl_props}, u'

let class_info c =
  try Refmap.find c !classes
  with Not_found -> not_a_class (Global.env()) (printable_constr_of_global c)

let global_class_of_constr env c =
  try let gr, u = Universes.global_of_constr c in
	class_info gr, u
  with Not_found -> not_a_class env c

let dest_class_app env c =
  let cl, args = decompose_app c in
    global_class_of_constr env cl, args

let dest_class_arity env c =
  let rels, c = decompose_prod_assum c in
    rels, dest_class_app env c

let class_of_constr c =
  try Some (dest_class_arity (Global.env ()) c)
  with e when Errors.noncritical e -> None

let is_class_constr c = 
  try let gr, u = Universes.global_of_constr c in
	Refmap.mem gr !classes
  with Not_found -> false

let rec is_class_type evd c =
  let c, args = decompose_app c in
    match kind_of_term c with
    | Prod (_, _, t) -> is_class_type evd t
    | Evar (e, _) when Evd.is_defined evd e ->
      is_class_type evd (Evarutil.whd_head_evar evd c)
    | _ -> is_class_constr c
      
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
  let do_subst_ctx ctx = List.smartmap
    (fun (na, b, t) -> (na, Option.smartmap do_subst b, do_subst t))
    ctx in
  let do_subst_context (grs,ctx) =
    List.smartmap (Option.smartmap (fun (gr,b) -> do_subst_gr gr, b)) grs,
    do_subst_ctx ctx in
  let do_subst_projs projs = List.smartmap (fun (x, y, z) -> 
    (x, y, Option.smartmap do_subst_con z)) projs in
  { cl_impl = do_subst_gr cl.cl_impl;
    cl_context = do_subst_context cl.cl_context;
    cl_props = do_subst_ctx cl.cl_props;
    cl_projs = do_subst_projs cl.cl_projs;
    cl_strict = cl.cl_strict;
    cl_unique = cl.cl_unique }

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
	| Some (_, ((tc,_), _)) -> Some (tc.cl_impl, true))
	ctx' 
      in
	List.smartmap (Option.smartmap (fun (gr, b) -> Lib.discharge_global gr, b)) grs
	  @ newgrs
    in grs', discharge_rel_context subst 1 ctx @ ctx' in
  let cl_impl' = Lib.discharge_global cl.cl_impl in
  if cl_impl' == cl.cl_impl then cl else
    let ctx, usubst, uctx = abs_context cl in
    let ctx, subst = rel_of_variable_context ctx in
    let context = discharge_context ctx subst cl.cl_context in
    let props = discharge_rel_context subst (succ (List.length (fst cl.cl_context))) cl.cl_props in
    let discharge_proj (x, y, z) = x, y, Option.smartmap Lib.discharge_con z in
      { cl_impl = cl_impl';
	cl_context = context;
	cl_props = props;
	cl_projs = List.smartmap discharge_proj cl.cl_projs;
	cl_strict = cl.cl_strict;
	cl_unique = cl.cl_unique
      }

let rebuild_class cl = 
  try 
    let cst = Tacred.evaluable_of_global_reference (Global.env ()) cl.cl_impl in
      set_typeclass_transparency cst false false; cl
  with e when Errors.noncritical e -> cl

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
  with e when Errors.noncritical e -> false

let build_subclasses ~check env sigma glob pri =
  let _id = Nametab.basename_of_global glob in
  let _next_id = 
    let i = ref (-1) in 
      (fun () -> incr i;
        Nameops.add_suffix _id ("_subinstance_" ^ string_of_int !i))
  in
  let ty, ctx = Global.type_of_global_in_context env glob in
  let sigma = Evd.merge_context_set Evd.univ_rigid sigma (Univ.ContextSet.of_context ctx) in
  let rec aux pri c ty path =
    let ty = Evarutil.nf_evar sigma ty in
      match class_of_constr ty with
      | None -> []
      | Some (rels, ((tc,u), args)) ->
	let instapp = 
	  Reductionops.whd_beta sigma (appvectc c (Termops.extended_rel_vect 0 rels)) 
	in
	let projargs = Array.of_list (args @ [instapp]) in
	let projs = List.map_filter 
	  (fun (n, b, proj) ->
	   match b with 
	   | None -> None
	   | Some (Backward, _) -> None
	   | Some (Forward, pri') ->
	     let proj = Option.get proj in
	     let body = it_mkLambda_or_LetIn (mkApp (mkConstU (proj,u), projargs)) rels in
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
	  let path' = cref :: path in
	  let ty = Retyping.get_type_of env sigma body in
	  let rest = aux pri body ty path' in
	    hints @ (path', pri, body) :: rest
	in List.fold_left declare_proj [] projs 
  in
  let term = Universes.constr_of_global_univ (glob,Univ.UContext.instance ctx) in
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
  if inst.is_global <= 0 then None
  else Some (action,
    { inst with 
      is_global = pred inst.is_global;
      is_class = Lib.discharge_global inst.is_class;
      is_impl = Lib.discharge_global inst.is_impl })
    

let is_local i = Int.equal i.is_global (-1)

let add_instance check inst =
  let poly = Global.is_polymorphic inst.is_impl in
  add_instance_hint (IsGlobal inst.is_impl) [inst.is_impl] (is_local inst) 
    inst.is_pri poly;
  List.iter (fun (path, pri, c) -> add_instance_hint (IsConstr c) path
    (is_local inst) pri poly)
    (build_subclasses ~check:(check && not (isVarRef inst.is_impl))
       (Global.env ()) Evd.empty inst.is_impl inst.is_pri)

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

let declare_instance pri local glob =
  let ty = Global.type_of_global_unsafe glob in
    match class_of_constr ty with
    | Some (rels, ((tc,_), args) as _cl) ->
      add_instance (new_instance tc pri (not local) (Flags.use_polymorphic_flag ()) glob)
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
	       (match body with
	       | None -> Errors.error "Non-definable projection can not be declared as a subinstance"
	       | Some b -> declare_instance pri false (ConstRef b))
	     | _ -> ())
  cl.cl_projs


open Declarations
      
(*
 * interface functions
 *)

let instance_constructor (cl,u) args =
  let filter (_, b, _) = match b with
  | None -> true
  | Some _ -> false
  in
  let lenpars = List.length (List.filter filter (snd cl.cl_context)) in
  let pars = fst (List.chop lenpars args) in
    match cl.cl_impl with
      | IndRef ind -> 
        let ind = ind, u in
          (Some (applistc (mkConstructUi (ind, 1)) args),
	   applistc (mkIndU ind) pars)
      | ConstRef cst -> 
        let cst = cst, u in
	let term = match args with
	  | [] -> None
	  | _ -> Some (List.last args)
	in
	  (term, applistc (mkConstU cst) pars)
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
  Refmap.exists (fun _ v -> eq_gr v.cl_impl gr) !classes

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

let is_implicit_arg = function
| Evar_kinds.GoalEvar -> false
| _ -> true
  (* match k with *)
  (*     ImplicitArg (ref, (n, id), b) -> true *)
  (*   | InternalHole -> true *)
  (*   | _ -> false *)


(* To embed a boolean for resolvability status.
   This is essentially a hack to mark which evars correspond to
   goals and do not need to be resolved when we have nested [resolve_all_evars]
   calls (e.g. when doing apply in an External hint in typeclass_instances).
   Would be solved by having real evars-as-goals.

   Nota: we will only check the resolvability status of undefined evars.
 *)

let resolvable = Store.field ()

let set_resolvable s b =
  Store.set s resolvable b

let is_resolvable evi =
  assert (match evi.evar_body with Evar_empty -> true | _ -> false);
  Option.default true (Store.get evi.evar_extra resolvable)

let mark_resolvability_undef b evi =
  let t = Store.set evi.evar_extra resolvable b in
  { evi with evar_extra = t }

let mark_resolvability b evi =
  assert (match evi.evar_body with Evar_empty -> true | _ -> false);
  mark_resolvability_undef b evi

let mark_unresolvable evi = mark_resolvability false evi
let mark_resolvable evi = mark_resolvability true evi

open Evar_kinds
type evar_filter = existential_key -> Evar_kinds.t -> bool

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

let solve_instantiations_problem = ref (fun _ _ _ _ _ _ -> assert false)

let solve_problem env evd filter unique split fail =
  !solve_instantiations_problem env evd filter unique split fail

(** Profiling resolution of typeclasses *)
(* let solve_classeskey = Profile.declare_profile "solve_typeclasses" *)
(* let solve_problem = Profile.profile5 solve_classeskey solve_problem *)

let resolve_typeclasses ?(filter=no_goals) ?(unique=get_typeclasses_unique_solutions ())
    ?(split=true) ?(fail=true) env evd =
  if not (has_typeclasses filter evd) then evd
  else solve_problem env evd filter unique split fail
