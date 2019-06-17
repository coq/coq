(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i*)
open Names
open Globnames
open Term
open Constr
open Vars
open Evd
open Util
open Typeclasses_errors
open Context.Rel.Declaration

(*i*)

(* Core typeclasses hints *)
type 'a hint_info_gen =
    { hint_priority : int option;
      hint_pattern : 'a option }

type hint_info = (Pattern.patvar list * Pattern.constr_pattern) hint_info_gen

let get_typeclasses_unique_solutions =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~name:"check that typeclasses proof search returns unique solutions"
    ~key:["Typeclasses";"Unique";"Solutions"]
    ~value:false

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

  (* The method implementations as projections. *)
  cl_projs : (Name.t * (direction * hint_info) option
	      * Constant.t option) list;
  
  cl_strict : bool;

  cl_unique : bool;
}

type typeclasses = typeclass GlobRef.Map.t

type instance = {
  is_class: GlobRef.t;
  is_info: hint_info;
  (* Sections where the instance should be redeclared,
     None for discard, Some 0 for none. *)
  is_global: int option;
  is_impl: GlobRef.t;
}

type instances = (instance GlobRef.Map.t) GlobRef.Map.t

let instance_impl is = is.is_impl

let hint_priority is = is.is_info.hint_priority

(*
 * states management
 *)

let classes : typeclasses ref = Summary.ref GlobRef.Map.empty ~name:"classes"
let instances : instances ref = Summary.ref GlobRef.Map.empty ~name:"instances"

let typeclass_univ_instance (cl, u) =
  assert (Univ.AUContext.size cl.cl_univs == Univ.Instance.length u);
  let subst_ctx c = Context.Rel.map (subst_instance_constr u) c in
    { cl with cl_context = on_snd subst_ctx cl.cl_context;
      cl_props = subst_ctx cl.cl_props}

let class_info env sigma c =
  try GlobRef.Map.find c !classes
  with Not_found ->
    not_a_class env sigma (EConstr.of_constr (printable_constr_of_global c))

let global_class_of_constr env sigma c =
  try let gr, u = Termops.global_of_constr sigma c in
    GlobRef.Map.find gr !classes, u
  with Not_found -> not_a_class env sigma c

let dest_class_app env sigma c =
  let cl, args = EConstr.decompose_app sigma c in
    global_class_of_constr env sigma cl, (List.map EConstr.Unsafe.to_constr args)

let dest_class_arity env sigma c =
  let open EConstr in
  let rels, c = decompose_prod_assum sigma c in
    rels, dest_class_app env sigma c

let class_of_constr env sigma c =
  try Some (dest_class_arity env sigma c)
  with e when CErrors.noncritical e -> None

let is_class_constr sigma c = 
  try let gr, u = Termops.global_of_constr sigma c in
    GlobRef.Map.mem gr !classes
  with Not_found -> false

let rec is_class_type evd c =
  let c, _ = Termops.decompose_app_vect evd c in
    match EConstr.kind evd c with
    | Prod (_, _, t) -> is_class_type evd t
    | Cast (t, _, _) -> is_class_type evd t
    | _ -> is_class_constr evd c
      
let is_class_evar evd evi =
  is_class_type evd evi.Evd.evar_concl

let is_class_constr sigma c =
  try let gr, u = Termops.global_of_constr sigma c in
    GlobRef.Map.mem gr !classes
  with Not_found -> false

let rec is_maybe_class_type evd c =
  let c, _ = Termops.decompose_app_vect evd c in
    match EConstr.kind evd c with
    | Prod (_, _, t) -> is_maybe_class_type evd t
    | Cast (t, _, _) -> is_maybe_class_type evd t
    | Evar _ -> true
    | _ -> is_class_constr evd c

let () = Hook.set Evd.is_maybe_typeclass_hook (fun evd c -> is_maybe_class_type evd (EConstr.of_constr c))

let load_class cl =
  classes := GlobRef.Map.add cl.cl_impl cl !classes

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
  let ty, ctx = Typeops.type_of_global_in_context env glob in
  let inst, ctx = UnivGen.fresh_instance_from ctx None in
  let ty = Vars.subst_instance_constr inst ty in
  let ty = EConstr.of_constr ty in
  let sigma = Evd.merge_context_set Evd.univ_rigid sigma ctx in
  let rec aux pri c ty path =
      match class_of_constr env sigma ty with
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
  let term = Constr.mkRef (glob, inst) in
    (*FIXME subclasses should now get substituted for each particular instance of
      the polymorphic superclass *)
    aux pri term ty [glob]

(*
 * interface functions
 *)

let load_instance inst =
  let insts =
    try GlobRef.Map.find inst.is_class !instances
    with Not_found -> GlobRef.Map.empty in
  let insts = GlobRef.Map.add inst.is_impl inst insts in
  instances := GlobRef.Map.add inst.is_class insts !instances

let remove_instance inst =
  let insts =
    try GlobRef.Map.find inst.is_class !instances
    with Not_found -> assert false in
  let insts = GlobRef.Map.remove inst.is_impl insts in
  instances := GlobRef.Map.add inst.is_class insts !instances


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

let typeclasses () = GlobRef.Map.fold (fun _ l c -> l :: c) !classes []

let cmap_elements c = GlobRef.Map.fold (fun k v acc -> v :: acc) c []

let instances_of c =
  try cmap_elements (GlobRef.Map.find c.cl_impl !instances) with Not_found -> []

let all_instances () = 
  GlobRef.Map.fold (fun k v acc ->
    GlobRef.Map.fold (fun k v acc -> v :: acc) v acc)
    !instances []

let instances env sigma r =
  let cl = class_info env sigma r in instances_of cl

let is_class gr = 
  GlobRef.Map.exists (fun _ v -> GlobRef.equal v.cl_impl gr) !classes

open Evar_kinds
type evar_filter = Evar.t -> Evar_kinds.t Lazy.t -> bool

let make_unresolvables filter evd =
  let tcs = Evd.get_typeclass_evars evd in
  Evd.set_typeclass_evars evd (Evar.Set.filter (fun x -> not (filter x)) tcs)

let all_evars _ _ = true
let all_goals _ source =
  match Lazy.force source with
  | VarInstance _ | GoalEvar -> true
  | _ -> false

let no_goals ev evi = not (all_goals ev evi)
let no_goals_or_obligations _ source =
  match Lazy.force source with
  | VarInstance _ | GoalEvar | QuestionMark _ -> false
  | _ -> true

let has_typeclasses filter evd =
  let tcs = get_typeclass_evars evd in
  let check ev = filter ev (lazy (snd (Evd.find evd ev).evar_source)) in
  Evar.Set.exists check tcs

let get_solve_all_instances, solve_all_instances_hook = Hook.make ()

let solve_all_instances env evd filter unique split fail =
  Hook.get get_solve_all_instances env evd filter unique split fail

(** Profiling resolution of typeclasses *)
(* let solve_classeskey = CProfile.declare_profile "solve_typeclasses" *)
(* let solve_problem = CProfile.profile5 solve_classeskey solve_problem *)

let resolve_typeclasses ?(filter=no_goals) ?(unique=get_typeclasses_unique_solutions ())
    ?(split=true) ?(fail=true) env evd =
  if not (has_typeclasses filter evd) then evd
  else solve_all_instances env evd filter unique split fail
