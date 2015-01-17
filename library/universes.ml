(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Pp
open Names
open Term
open Environ
open Univ

type universe_names = 
    Univ.universe_level Idmap.t * Id.t Univ.LMap.t

let global_universes = Summary.ref ~name:"Global universe names" 
  ((Idmap.empty, Univ.LMap.empty) : universe_names)

let global_universe_names () = !global_universes
let set_global_universe_names s = global_universes := s

let pr_with_global_universes l = 
  try Nameops.pr_id (LMap.find l (snd !global_universes))
  with Not_found -> Level.pr l

type universe_constraint_type = ULe | UEq | ULub

type universe_constraint = universe * universe_constraint_type * universe

module Constraints = struct
  module S = Set.Make(
  struct 
    type t = universe_constraint

    let compare_type c c' =
      match c, c' with
      | ULe, ULe -> 0
      | ULe, _ -> -1
      | _, ULe -> 1
      | UEq, UEq -> 0
      | UEq, _ -> -1
      | ULub, ULub -> 0
      | ULub, _ -> 1
      
    let compare (u,c,v) (u',c',v') =
      let i = compare_type c c' in
	if Int.equal i 0 then
	  let i' = Universe.compare u u' in
	    if Int.equal i' 0 then Universe.compare v v'
	    else 
	      if c != ULe && Universe.compare u v' = 0 && Universe.compare v u' = 0 then 0
	      else i'
	else i
  end)
  
  include S
  
  let add (l,d,r as cst) s = 
    if Universe.equal l r then s
    else add cst s

  let tr_dir = function
    | ULe -> Le
    | UEq -> Eq
    | ULub -> Eq

  let op_str = function ULe -> " <= " | UEq -> " = " | ULub -> " /\\ "

  let pr c =
    fold (fun (u1,op,u2) pp_std ->
	pp_std ++ Universe.pr u1 ++ str (op_str op) ++
	Universe.pr u2 ++ fnl ()) c (str "")

  let equal x y = 
    x == y || equal x y

end

type universe_constraints = Constraints.t
type 'a universe_constrained = 'a * universe_constraints

type 'a universe_constraint_function = 'a -> 'a -> universe_constraints -> universe_constraints

let enforce_eq_instances_univs strict x y c = 
  let d = if strict then ULub else UEq in
  let ax = Instance.to_array x and ay = Instance.to_array y in
    if Array.length ax != Array.length ay then
      Errors.anomaly (Pp.str "Invalid argument: enforce_eq_instances_univs called with" ++
	       Pp.str " instances of different lengths");
    CArray.fold_right2
      (fun x y -> Constraints.add (Universe.make x, d, Universe.make y))
      ax ay c

let subst_univs_universe_constraint fn (u,d,v) =
  let u' = subst_univs_universe fn u and v' = subst_univs_universe fn v in
    if Universe.equal u' v' then None
    else Some (u',d,v')

let subst_univs_universe_constraints subst csts =
  Constraints.fold 
    (fun c -> Option.fold_right Constraints.add (subst_univs_universe_constraint subst c))
    csts Constraints.empty 


let to_constraints g s = 
  let tr (x,d,y) acc =
    let add l d l' acc = Constraint.add (l,Constraints.tr_dir d,l') acc in
      match Universe.level x, d, Universe.level y with
      | Some l, (ULe | UEq | ULub), Some l' -> add l d l' acc
      | _, ULe, Some l' -> enforce_leq x y acc
      | _, ULub, _ -> acc
      | _, d, _ -> 
	let f = if d == ULe then check_leq else check_eq in
	  if f g x y then acc else 
	    raise (Invalid_argument 
		   "to_constraints: non-trivial algebraic constraint between universes")
  in Constraints.fold tr s Constraint.empty

let eq_constr_univs_infer univs m n =
  if m == n then true, Constraints.empty
  else 
    let cstrs = ref Constraints.empty in
    let eq_universes strict = Univ.Instance.check_eq univs in
    let eq_sorts s1 s2 = 
      if Sorts.equal s1 s2 then true
      else
	let u1 = Sorts.univ_of_sort s1 and u2 = Sorts.univ_of_sort s2 in
	  if Univ.check_eq univs u1 u2 then true
	  else
	    (cstrs := Constraints.add (u1, UEq, u2) !cstrs;
	     true)
    in
    let rec eq_constr' m n = 
      m == n ||	Constr.compare_head_gen eq_universes eq_sorts eq_constr' m n
    in
    let res = Constr.compare_head_gen eq_universes eq_sorts eq_constr' m n in
      res, !cstrs

let leq_constr_univs_infer univs m n =
  if m == n then true, Constraints.empty
  else 
    let cstrs = ref Constraints.empty in
    let eq_universes strict l l' = Univ.Instance.check_eq univs l l' in
    let eq_sorts s1 s2 = 
      if Sorts.equal s1 s2 then true
      else
	let u1 = Sorts.univ_of_sort s1 and u2 = Sorts.univ_of_sort s2 in
	  if Univ.check_eq univs u1 u2 then true
	  else (cstrs := Constraints.add (u1, UEq, u2) !cstrs;
		true)
    in
    let leq_sorts s1 s2 = 
      if Sorts.equal s1 s2 then true
      else 
	let u1 = Sorts.univ_of_sort s1 and u2 = Sorts.univ_of_sort s2 in
	  if Univ.check_leq univs u1 u2 then true
	  else
	    (cstrs := Constraints.add (u1, ULe, u2) !cstrs; 
	     true)
    in
    let rec eq_constr' m n = 
      m == n ||	Constr.compare_head_gen eq_universes eq_sorts eq_constr' m n
    in
    let rec compare_leq m n =
      Constr.compare_head_gen_leq eq_universes eq_sorts leq_sorts 
	eq_constr' leq_constr' m n
    and leq_constr' m n = m == n || compare_leq m n in
    let res = compare_leq m n in
      res, !cstrs

let eq_constr_universes m n =
  if m == n then true, Constraints.empty
  else 
    let cstrs = ref Constraints.empty in
    let eq_universes strict l l' = 
      cstrs := enforce_eq_instances_univs strict l l' !cstrs; true in
    let eq_sorts s1 s2 = 
      if Sorts.equal s1 s2 then true
      else
	(cstrs := Constraints.add 
	   (Sorts.univ_of_sort s1, UEq, Sorts.univ_of_sort s2) !cstrs;
	 true)
    in
    let rec eq_constr' m n = 
      m == n ||	Constr.compare_head_gen eq_universes eq_sorts eq_constr' m n
    in
    let res = Constr.compare_head_gen eq_universes eq_sorts eq_constr' m n in
      res, !cstrs

let leq_constr_universes m n =
  if m == n then true, Constraints.empty
  else 
    let cstrs = ref Constraints.empty in
    let eq_universes strict l l' = 
      cstrs := enforce_eq_instances_univs strict l l' !cstrs; true in
    let eq_sorts s1 s2 = 
      if Sorts.equal s1 s2 then true
      else (cstrs := Constraints.add 
	      (Sorts.univ_of_sort s1,UEq,Sorts.univ_of_sort s2) !cstrs; 
	    true)
    in
    let leq_sorts s1 s2 = 
      if Sorts.equal s1 s2 then true
      else 
	(cstrs := Constraints.add 
	   (Sorts.univ_of_sort s1,ULe,Sorts.univ_of_sort s2) !cstrs; 
	 true)
    in
    let rec eq_constr' m n = 
      m == n ||	Constr.compare_head_gen eq_universes eq_sorts eq_constr' m n
    in
    let rec compare_leq m n =
      Constr.compare_head_gen_leq eq_universes eq_sorts leq_sorts eq_constr' leq_constr' m n
    and leq_constr' m n = m == n || compare_leq m n in
    let res = compare_leq m n in
      res, !cstrs

let compare_head_gen_proj env equ eqs eqc' m n =
  match kind_of_term m, kind_of_term n with
  | Proj (p, c), App (f, args)
  | App (f, args), Proj (p, c) -> 
    (match kind_of_term f with
    | Const (p', u) when eq_constant (Projection.constant p) p' -> 
      let pb = Environ.lookup_projection p env in
      let npars = pb.Declarations.proj_npars in
	if Array.length args == npars + 1 then
	  eqc' c args.(npars)
	else false
    | _ -> false)
  | _ -> Constr.compare_head_gen equ eqs eqc' m n
    
let eq_constr_universes_proj env m n =
  if m == n then true, Constraints.empty
  else 
    let cstrs = ref Constraints.empty in
    let eq_universes strict l l' = 
      cstrs := enforce_eq_instances_univs strict l l' !cstrs; true in
    let eq_sorts s1 s2 = 
      if Sorts.equal s1 s2 then true
      else
	(cstrs := Constraints.add 
	   (Sorts.univ_of_sort s1, UEq, Sorts.univ_of_sort s2) !cstrs;
	 true)
    in
    let rec eq_constr' m n = 
      m == n ||	compare_head_gen_proj env eq_universes eq_sorts eq_constr' m n
    in
    let res = eq_constr' m n in
      res, !cstrs

(* Generator of levels *)
let new_univ_level, set_remote_new_univ_level =
  RemoteCounter.new_counter ~name:"Universes" 0 ~incr:((+) 1)
    ~build:(fun n -> Univ.Level.make (Global.current_dirpath ()) n)

let new_univ_level _ = new_univ_level ()
  (* Univ.Level.make db (new_univ_level ()) *)

let fresh_level () = new_univ_level (Global.current_dirpath ())

(* TODO: remove *)
let new_univ dp = Univ.Universe.make (new_univ_level dp)
let new_Type dp = mkType (new_univ dp)
let new_Type_sort dp = Type (new_univ dp)

let fresh_universe_instance ctx =
  Instance.subst_fn (fun _ -> new_univ_level (Global.current_dirpath ())) 
    (UContext.instance ctx)

let fresh_instance_from_context ctx =
  let inst = fresh_universe_instance ctx in
  let constraints = instantiate_univ_constraints inst ctx in
    inst, constraints

let fresh_instance ctx =
  let ctx' = ref LSet.empty in
  let inst = 
    Instance.subst_fn (fun v -> 
      let u = new_univ_level (Global.current_dirpath ()) in
	ctx' := LSet.add u !ctx'; u) 
      (UContext.instance ctx)
  in !ctx', inst

let existing_instance ctx inst = 
  let () = 
    let a1 = Instance.to_array inst 
    and a2 = Instance.to_array (UContext.instance ctx) in
    let len1 = Array.length a1 and len2 = Array.length a2 in 
      if not (len1 == len2) then
	Errors.errorlabstrm "Universes"
	  (str "Polymorphic constant expected " ++ int len2 ++ 
	     str" levels but was given " ++ int len1)
      else ()
  in LSet.empty, inst

let fresh_instance_from ctx inst =
  let ctx', inst = 
    match inst with 
    | Some inst -> existing_instance ctx inst
    | None -> fresh_instance ctx 
  in
  let constraints = instantiate_univ_constraints inst ctx in
    inst, (ctx', constraints)

let unsafe_instance_from ctx =
  (Univ.UContext.instance ctx, ctx)
    
(** Fresh universe polymorphic construction *)

let fresh_constant_instance env c inst =
  let cb = lookup_constant c env in
    if cb.Declarations.const_polymorphic then
      let inst, ctx =
        fresh_instance_from
          (Declareops.universes_of_constant (Environ.opaque_tables env) cb) inst
      in
	((c, inst), ctx)
    else ((c,Instance.empty), ContextSet.empty)

let fresh_inductive_instance env ind inst = 
  let mib, mip = Inductive.lookup_mind_specif env ind in
    if mib.Declarations.mind_polymorphic then
      let inst, ctx = fresh_instance_from mib.Declarations.mind_universes inst in
	((ind,inst), ctx)
    else ((ind,Instance.empty), ContextSet.empty)

let fresh_constructor_instance env (ind,i) inst = 
  let mib, mip = Inductive.lookup_mind_specif env ind in
    if mib.Declarations.mind_polymorphic then
      let inst, ctx = fresh_instance_from mib.Declarations.mind_universes inst in
	(((ind,i),inst), ctx)
    else (((ind,i),Instance.empty), ContextSet.empty)

let unsafe_constant_instance env c =
  let cb = lookup_constant c env in
    if cb.Declarations.const_polymorphic then
      let inst, ctx = unsafe_instance_from
        (Declareops.universes_of_constant (Environ.opaque_tables env) cb) in
	((c, inst), ctx)
    else ((c,Instance.empty), UContext.empty)

let unsafe_inductive_instance env ind = 
  let mib, mip = Inductive.lookup_mind_specif env ind in
    if mib.Declarations.mind_polymorphic then
      let inst, ctx = unsafe_instance_from mib.Declarations.mind_universes in
	((ind,inst), ctx)
    else ((ind,Instance.empty), UContext.empty)

let unsafe_constructor_instance env (ind,i) = 
  let mib, mip = Inductive.lookup_mind_specif env ind in
    if mib.Declarations.mind_polymorphic then
      let inst, ctx = unsafe_instance_from mib.Declarations.mind_universes in
	(((ind,i),inst), ctx)
    else (((ind,i),Instance.empty), UContext.empty)

open Globnames

let fresh_global_instance ?names env gr =
  match gr with
  | VarRef id -> mkVar id, ContextSet.empty
  | ConstRef sp -> 
     let c, ctx = fresh_constant_instance env sp names in
       mkConstU c, ctx
  | ConstructRef sp ->
     let c, ctx = fresh_constructor_instance env sp names in
       mkConstructU c, ctx
  | IndRef sp -> 
     let c, ctx = fresh_inductive_instance env sp names in
       mkIndU c, ctx

let fresh_constant_instance env sp = 
  fresh_constant_instance env sp None

let fresh_inductive_instance env sp = 
  fresh_inductive_instance env sp None

let fresh_constructor_instance env sp = 
  fresh_constructor_instance env sp None

let unsafe_global_instance env gr =
  match gr with
  | VarRef id -> mkVar id, UContext.empty
  | ConstRef sp -> 
     let c, ctx = unsafe_constant_instance env sp in
       mkConstU c, ctx
  | ConstructRef sp ->
     let c, ctx = unsafe_constructor_instance env sp in
       mkConstructU c, ctx
  | IndRef sp -> 
     let c, ctx = unsafe_inductive_instance env sp in
       mkIndU c, ctx

let constr_of_global gr =
  let c, ctx = fresh_global_instance (Global.env ()) gr in
    if not (Univ.ContextSet.is_empty ctx) then
      if Univ.LSet.is_empty (Univ.ContextSet.levels ctx) then 
	(* Should be an error as we might forget constraints, allow for now
	   to make firstorder work with "using" clauses *)
	c
      else raise (Invalid_argument 
		    ("constr_of_global: globalization of polymorphic reference " ^ 
			Pp.string_of_ppcmds (Nametab.pr_global_env Id.Set.empty gr) ^
			" would forget universes."))
    else c

let constr_of_reference = constr_of_global

let unsafe_constr_of_global gr =
  unsafe_global_instance (Global.env ()) gr

let constr_of_global_univ (gr,u) =
  match gr with
  | VarRef id -> mkVar id
  | ConstRef sp -> mkConstU (sp,u)
  | ConstructRef sp -> mkConstructU (sp,u)
  | IndRef sp -> mkIndU (sp,u)

let fresh_global_or_constr_instance env = function
  | IsConstr c -> c, ContextSet.empty
  | IsGlobal gr -> fresh_global_instance env gr

let global_of_constr c =
  match kind_of_term c with
  | Const (c, u) -> ConstRef c, u
  | Ind (i, u) -> IndRef i, u
  | Construct (c, u) -> ConstructRef c, u
  | Var id -> VarRef id, Instance.empty
  | _ -> raise Not_found

let global_app_of_constr c =
  match kind_of_term c with
  | Const (c, u) -> (ConstRef c, u), None
  | Ind (i, u) -> (IndRef i, u), None
  | Construct (c, u) -> (ConstructRef c, u), None
  | Var id -> (VarRef id, Instance.empty), None
  | Proj (p, c) -> (ConstRef (Projection.constant p), Instance.empty), Some c
  | _ -> raise Not_found

open Declarations

let type_of_reference env r =
  match r with
  | VarRef id -> Environ.named_type id env, ContextSet.empty
  | ConstRef c ->
     let cb = Environ.lookup_constant c env in
     let ty = Typeops.type_of_constant_type env cb.const_type in
       if cb.const_polymorphic then
	 let inst, ctx = fresh_instance_from (Declareops.universes_of_constant (Environ.opaque_tables env) cb) None in
	   Vars.subst_instance_constr inst ty, ctx
       else ty, ContextSet.empty

  | IndRef ind ->
     let (mib, oib as specif) = Inductive.lookup_mind_specif env ind in
       if mib.mind_polymorphic then
	 let inst, ctx = fresh_instance_from mib.mind_universes None in
	 let ty = Inductive.type_of_inductive env (specif, inst) in
	   ty, ctx
       else
	 let ty = Inductive.type_of_inductive env (specif, Univ.Instance.empty) in
	   ty, ContextSet.empty
  | ConstructRef cstr ->
     let (mib,oib as specif) = Inductive.lookup_mind_specif env (inductive_of_constructor cstr) in
       if mib.mind_polymorphic then
	 let inst, ctx = fresh_instance_from mib.mind_universes None in
	   Inductive.type_of_constructor (cstr,inst) specif, ctx
       else Inductive.type_of_constructor (cstr,Instance.empty) specif, ContextSet.empty

let type_of_global t = type_of_reference (Global.env ()) t

let unsafe_type_of_reference env r =
  match r with
  | VarRef id -> Environ.named_type id env
  | ConstRef c ->
     let cb = Environ.lookup_constant c env in
       Typeops.type_of_constant_type env cb.const_type

  | IndRef ind ->
     let (mib, oib as specif) = Inductive.lookup_mind_specif env ind in
     let (_, inst), _ = unsafe_inductive_instance env ind in
       Inductive.type_of_inductive env (specif, inst)

  | ConstructRef (ind, _ as cstr) ->
     let (mib,oib as specif) = Inductive.lookup_mind_specif env (inductive_of_constructor cstr) in
     let (_, inst), _ = unsafe_inductive_instance env ind in
       Inductive.type_of_constructor (cstr,inst) specif

let unsafe_type_of_global t = unsafe_type_of_reference (Global.env ()) t

let fresh_sort_in_family env = function
  | InProp -> prop_sort, ContextSet.empty
  | InSet -> set_sort, ContextSet.empty
  | InType -> 
    let u = fresh_level () in
      Type (Univ.Universe.make u), ContextSet.singleton u

let new_sort_in_family sf =
  fst (fresh_sort_in_family (Global.env ()) sf)

let extend_context (a, ctx) (ctx') =
  (a, ContextSet.union ctx ctx')

let new_global_univ () =
  let u = fresh_level () in
    (Univ.Universe.make u, ContextSet.singleton u)

(** Simplification *)

module LevelUnionFind = Unionfind.Make (Univ.LSet) (Univ.LMap)

let add_list_map u t map =
  try
    let l = LMap.find u map in
    LMap.update u (t :: l) map
  with Not_found ->
    LMap.add u [t] map

module UF = LevelUnionFind

(** Precondition: flexible <= ctx *)
let choose_canonical ctx flexible algs s =
  let global = LSet.diff s ctx in
  let flexible, rigid = LSet.partition flexible (LSet.inter s ctx) in
    (** If there is a global universe in the set, choose it *)
    if not (LSet.is_empty global) then
      let canon = LSet.choose global in
	canon, (LSet.remove canon global, rigid, flexible)
    else (** No global in the equivalence class, choose a rigid one *)
	if not (LSet.is_empty rigid) then
	  let canon = LSet.choose rigid in
	    canon, (global, LSet.remove canon rigid, flexible)
	else (** There are only flexible universes in the equivalence
		 class, choose a non-algebraic. *)
	  let algs, nonalgs = LSet.partition (fun x -> LSet.mem x algs) flexible in
	    if not (LSet.is_empty nonalgs) then
	      let canon = LSet.choose nonalgs in
		canon, (global, rigid, LSet.remove canon flexible)
	    else
	      let canon = LSet.choose algs in
		canon, (global, rigid, LSet.remove canon flexible)

let subst_univs_fn_puniverses lsubst (c, u as cu) =
  let u' = Instance.subst_fn lsubst u in
    if u' == u then cu else (c, u')

let nf_evars_and_universes_opt_subst f subst =
  let subst = fun l -> match LMap.find l subst with None -> raise Not_found | Some l' -> l' in
  let lsubst = Univ.level_subst_of subst in
  let rec aux c =
    match kind_of_term c with
    | Evar (evk, args) ->
      let args = Array.map aux args in
      (match try f (evk, args) with Not_found -> None with
      | None -> c
      | Some c -> aux c)
    | Const pu -> 
      let pu' = subst_univs_fn_puniverses lsubst pu in
	if pu' == pu then c else mkConstU pu'
    | Ind pu ->
      let pu' = subst_univs_fn_puniverses lsubst pu in
	if pu' == pu then c else mkIndU pu'
    | Construct pu ->
      let pu' = subst_univs_fn_puniverses lsubst pu in
	if pu' == pu then c else mkConstructU pu'
    | Sort (Type u) ->
      let u' = Univ.subst_univs_universe subst u in
	if u' == u then c else mkSort (sort_of_univ u')
    | _ -> map_constr aux c
  in aux

let fresh_universe_context_set_instance ctx =
  if ContextSet.is_empty ctx then LMap.empty, ctx
  else
    let (univs, cst) = ContextSet.levels ctx, ContextSet.constraints ctx in
    let univs',subst = LSet.fold
      (fun u (univs',subst) ->
	let u' = fresh_level () in
	  (LSet.add u' univs', LMap.add u u' subst))
      univs (LSet.empty, LMap.empty)
    in
    let cst' = subst_univs_level_constraints subst cst in
      subst, (univs', cst')

let normalize_univ_variable ~find ~update =
  let rec aux cur =
    let b = find cur in
    let b' = subst_univs_universe aux b in
      if Universe.equal b' b then b
      else update cur b'
  in aux

let normalize_univ_variable_opt_subst ectx =
  let find l = 
    match Univ.LMap.find l !ectx with
    | Some b -> b
    | None -> raise Not_found
  in
  let update l b =
    assert (match Universe.level b with Some l' -> not (Level.equal l l') | None -> true);
    ectx := Univ.LMap.add l (Some b) !ectx; b
  in normalize_univ_variable ~find ~update

let normalize_univ_variable_subst subst =
  let find l = Univ.LMap.find l !subst in
  let update l b =
    assert (match Universe.level b with Some l' -> not (Level.equal l l') | None -> true);
    subst := Univ.LMap.add l b !subst; b in
    normalize_univ_variable ~find ~update

let normalize_universe_opt_subst subst =
  let normlevel = normalize_univ_variable_opt_subst subst in
    subst_univs_universe normlevel

let normalize_universe_subst subst =
  let normlevel = normalize_univ_variable_subst subst in
    subst_univs_universe normlevel

let normalize_opt_subst ctx = 
  let ectx = ref ctx in
  let normalize = normalize_univ_variable_opt_subst ectx in
  let () =
    Univ.LMap.iter (fun u v ->
      if Option.is_empty v then ()
      else try ignore(normalize u) with Not_found -> assert(false)) ctx 
  in !ectx

type universe_opt_subst = universe option universe_map
	  
let make_opt_subst s = 
  fun x -> 
    (match Univ.LMap.find x s with
    | Some u -> u
    | None -> raise Not_found)

let subst_opt_univs_constr s = 
  let f = make_opt_subst s in
    Vars.subst_univs_fn_constr f


let normalize_univ_variables ctx = 
  let ctx = normalize_opt_subst ctx in
  let undef, def, subst =
    Univ.LMap.fold (fun u v (undef, def, subst) -> 
      match v with
      | None -> (Univ.LSet.add u undef, def, subst)
      | Some b -> (undef, Univ.LSet.add u def, Univ.LMap.add u b subst))
    ctx (Univ.LSet.empty, Univ.LSet.empty, Univ.LMap.empty)
  in ctx, undef, def, subst

let pr_universe_body = function
  | None -> mt ()
  | Some v -> str" := " ++ Univ.Universe.pr v

let pr_universe_opt_subst = Univ.LMap.pr pr_universe_body

exception Found of Level.t
let find_inst insts v =
  try LMap.iter (fun k (enf,alg,v') ->
    if not alg && enf && Universe.equal v' v then raise (Found k))
	insts; raise Not_found
  with Found l -> l

let compute_lbound left =
 (** The universe variable was not fixed yet.
     Compute its level using its lower bound. *)
  let sup l lbound = 
    match lbound with
    | None -> Some l
    | Some l' -> Some (Universe.sup l l')
  in
    List.fold_left (fun lbound (d, l) -> 
      if d == Le (* l <= ?u *) then sup l lbound
      else (* l < ?u *) 
	(assert (d == Lt); 
	 if not (Universe.level l == None) then
	   sup (Universe.super l) lbound
	 else None))
      None left
  
let instantiate_with_lbound u lbound alg enforce (ctx, us, algs, insts, cstrs) =
  if enforce then
    let inst = Universe.make u in
    let cstrs' = enforce_leq lbound inst cstrs in
      (ctx, us, LSet.remove u algs, 
       LMap.add u (enforce,alg,lbound) insts, cstrs'), (enforce, alg, inst)
  else (* Actually instantiate *)
    (Univ.LSet.remove u ctx, Univ.LMap.add u (Some lbound) us, algs,
     LMap.add u (enforce,alg,lbound) insts, cstrs), (enforce, alg, lbound)

type constraints_map = (Univ.constraint_type * Univ.LMap.key) list Univ.LMap.t

let pr_constraints_map cmap =
  LMap.fold (fun l cstrs acc -> 
    Level.pr l ++ str " => " ++ 
      prlist_with_sep spc (fun (d,r) -> pr_constraint_type d ++ Level.pr r) cstrs ++ fnl ()
    ++ acc)
    cmap (mt ())
	
let minimize_univ_variables ctx us algs left right cstrs =
  let left, lbounds = 
    Univ.LMap.fold (fun r lower (left, lbounds as acc)  ->
      if Univ.LMap.mem r us || not (Univ.LSet.mem r ctx) then acc
      else (* Fixed universe, just compute its glb for sharing *)
	let lbounds' = 
	  match compute_lbound (List.map (fun (d,l) -> d, Universe.make l) lower) with
	  | None -> lbounds
	  | Some lbound -> LMap.add r (true, false, lbound) lbounds
	in (Univ.LMap.remove r left, lbounds'))
      left (left, Univ.LMap.empty)
  in
  let rec instance (ctx', us, algs, insts, cstrs as acc) u =
    let acc, left = 
      try let l = LMap.find u left in
	    List.fold_left (fun (acc, left') (d, l) -> 
	      let acc', (enf,alg,l') = aux acc l in
		(* if alg then assert(not alg); *)
		let l' = 
		  if enf then Universe.make l 
		  else l' 
		(* match Universe.level l' with Some _ -> l' | None -> Universe.make l  *)
		in
		  acc', (d, l') :: left') (acc, []) l
      with Not_found -> acc, []
    and right =
      try Some (LMap.find u right)
      with Not_found -> None
    in
    let instantiate_lbound lbound =
      let alg = LSet.mem u algs in
      if alg then
	 (* u is algebraic and has no upper bound constraints: we
	    instantiate it with it's lower bound, if any *)
	 instantiate_with_lbound u lbound true false acc
      else (* u is non algebraic *)
	match Universe.level lbound with
	| Some l -> (* The lowerbound is directly a level *) 
	  (* u is not algebraic but has no upper bounds,
	     we instantiate it with its lower bound if it is a 
	     different level, otherwise we keep it. *)
	  if not (Level.equal l u) && not (LSet.mem l algs) then
	    (* if right = None then. Should check that u does not 
	       have upper constraints that are not already in right *)
	      instantiate_with_lbound u lbound false false acc
	    (* else instantiate_with_lbound u lbound false true acc *)
	  else
	    (* assert false: l can't be alg *)
	    acc, (true, false, lbound)
	| None -> 
	  try 
	    (* if right <> None then raise Not_found; *)
	    (* Another universe represents the same lower bound, 
	       we can share them with no harm. *)
	    let can = find_inst insts lbound in
	      instantiate_with_lbound u (Universe.make can) false false acc
	  with Not_found -> 
	    (* We set u as the canonical universe representing lbound *)
	    instantiate_with_lbound u lbound false true acc
    in
    let acc' acc = 
      match right with
      | None -> acc
      | Some cstrs -> 
	let dangling = List.filter (fun (d, r) -> not (LMap.mem r us)) cstrs in
	  if List.is_empty dangling then acc
	  else
	    let ((ctx', us, algs, insts, cstrs), (enf,_,inst as b)) = acc in
	    let cstrs' = List.fold_left (fun cstrs (d, r) -> 
	      if d == Univ.Le then
		enforce_leq inst (Universe.make r) cstrs
	      else 
		try let lev = Option.get (Universe.level inst) in
		      Constraint.add (lev, d, r) cstrs
		with Option.IsNone -> assert false)
	      cstrs dangling
	    in
	      (ctx', us, algs, insts, cstrs'), b
    in
      if not (LSet.mem u ctx) then acc' (acc, (true, false, Universe.make u))
      else
	let lbound = compute_lbound left in
	  match lbound with
	  | None -> (* Nothing to do *)
	    acc' (acc, (true, false, Universe.make u))
	  | Some lbound ->
	    acc' (instantiate_lbound lbound)
  and aux (ctx', us, algs, seen, cstrs as acc) u =
    try acc, LMap.find u seen 
    with Not_found -> instance acc u
  in
    LMap.fold (fun u v (ctx', us, algs, seen, cstrs as acc) -> 
      if v == None then fst (aux acc u)
      else LSet.remove u ctx', us, LSet.remove u algs, seen, cstrs)
      us (ctx, us, algs, lbounds, cstrs)
      
let normalize_context_set ctx us algs = 
  let (ctx, csts) = ContextSet.levels ctx, ContextSet.constraints ctx in
  let uf = UF.create () in
  let csts = 
    (* We first put constraints in a normal-form: all self-loops are collapsed
       to equalities. *)
    let g = Univ.merge_constraints csts Univ.empty_universes in
      Univ.constraints_of_universes g
  in
  let noneqs =
    Constraint.fold (fun (l,d,r) noneqs ->
      if d == Eq then (UF.union l r uf; noneqs) 
      else Constraint.add (l,d,r) noneqs)
    csts Constraint.empty
  in
  let partition = UF.partition uf in
  let flex x = LMap.mem x us in
  let ctx, subst, eqs = List.fold_left (fun (ctx, subst, cstrs) s -> 
    let canon, (global, rigid, flexible) = choose_canonical ctx flex algs s in
    (* Add equalities for globals which can't be merged anymore. *)
    let cstrs = LSet.fold (fun g cst -> 
      Constraint.add (canon, Univ.Eq, g) cst) global
      cstrs 
    in
    let subst = LSet.fold (fun f -> LMap.add f canon) rigid subst in 
    let subst = LSet.fold (fun f -> LMap.add f canon) flexible subst in 
      (LSet.diff (LSet.diff ctx rigid) flexible, subst, cstrs))
    (ctx, LMap.empty, Constraint.empty) partition
  in
  (* Noneqs is now in canonical form w.r.t. equality constraints, 
     and contains only inequality constraints. *)
  let noneqs = subst_univs_level_constraints subst noneqs in
  let us = LMap.fold (fun u v acc -> LMap.add u (Some (Universe.make v)) acc) subst us in
  (* Compute the left and right set of flexible variables, constraints
     mentionning other variables remain in noneqs. *)
  let noneqs, ucstrsl, ucstrsr = 
    Constraint.fold (fun (l,d,r as cstr) (noneq, ucstrsl, ucstrsr) -> 
      let lus = LMap.mem l us 
      and rus = LMap.mem r us
      in
      let ucstrsl' = 
	if lus then add_list_map l (d, r) ucstrsl
	else ucstrsl
      and ucstrsr' = 
	add_list_map r (d, l) ucstrsr
      in 
      let noneqs = 
	if lus || rus then noneq 
	else Constraint.add cstr noneq
      in (noneqs, ucstrsl', ucstrsr'))
    noneqs (Constraint.empty, LMap.empty, LMap.empty)
  in
  (* Now we construct the instantiation of each variable. *)
  let ctx', us, algs, inst, noneqs = 
    minimize_univ_variables ctx us algs ucstrsr ucstrsl noneqs
  in
  let us = normalize_opt_subst us in
    (us, algs), (ctx', Constraint.union noneqs eqs)

(* let normalize_conkey = Profile.declare_profile "normalize_context_set" *)
(* let normalize_context_set a b c = Profile.profile3 normalize_conkey normalize_context_set a b c *)

let universes_of_constr c =
  let rec aux s c = 
    match kind_of_term c with
    | Const (_, u) | Ind (_, u) | Construct (_, u) ->
      LSet.union (Instance.levels u) s
    | Sort u when not (Sorts.is_small u) -> 
      let u = univ_of_sort u in
	LSet.union (Universe.levels u) s
    | _ -> fold_constr aux s c
  in aux LSet.empty c

let restrict_universe_context (univs,csts) s =
  (* Universes that are not necessary to typecheck the term.
     E.g. univs introduced by tactics and not used in the proof term. *)
  let diff = LSet.diff univs s in
  let rec aux diff candid univs ness = 
    let (diff', candid', univs', ness') = 
      Constraint.fold
	(fun (l, d, r as c) (diff, candid, univs, csts) ->
	  if not (LSet.mem l diff) then
	    (LSet.remove r diff, candid, univs, Constraint.add c csts)
	  else if not (LSet.mem r diff) then
	    (LSet.remove l diff, candid, univs, Constraint.add c csts)
	  else (diff, Constraint.add c candid, univs, csts))
	candid (diff, Constraint.empty, univs, ness)
    in
      if ness' == ness then (LSet.diff univs diff', ness)
      else aux diff' candid' univs' ness'
  in aux diff csts univs Constraint.empty

let simplify_universe_context (univs,csts) =
  let uf = UF.create () in
  let noneqs =
    Constraint.fold (fun (l,d,r) noneqs ->
      if d == Eq && (LSet.mem l univs || LSet.mem r univs) then 
	(UF.union l r uf; noneqs)
      else Constraint.add (l,d,r) noneqs)
      csts Constraint.empty
  in
  let partition = UF.partition uf in
  let flex x = LSet.mem x univs in
  let subst, univs', csts' = List.fold_left (fun (subst, univs, cstrs) s -> 
    let canon, (global, rigid, flexible) = choose_canonical univs flex LSet.empty s in
    (* Add equalities for globals which can't be merged anymore. *)
    let cstrs = LSet.fold (fun g cst -> 
      Constraint.add (canon, Univ.Eq, g) cst) (LSet.union global rigid)
      cstrs 
    in
    let subst = LSet.fold (fun f -> LMap.add f canon)
      flexible subst
    in (subst, LSet.diff univs flexible, cstrs))
    (LMap.empty, univs, noneqs) partition
  in
  (* Noneqs is now in canonical form w.r.t. equality constraints, 
     and contains only inequality constraints. *)
  let csts' = subst_univs_level_constraints subst csts' in
    (univs', csts'), subst

let is_small_leq (l,d,r) =
  Level.is_small l && d == Univ.Le

(* Prop < i <-> Set+1 <= i <-> Set < i *)
let translate_cstr (l,d,r as cstr) =
  if Level.equal Level.prop l && d == Univ.Lt then
    (Level.set, d, r)
  else cstr

let refresh_constraints univs (ctx, cstrs) =
  let cstrs', univs' = 
    Univ.Constraint.fold (fun c (cstrs', univs as acc) -> 
      let c = translate_cstr c in
      if Univ.check_constraint univs c && not (is_small_leq c) then acc
      else (Univ.Constraint.add c cstrs', Univ.enforce_constraint c univs))
      cstrs (Univ.Constraint.empty, univs)
  in ((ctx, cstrs'), univs')


(**********************************************************************)
(* Tools for sort-polymorphic inductive types                         *)

(* Miscellaneous functions to remove or test local univ assumed to
   occur only in the le constraints *)

(*
   Solve a system of universe constraint of the form

   u_s11, ..., u_s1p1, w1 <= u1
   ...
   u_sn1, ..., u_snpn, wn <= un

where

  - the ui (1 <= i <= n) are universe variables,
  - the sjk select subsets of the ui for each equations,
  - the wi are arbitrary complex universes that do not mention the ui.
*)

let is_direct_sort_constraint s v = match s with
  | Some u -> univ_level_mem u v
  | None -> false

let solve_constraints_system levels level_bounds level_min =
  let open Univ in
  let levels =
    Array.mapi (fun i o ->
      match o with
      | Some u ->
	(match Universe.level u with 
	| Some u -> Some u 
	| _ -> level_bounds.(i) <- Universe.sup level_bounds.(i) u; None)
      | None -> None)
      levels in
  let v = Array.copy level_bounds in
  let nind = Array.length v in
  let clos = Array.map (fun _ -> Int.Set.empty) levels in
  (* First compute the transitive closure of the levels dependencies *)
  for i=0 to nind-1 do
    for j=0 to nind-1 do
      if not (Int.equal i j) && is_direct_sort_constraint levels.(j) v.(i) then
	clos.(i) <- Int.Set.add j clos.(i);
    done;
  done;
  let rec closure () = 
    let continue = ref false in
      Array.iteri (fun i deps -> 
	let deps' = 
	  Int.Set.fold (fun j acc -> Int.Set.union acc clos.(j)) deps deps
	in 
	  if Int.Set.equal deps deps' then ()
	  else (clos.(i) <- deps'; continue := true))
	clos;
      if !continue then closure ()
      else ()
  in 
  closure ();
  for i=0 to nind-1 do
    for j=0 to nind-1 do
      if not (Int.equal i j) && Int.Set.mem j clos.(i) then
	(v.(i) <- Universe.sup v.(i) level_bounds.(j);
	 level_min.(i) <- Universe.sup level_min.(i) level_min.(j))
    done;
    for j=0 to nind-1 do
      match levels.(j) with
      | Some u -> v.(i) <- univ_level_rem u v.(i) level_min.(i)
      | None -> ()
    done
  done;
  v
