(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Pp
open Names
open Term
open Context
open Environ
open Locus
open Univ

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
  let subst = make_universe_subst inst ctx in
  let constraints = instantiate_univ_context subst ctx in
    (inst, subst), constraints

let fresh_instance ctx =
  let s = ref LSet.empty in
  let inst = 
    Instance.subst_fn (fun _ -> 
      let u = new_univ_level (Global.current_dirpath ()) in 
	s := LSet.add u !s; u) 
      (UContext.instance ctx)
  in !s, inst

let fresh_instance_from ctx =
  let ctx', inst = fresh_instance ctx in
  let subst = make_universe_subst inst ctx in
  let constraints = instantiate_univ_context subst ctx in
    (inst, subst), (ctx', constraints)

(** Fresh universe polymorphic construction *)

let fresh_constant_instance env c =
  let cb = lookup_constant c env in
    if cb.Declarations.const_polymorphic then
      let (inst,_), ctx = fresh_instance_from (Future.force cb.Declarations.const_universes) in
	((c, inst), ctx)
    else ((c,Instance.empty), ContextSet.empty)

let fresh_inductive_instance env ind = 
  let mib, mip = Inductive.lookup_mind_specif env ind in
    if mib.Declarations.mind_polymorphic then
      let (inst,_), ctx = fresh_instance_from mib.Declarations.mind_universes in
	((ind,inst), ctx)
    else ((ind,Instance.empty), ContextSet.empty)

let fresh_constructor_instance env (ind,i) = 
  let mib, mip = Inductive.lookup_mind_specif env ind in
    if mib.Declarations.mind_polymorphic then
      let (inst,_), ctx = fresh_instance_from mib.Declarations.mind_universes in
	(((ind,i),inst), ctx)
    else (((ind,i),Instance.empty), ContextSet.empty)

open Globnames
let fresh_global_instance env gr =
  match gr with
  | VarRef id -> mkVar id, ContextSet.empty
  | ConstRef sp -> 
     let c, ctx = fresh_constant_instance env sp in
       mkConstU c, ctx
  | ConstructRef sp ->
     let c, ctx = fresh_constructor_instance env sp in
       mkConstructU c, ctx
  | IndRef sp -> 
     let c, ctx = fresh_inductive_instance env sp in
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

let unsafe_constr_of_global gr =
  let c, ctx = fresh_global_instance (Global.env ()) gr in
    c

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
  | Proj (p, c) -> (ConstRef p, Instance.empty), Some c
  | _ -> raise Not_found

open Declarations

let type_of_reference env r =
  match r with
  | VarRef id -> Environ.named_type id env, ContextSet.empty
  | ConstRef c ->
     let cb = Environ.lookup_constant c env in
     let ty = Typeops.type_of_constant_type env cb.const_type in
       if cb.const_polymorphic then
	 let (inst, subst), ctx = fresh_instance_from (Future.force cb.const_universes) in
	   Vars.subst_univs_constr subst ty, ctx
       else ty, ContextSet.empty

  | IndRef ind ->
     let (mib, oib as specif) = Inductive.lookup_mind_specif env ind in
       if mib.mind_polymorphic then
	 let (inst, subst), ctx = fresh_instance_from mib.mind_universes in
	 let ty = Inductive.type_of_inductive env (specif, inst) in
	   ty, ctx
       else
	 let ty = Inductive.type_of_inductive env (specif, Univ.Instance.empty) in
	   ty, ContextSet.empty
  | ConstructRef cstr ->
     let (mib,oib as specif) = Inductive.lookup_mind_specif env (inductive_of_constructor cstr) in
       if mib.mind_polymorphic then
	 let (inst, subst), ctx = fresh_instance_from mib.mind_universes in
	   Inductive.type_of_constructor (cstr,inst) specif, ctx
       else Inductive.type_of_constructor (cstr,Instance.empty) specif, ContextSet.empty

let type_of_global t = type_of_reference (Global.env ()) t

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

let remove_trivial_constraints cst =
  Constraint.fold (fun (l,d,r as cstr) nontriv ->
    if d != Lt && Univ.Level.equal l r then nontriv
    else if d == Le && is_type0m_univ (Univ.Universe.make l) then nontriv
    else Constraint.add cstr nontriv)
    cst Constraint.empty

let add_list_map u t map = 
  let l, d, r = LMap.split u map in
  let d' = match d with None -> [t] | Some l -> t :: l in
  let lr = 
    LMap.merge (fun k lm rm -> 
      match lm with Some t -> lm | None ->
      match rm with Some t -> rm | None -> None) l r
  in LMap.add u d' lr

let find_list_map u map =
  try LMap.find u map with Not_found -> []

module UF = LevelUnionFind
type universe_full_subst = (universe_level * universe) list
  
(** Precondition: flexible <= ctx *)
let choose_canonical ctx flexible algs s =
  let global = LSet.diff s ctx in
  let flexible, rigid = LSet.partition (fun x -> LMap.mem x flexible) (LSet.inter s ctx) in
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

open Universe

let subst_puniverses subst (c, u as cu) =
  let u' = Instance.subst subst u in
    if u' == u then cu else (c, u')

let nf_evars_and_universes_local f subst =
  let rec aux c =
    match kind_of_term c with
    | Evar (evdk, _ as ev) ->
      (match f ev with
      | None -> c
      | Some c -> aux c)
    | Const pu -> 
      let pu' = subst_puniverses subst pu in
	if pu' == pu then c else mkConstU pu'
    | Ind pu ->
      let pu' = subst_puniverses subst pu in
	if pu' == pu then c else mkIndU pu'
    | Construct pu ->
      let pu' = subst_puniverses subst pu in
	if pu' == pu then c else mkConstructU pu'
    | Sort (Type u) ->
      let u' = Univ.subst_univs_level_universe subst u in
	if u' == u then c else mkSort (sort_of_univ u')
    | _ -> map_constr aux c
  in aux

let subst_univs_fn_puniverses lsubst (c, u as cu) =
  let u' = Instance.subst_fn lsubst u in
    if u' == u then cu else (c, u')

let subst_univs_puniverses subst cu =
  subst_univs_fn_puniverses (Univ.level_subst_of (Univ.make_subst subst)) cu

let nf_evars_and_universes_gen f subst =
  let lsubst = Univ.level_subst_of subst in
  let rec aux c =
    match kind_of_term c with
    | Evar (evdk, _ as ev) ->
      (match try f ev with Not_found -> None with
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

let nf_evars_and_universes_subst f subst =
  nf_evars_and_universes_gen f (Univ.make_subst subst)

let nf_evars_and_universes_opt_subst f subst =
  let subst = fun l -> match LMap.find l subst with None -> raise Not_found | Some l' -> l' in
    nf_evars_and_universes_gen f subst

let subst_univs_full_constr subst c = 
  nf_evars_and_universes_subst (fun _ -> None) subst c

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
  in fun b -> try aux b with Not_found -> Universe.make b

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
  let ectx = ref ctx in
  let normalize = normalize_univ_variable_opt_subst ectx in
  let _ = Univ.LMap.iter (fun u _ -> ignore(normalize u)) ctx in
  let undef, def, subst = 
    Univ.LMap.fold (fun u v (undef, def, subst) -> 
      match v with
      | None -> (Univ.LSet.add u undef, def, subst)
      | Some b -> (undef, Univ.LSet.add u def, Univ.LMap.add u b subst))
    !ectx (Univ.LSet.empty, Univ.LSet.empty, Univ.LMap.empty)
  in !ectx, undef, def, subst

let pr_universe_body = function
  | None -> mt ()
  | Some v -> str" := " ++ Univ.Universe.pr v

let pr_universe_opt_subst = Univ.LMap.pr pr_universe_body

let is_defined_var u l = 
  try
    match LMap.find u l with
    | Some _ -> true
    | None -> false
  with Not_found -> false

let subst_univs_subst u l s = 
  LMap.add u l s
    
exception Found of Level.t
let find_inst insts v =
  try LMap.iter (fun k (enf,alg,v') ->
    if not alg && enf && Universe.equal v' v then raise (Found k))
	insts; raise Not_found
  with Found l -> l

let add_inst u (enf,b,lbound) insts =
  match lbound with
  | Some v -> LMap.add u (enf,b,v) insts
  | None -> insts

exception Stays

let compute_lbound left =
 (** The universe variable was not fixed yet.
     Compute its level using its lower bound. *)
  if CList.is_empty left then None
  else
    let lbound = List.fold_left (fun lbound (d, l) -> 
      if d == Le (* l <= ?u *) then (Universe.sup l lbound)
      else (* l < ?u *) 
	(assert (d == Lt); 
	 (Universe.sup (Universe.super l) lbound)))	    
      Universe.type0m left
    in 
      Some lbound
  
let maybe_enforce_leq lbound u cstrs = 
  match lbound with
  | Some lbound -> enforce_leq lbound (Universe.make u) cstrs
  | None -> cstrs

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
      Univ.constraints_of_universes (Univ.normalize_universes g)
  in
  let noneqs =
    Constraint.fold (fun (l,d,r) noneqs ->
      if d == Eq then (UF.union l r uf; noneqs) 
      else Constraint.add (l,d,r) noneqs)
    csts Constraint.empty
  in
  let partition = UF.partition uf in
  let subst, eqs = List.fold_left (fun (subst, cstrs) s -> 
    let canon, (global, rigid, flexible) = choose_canonical ctx us algs s in
    (* Add equalities for globals which can't be merged anymore. *)
    let cstrs = LSet.fold (fun g cst -> 
      Constraint.add (canon, Univ.Eq, g) cst) global cstrs 
    in
    (** Should this really happen? *)
    let subst' = LSet.fold (fun f -> LMap.add f canon)
      (LSet.union rigid flexible) LMap.empty
    in 
    let subst = LMap.union subst' subst in
      (subst, cstrs))
    (LMap.empty, Constraint.empty) partition
  in
  (* Noneqs is now in canonical form w.r.t. equality constraints, 
     and contains only inequality constraints. *)
  let noneqs = subst_univs_level_constraints subst noneqs in
  let us = 
    LMap.subst_union (LMap.map (fun v -> Some (Universe.make v)) subst) us
  in
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
  (* Now we construct the instanciation of each variable. *)
  let ctx', us, algs, inst, noneqs = 
    minimize_univ_variables ctx us algs ucstrsr ucstrsl noneqs
  in
  let us = ref us in
  let norm = normalize_univ_variable_opt_subst us in
  let _normalize_subst = LMap.iter (fun u v -> ignore(norm u)) !us in
    (!us, algs), (ctx', Constraint.union noneqs eqs)

(* let normalize_conkey = Profile.declare_profile "normalize_context_set" *)
(* let normalize_context_set a b c = Profile.profile3 normalize_conkey normalize_context_set a b c *)

let universes_of_constr c =
  let rec aux s c = 
    match kind_of_term c with
    | Const (_, u) | Ind (_, u) | Construct (_, u) ->
      LSet.union (Instance.levels u) s
    | Sort u -> 
      let u = univ_of_sort u in
	LSet.union (Universe.levels u) s
    | _ -> fold_constr aux s c
  in aux LSet.empty c

let shrink_universe_context (univs,csts) s =
  let univs' = LSet.inter univs s in
    Constraint.fold (fun (l,d,r as c) (univs',csts) ->
      if LSet.mem l univs' then
	let univs' = if LSet.mem r univs then LSet.add r univs' else univs' in
	  (univs', Constraint.add c csts)
      else if LSet.mem r univs' then
	let univs' = if LSet.mem l univs then LSet.add l univs' else univs' in
	  (univs', Constraint.add c csts)
      else (univs', csts))
      csts (univs',Constraint.empty)

let restrict_universe_context (univs,csts) s =
  let univs' = LSet.inter univs s in
  (* Universes that are not necessary to typecheck the term.
     E.g. univs introduced by tactics and not used in the proof term. *)
  let diff = LSet.diff univs s in
  let csts' = 
    Constraint.fold (fun (l,d,r as c) csts ->
      if LSet.mem l diff || LSet.mem r diff then csts
      else Constraint.add c csts)
      csts Constraint.empty
  in (univs', csts')

let is_small_leq (l,d,r) =
  Level.is_small l && d == Univ.Le

let is_prop_leq (l,d,r) =
  Level.equal Level.prop l && d == Univ.Le

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

let remove_trivial_constraints (ctx, cstrs) =
  let cstrs' = 
    Univ.Constraint.fold (fun c acc ->
      if is_prop_leq c then Univ.Constraint.remove c acc
      else acc) cstrs cstrs
  in (ctx, cstrs')
