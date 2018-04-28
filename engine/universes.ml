(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Sorts
open Util
open Pp
open Constr
open Univ

(* To disallow minimization to Set *)

let set_minimization = ref true
let is_set_minimization () = !set_minimization

let _ =
  Goptions.(declare_bool_option
          { optdepr  = false;
            optname  = "minimization to Set";
            optkey   = ["Universe";"Minimization";"ToSet"];
            optread  = is_set_minimization;
            optwrite = (:=) set_minimization })

type universe_constraint =
  | ULe of Universe.t * Universe.t
  | UEq of Universe.t * Universe.t
  | ULub of Level.t * Level.t
  | UWeak of Level.t * Level.t

module Constraints = struct
  module S = Set.Make(
  struct 
    type t = universe_constraint

    let compare x y =
      match x, y with
      | ULe (u, v), ULe (u', v') ->
        let i = Universe.compare u u' in
        if Int.equal i 0 then Universe.compare v v'
        else i
      | UEq (u, v), UEq (u', v') ->
        let i = Universe.compare u u' in
        if Int.equal i 0 then Universe.compare v v'
        else if Universe.equal u v' && Universe.equal v u' then 0
        else i
      | ULub (u, v), ULub (u', v') | UWeak (u, v), UWeak (u', v') ->
        let i = Level.compare u u' in
        if Int.equal i 0 then Level.compare v v'
        else if Level.equal u v' && Level.equal v u' then 0
        else i
      | ULe _, _ -> -1
      | _, ULe _ -> 1
      | UEq _, _ -> -1
      | _, UEq _ -> 1
      | ULub _, _ -> -1
      | _, ULub _ -> 1
  end)
  
  include S

  let is_trivial = function
    | ULe (u, v) | UEq (u, v) -> Universe.equal u v
    | ULub (u, v) | UWeak (u, v) -> Level.equal u v

  let add cst s =
    if is_trivial cst then s
    else add cst s

  let pr_one = function
    | ULe (u, v) -> Universe.pr u ++ str " <= " ++ Universe.pr v
    | UEq (u, v) -> Universe.pr u ++ str " = " ++ Universe.pr v
    | ULub (u, v) -> Level.pr u ++ str " /\\ " ++ Level.pr v
    | UWeak (u, v) -> Level.pr u ++ str " ~ " ++ Level.pr v

  let pr c =
    fold (fun cst pp_std ->
        pp_std ++ pr_one cst ++ fnl ()) c (str "")

  let equal x y = 
    x == y || equal x y

end

type universe_constraints = Constraints.t
type 'a constraint_accumulator = universe_constraints -> 'a -> 'a option
type 'a universe_constrained = 'a * universe_constraints

type 'a universe_constraint_function = 'a -> 'a -> universe_constraints -> universe_constraints

let enforce_eq_instances_univs strict x y c = 
  let mk u v = if strict then ULub (u, v) else UEq (Universe.make u, Universe.make v) in
  let ax = Instance.to_array x and ay = Instance.to_array y in
    if Array.length ax != Array.length ay then
      CErrors.anomaly (Pp.str "Invalid argument: enforce_eq_instances_univs called with" ++
	       Pp.str " instances of different lengths.");
    CArray.fold_right2
      (fun x y -> Constraints.add (mk x y))
      ax ay c

let enforce_univ_constraint (u,d,v) =
  match d with
  | Eq -> enforce_eq u v
  | Le -> enforce_leq u v
  | Lt -> enforce_leq (super u) v

let subst_univs_level fn l =
  try Some (fn l)
  with Not_found -> None

let subst_univs_constraint fn (u,d,v as c) cstrs =
  let u' = subst_univs_level fn u in
  let v' = subst_univs_level fn v in
  match u', v' with
  | None, None -> Constraint.add c cstrs
  | Some u, None -> enforce_univ_constraint (u,d,Universe.make v) cstrs
  | None, Some v -> enforce_univ_constraint (Universe.make u,d,v) cstrs
  | Some u, Some v -> enforce_univ_constraint (u,d,v) cstrs

let subst_univs_constraints subst csts =
  Constraint.fold
    (fun c cstrs -> subst_univs_constraint subst c cstrs)
    csts Constraint.empty

let level_subst_of f =
  fun l ->
    try let u = f l in
          match Universe.level u with
          | None -> l
          | Some l -> l
    with Not_found -> l

let subst_univs_universe_constraint fn = function
  | ULe (u, v) ->
    let u' = subst_univs_universe fn u and v' = subst_univs_universe fn v in
    if Universe.equal u' v' then None
    else Some (ULe (u',v'))
  | UEq (u, v) ->
    let u' = subst_univs_universe fn u and v' = subst_univs_universe fn v in
    if Universe.equal u' v' then None
    else Some (ULe (u',v'))
  | ULub (u, v) ->
    let u' = level_subst_of fn u and v' = level_subst_of fn v in
    if Level.equal u' v' then None
    else Some (ULub (u',v'))
  | UWeak (u, v) ->
    let u' = level_subst_of fn u and v' = level_subst_of fn v in
    if Level.equal u' v' then None
    else Some (UWeak (u',v'))

let subst_univs_universe_constraints subst csts =
  Constraints.fold 
    (fun c -> Option.fold_right Constraints.add (subst_univs_universe_constraint subst c))
    csts Constraints.empty 

let to_constraints ~force_weak g s =
  let invalid () =
    raise (Invalid_argument "to_constraints: non-trivial algebraic constraint between universes")
  in
  let tr cst acc =
    match cst with
    | ULub (l, l') -> Constraint.add (l, Eq, l') acc
    | UWeak (l, l') when force_weak -> Constraint.add (l, Eq, l') acc
    | UWeak  _-> acc
    | ULe (l, l') ->
      begin match Universe.level l, Universe.level l' with
        | Some l, Some l' -> Constraint.add (l, Le, l') acc
        | None, Some _ -> enforce_leq l l' acc
        | _, None ->
          if UGraph.check_leq g l l'
          then acc
          else invalid ()
      end
    | UEq (l, l') ->
      begin match Universe.level l, Universe.level l' with
        | Some l, Some l' -> Constraint.add (l, Eq, l') acc
        | None, _ | _, None ->
          if UGraph.check_eq g l l'
          then acc
          else invalid ()
      end
  in
  Constraints.fold tr s Constraint.empty

(** Variant of [eq_constr_univs_infer] taking kind-of-term functions,
    to expose subterms of [m] and [n], arguments. *)
let eq_constr_univs_infer_with kind1 kind2 univs fold m n accu =
  (* spiwack: duplicates the code of [eq_constr_univs_infer] because I
     haven't find a way to factor the code without destroying
     pointer-equality optimisations in [eq_constr_univs_infer].
     Pointer equality is not sufficient to ensure equality up to
     [kind1,kind2], because [kind1] and [kind2] may be different,
     typically evaluating [m] and [n] in different evar maps. *)
  let cstrs = ref accu in
  let eq_universes _ _ = UGraph.check_eq_instances univs in
  let eq_sorts s1 s2 = 
    if Sorts.equal s1 s2 then true
    else
      let u1 = Sorts.univ_of_sort s1 and u2 = Sorts.univ_of_sort s2 in
      match fold (Constraints.singleton (UEq (u1, u2))) !cstrs with
      | None -> false
      | Some accu -> cstrs := accu; true
  in
  let rec eq_constr' nargs m n =
    Constr.compare_head_gen_with kind1 kind2 eq_universes eq_sorts eq_constr' nargs m n
  in
  let res = Constr.compare_head_gen_with kind1 kind2 eq_universes eq_sorts eq_constr' 0 m n in
  if res then Some !cstrs else None

(** Simplification *)

let add_list_map u t map =
  try
    let l = LMap.find u map in
    LMap.set u (t :: l) map
  with Not_found ->
    LMap.add u [t] map

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

let subst_univs_fn_constr f c =
  let changed = ref false in
  let fu = Univ.subst_univs_universe f in
  let fi = Univ.Instance.subst_fn (level_subst_of f) in
  let rec aux t =
    match kind t with
    | Sort (Sorts.Type u) ->
      let u' = fu u in
        if u' == u then t else
          (changed := true; mkSort (Sorts.sort_of_univ u'))
    | Const (c, u) ->
      let u' = fi u in
        if u' == u then t
        else (changed := true; mkConstU (c, u'))
    | Ind (i, u) ->
      let u' = fi u in
        if u' == u then t
        else (changed := true; mkIndU (i, u'))
    | Construct (c, u) ->
      let u' = fi u in
        if u' == u then t
        else (changed := true; mkConstructU (c, u'))
    | _ -> map aux t
  in
  let c' = aux c in
    if !changed then c' else c

let subst_univs_constr subst c =
  if Univ.is_empty_subst subst then c
  else
    let f = Univ.make_subst subst in
      subst_univs_fn_constr f c

let subst_univs_constr =
  if Flags.profile then
    let subst_univs_constr_key = CProfile.declare_profile "subst_univs_constr" in
      CProfile.profile2 subst_univs_constr_key subst_univs_constr
  else subst_univs_constr

let normalize_univ_variable ~find =
  let rec aux cur =
    let b = find cur in
    let b' = subst_univs_universe aux b in
      if Universe.equal b' b then b
      else b'
  in aux

let normalize_univ_variable_opt_subst ectx =
  let find l = 
    match Univ.LMap.find l ectx with
    | Some b -> b
    | None -> raise Not_found
  in
  normalize_univ_variable ~find

let normalize_univ_variable_subst subst =
  let find l = Univ.LMap.find l subst in
  normalize_univ_variable ~find

let normalize_universe_opt_subst subst =
  let normlevel = normalize_univ_variable_opt_subst subst in
    subst_univs_universe normlevel

let normalize_universe_subst subst =
  let normlevel = normalize_univ_variable_subst subst in
    subst_univs_universe normlevel

let normalize_opt_subst ctx = 
  let normalize = normalize_universe_opt_subst ctx in
  Univ.LMap.mapi (fun u -> function
      | None -> None
      | Some v -> Some (normalize v)) ctx

type universe_opt_subst = Universe.t option universe_map

let subst_univs_fn_puniverses f (c, u as cu) =
  let u' = Instance.subst_fn f u in
    if u' == u then cu else (c, u')

let nf_evars_and_universes_opt_subst f subst =
  let subst = normalize_univ_variable_opt_subst subst in
  let lsubst = level_subst_of subst in
  let rec aux c =
    match kind c with
    | Evar (evk, args) ->
      let args = Array.map aux args in
      (match try f (evk, args) with Not_found -> None with
      | None -> mkEvar (evk, args)
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
    | _ -> Constr.map aux c
  in aux

let make_opt_subst s = 
  fun x -> 
    (match Univ.LMap.find x s with
    | Some u -> u
    | None -> raise Not_found)

let subst_opt_univs_constr s = 
  let f = make_opt_subst s in
  subst_univs_fn_constr f

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

(* Eq < Le < Lt *)
let compare_constraint_type d d' =
  match d, d' with
  | Eq, Eq -> 0
  | Eq, _ -> -1
  | _, Eq -> 1
  | Le, Le -> 0
  | Le, _ -> -1
  | _, Le -> 1
  | Lt, Lt -> 0

type lowermap = constraint_type LMap.t

let lower_union =
  let merge k a b =
    match a, b with
    | Some _, None -> a
    | None, Some _ -> b
    | None, None -> None
    | Some l, Some r ->
       if compare_constraint_type l r >= 0 then a
       else b
  in LMap.merge merge

let lower_add l c m =
  try let c' = LMap.find l m in
      if compare_constraint_type c c' > 0 then
        LMap.add l c m
      else m
  with Not_found -> LMap.add l c m

let lower_of_list l =
  List.fold_left (fun acc (d,l) -> LMap.add l d acc) LMap.empty l

type lbound = { enforce : bool; alg : bool; lbound: Universe.t; lower : lowermap }

exception Found of Level.t * lowermap
let find_inst insts v =
  try LMap.iter (fun k {enforce;alg;lbound=v';lower} ->
    if not alg && enforce && Universe.equal v' v then raise (Found (k, lower)))
	insts; raise Not_found
  with Found (f,l) -> (f,l)

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

let instantiate_with_lbound u lbound lower ~alg ~enforce (ctx, us, algs, insts, cstrs) =
  if enforce then
    let inst = Universe.make u in
    let cstrs' = enforce_leq lbound inst cstrs in
      (ctx, us, LSet.remove u algs, 
       LMap.add u {enforce;alg;lbound;lower} insts, cstrs'),
      {enforce; alg; lbound=inst; lower}
  else (* Actually instantiate *)
    (Univ.LSet.remove u ctx, Univ.LMap.add u (Some lbound) us, algs,
     LMap.add u {enforce;alg;lbound;lower} insts, cstrs),
    {enforce; alg; lbound; lower}

type constraints_map = (Univ.constraint_type * Univ.LMap.key) list Univ.LMap.t

let _pr_constraints_map (cmap:constraints_map) =
  LMap.fold (fun l cstrs acc -> 
    Level.pr l ++ str " => " ++ 
      prlist_with_sep spc (fun (d,r) -> pr_constraint_type d ++ Level.pr r) cstrs ++
      fnl () ++ acc)
    cmap (mt ())

let remove_alg l (ctx, us, algs, insts, cstrs) =
  (ctx, us, LSet.remove l algs, insts, cstrs)

let not_lower lower (d,l) =
  (* We're checking if (d,l) is already implied by the lower
     constraints on some level u. If it represents l < u (d is Lt
     or d is Le and i > 0, the i < 0 case is impossible due to
     invariants of Univ), and the lower constraints only have l <=
     u then it is not implied. *)
  Univ.Universe.exists
    (fun (l,i) ->
       let d =
         if i == 0 then d
         else match d with
           | Le -> Lt
           | d -> d
       in
       try let d' = LMap.find l lower in
         (* If d is stronger than the already implied lower
          * constraints we must keep it. *)
         compare_constraint_type d d' > 0
       with Not_found ->
         (** No constraint existing on l *) true) l

exception UpperBoundedAlg
(** [enforce_uppers upper lbound cstrs] interprets [upper] as upper
   constraints to [lbound], adding them to [cstrs].

    @raise UpperBoundedAlg if any [upper] constraints are strict and
   [lbound] algebraic. *)
let enforce_uppers upper lbound cstrs =
  List.fold_left (fun cstrs (d, r) ->
      if d == Univ.Le then
        enforce_leq lbound (Universe.make r) cstrs
      else
        match Universe.level lbound with
        | Some lev -> Constraint.add (lev, d, r) cstrs
        | None -> raise UpperBoundedAlg)
    cstrs upper

let minimize_univ_variables ctx us algs left right cstrs =
  let left, lbounds = 
    Univ.LMap.fold (fun r lower (left, lbounds as acc)  ->
      if Univ.LMap.mem r us || not (Univ.LSet.mem r ctx) then acc
      else (* Fixed universe, just compute its glb for sharing *)
        let lbounds =
	  match compute_lbound (List.map (fun (d,l) -> d, Universe.make l) lower) with
	  | None -> lbounds
          | Some lbound -> LMap.add r {enforce=true; alg=false; lbound; lower=lower_of_list lower}
                                   lbounds
        in (Univ.LMap.remove r left, lbounds))
      left (left, Univ.LMap.empty)
  in
  let rec instance (ctx, us, algs, insts, cstrs as acc) u =
    let acc, left, lower =
      match LMap.find u left with
      | exception Not_found -> acc, [], LMap.empty
      | l ->
	let acc, left, newlow, lower =
          List.fold_left
          (fun (acc, left, newlow, lower') (d, l) ->
           let acc', {enforce=enf;alg;lbound=l';lower} = aux acc l in
	   let l' =
	     if enf then Universe.make l
	     else l'
           in acc', (d, l') :: left,
              lower_add l d newlow, lower_union lower lower')
	  (acc, [], LMap.empty, LMap.empty) l
        in
        let left = List.uniquize (List.filter (not_lower lower) left) in
        (acc, left, LMap.union newlow lower)
    in
    let instantiate_lbound lbound =
      let alg = LSet.mem u algs in
	if alg then
	  (* u is algebraic: we instantiate it with its lower bound, if any,
              or enforce the constraints if it is bounded from the top. *)
          let lower = LSet.fold LMap.remove (Universe.levels lbound) lower in
          instantiate_with_lbound u lbound lower ~alg:true ~enforce:false acc
	else (* u is non algebraic *)
	  match Universe.level lbound with
	  | Some l -> (* The lowerbound is directly a level *) 
	     (* u is not algebraic but has no upper bounds,
  	        we instantiate it with its lower bound if it is a 
	        different level, otherwise we keep it. *)
             let lower = LMap.remove l lower in
	     if not (Level.equal l u) then
	       (* Should check that u does not 
  	          have upper constraints that are not already in right *)
               let acc = remove_alg l acc in
                 instantiate_with_lbound u lbound lower ~alg:false ~enforce:false acc
             else acc, {enforce=true; alg=false; lbound; lower}
	  | None ->
            begin match find_inst insts lbound with
              | can, lower ->
                (* Another universe represents the same lower bound,
                   we can share them with no harm. *)
                let lower = LMap.remove can lower in
                instantiate_with_lbound u (Universe.make can) lower ~alg:false ~enforce:false acc
              | exception Not_found ->
                (* We set u as the canonical universe representing lbound *)
                instantiate_with_lbound u lbound lower ~alg:false ~enforce:true acc
            end
    in
    let enforce_uppers ((ctx,us,algs,insts,cstrs), b as acc) =
      match LMap.find u right with
      | exception Not_found -> acc
      | upper ->
        let upper = List.filter (fun (d, r) -> not (LMap.mem r us)) upper in
        let cstrs = enforce_uppers upper b.lbound cstrs in
        (ctx, us, algs, insts, cstrs), b
    in
    if not (LSet.mem u ctx)
    then enforce_uppers (acc, {enforce=true; alg=false; lbound=Universe.make u; lower})
    else
      let lbound = compute_lbound left in
      match lbound with
      | None -> (* Nothing to do *)
        enforce_uppers (acc, {enforce=true;alg=false;lbound=Universe.make u; lower})
      | Some lbound ->
        try enforce_uppers (instantiate_lbound lbound)
        with UpperBoundedAlg ->
          enforce_uppers (acc, {enforce=true; alg=false; lbound=Universe.make u; lower})
  and aux (ctx, us, algs, seen, cstrs as acc) u =
    try acc, LMap.find u seen 
    with Not_found -> instance acc u
  in
    LMap.fold (fun u v (ctx, us, algs, seen, cstrs as acc) ->
      if v == None then fst (aux acc u)
      else LSet.remove u ctx, us, LSet.remove u algs, seen, cstrs)
      us (ctx, us, algs, lbounds, cstrs)

module UPairs = OrderedType.UnorderedPair(Univ.Level)
module UPairSet = Set.Make (UPairs)

let normalize_context_set g ctx us algs weak =
  let (ctx, csts) = ContextSet.levels ctx, ContextSet.constraints ctx in
  (** Keep the Prop/Set <= i constraints separate for minimization *)
  let smallles, csts =
    Constraint.partition (fun (l,d,r) -> d == Le && Level.is_small l) csts
  in
  let smallles = if is_set_minimization ()
    then Constraint.filter (fun (l,d,r) -> LSet.mem r ctx) smallles
    else Constraint.empty
  in
  let csts, partition =
    (* We first put constraints in a normal-form: all self-loops are collapsed
       to equalities. *)
    let g = LSet.fold (fun v g -> UGraph.add_universe v false g)
			   ctx UGraph.initial_universes
    in
    let add_soft u g =
      if not (Level.is_small u || LSet.mem u ctx)
      then try UGraph.add_universe u false g with UGraph.AlreadyDeclared -> g
      else g
    in
    let g = Constraint.fold
        (fun (l, d, r) g -> add_soft r (add_soft l g))
        csts g
    in
    let g = UGraph.merge_constraints csts g in
      UGraph.constraints_of_universes g
  in
  (* We ignore the trivial Prop/Set <= i constraints. *)
  let noneqs =
    Constraint.filter
      (fun (l,d,r) -> not ((d == Le && Level.is_small l) ||
                           (Level.is_prop l && d == Lt && Level.is_set r)))
      csts
  in
  let noneqs = Constraint.union noneqs smallles in
  let flex x = LMap.mem x us in
  let ctx, us, eqs = List.fold_left (fun (ctx, us, cstrs) s ->
    let canon, (global, rigid, flexible) = choose_canonical ctx flex algs s in
    (* Add equalities for globals which can't be merged anymore. *)
    let cstrs = LSet.fold (fun g cst -> 
      Constraint.add (canon, Eq, g) cst) global
      cstrs 
    in
    (* Also add equalities for rigid variables *)
    let cstrs = LSet.fold (fun g cst -> 
      Constraint.add (canon, Eq, g) cst) rigid
      cstrs
    in
    let canonu = Some (Universe.make canon) in
    let us = LSet.fold (fun f -> LMap.add f canonu) flexible us in
      (LSet.diff ctx flexible, us, cstrs))
    (ctx, us, Constraint.empty) partition
  in
  (* Process weak constraints: when one side is flexible and the 2
     universes are unrelated unify them. *)
  let ctx, us, g = UPairSet.fold (fun (u,v) (ctx, us, g as acc) ->
      let norm = level_subst_of (normalize_univ_variable_opt_subst us) in
      let u = norm u and v = norm v in
      let set_to a b =
        (LSet.remove a ctx,
         LMap.add a (Some (Universe.make b)) us,
         UGraph.enforce_constraint (a,Eq,b) g)
      in
      if UGraph.check_constraint g (u,Le,v) || UGraph.check_constraint g (v,Le,u)
      then acc
      else
      if LMap.mem u us
      then set_to u v
      else if LMap.mem v us
      then set_to v u
      else acc)
      weak (ctx, us, g)  in
  (* Noneqs is now in canonical form w.r.t. equality constraints, 
     and contains only inequality constraints. *)
  let noneqs =
    let norm = level_subst_of (normalize_univ_variable_opt_subst us) in
    Constraint.fold (fun (u,d,v) noneqs ->
        let u = norm u and v = norm v in
        if d != Lt && Level.equal u v then noneqs
        else Constraint.add (u,d,v) noneqs)
      noneqs Constraint.empty
  in
  (* Compute the left and right set of flexible variables, constraints
     mentionning other variables remain in noneqs. *)
  let noneqs, ucstrsl, ucstrsr = 
    Constraint.fold (fun (l,d,r as cstr) (noneq, ucstrsl, ucstrsr) -> 
      let lus = LMap.mem l us and rus = LMap.mem r us in
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

(* let normalize_conkey = CProfile.declare_profile "normalize_context_set" *)
(* let normalize_context_set a b c = CProfile.profile3 normalize_conkey normalize_context_set a b c *)

let is_trivial_leq (l,d,r) =
  Univ.Level.is_prop l && (d == Univ.Le || (d == Univ.Lt && Univ.Level.is_set r))

(* Prop < i <-> Set+1 <= i <-> Set < i *)
let translate_cstr (l,d,r as cstr) =
  if Level.equal Level.prop l && d == Univ.Lt && not (Level.equal Level.set r) then
    (Level.set, d, r)
  else cstr

let refresh_constraints univs (ctx, cstrs) =
  let cstrs', univs' = 
    Univ.Constraint.fold (fun c (cstrs', univs as acc) -> 
      let c = translate_cstr c in
      if is_trivial_leq c then acc
      else (Univ.Constraint.add c cstrs', UGraph.enforce_constraint c univs))
      cstrs (Univ.Constraint.empty, univs)
  in ((ctx, cstrs'), univs')

(** Deprecated *)

(** UnivNames *)
type universe_binders = UnivNames.universe_binders
type univ_name_list = UnivNames.univ_name_list

let pr_with_global_universes = UnivNames.pr_with_global_universes
let reference_of_level = UnivNames.reference_of_level

let add_global_universe = UnivNames.add_global_universe

let is_polymorphic = UnivNames.is_polymorphic

let empty_binders = UnivNames.empty_binders

let register_universe_binders = UnivNames.register_universe_binders
let universe_binders_of_global = UnivNames.universe_binders_of_global

let universe_binders_with_opt_names = UnivNames.universe_binders_with_opt_names

(** UnivGen *)
type universe_id = UnivGen.universe_id

let set_remote_new_univ_id = UnivGen.set_remote_new_univ_id
let new_univ_id = UnivGen.new_univ_id
let new_univ_level = UnivGen.new_univ_level
let new_univ = UnivGen.new_univ
let new_Type = UnivGen.new_Type
let new_Type_sort = UnivGen.new_Type_sort
let new_global_univ = UnivGen.new_global_univ
let new_sort_in_family = UnivGen.new_sort_in_family
let fresh_instance_from_context = UnivGen.fresh_instance_from_context
let fresh_instance_from = UnivGen.fresh_instance_from
let fresh_sort_in_family = UnivGen.fresh_sort_in_family
let fresh_constant_instance = UnivGen.fresh_constant_instance
let fresh_inductive_instance = UnivGen.fresh_inductive_instance
let fresh_constructor_instance = UnivGen.fresh_constructor_instance
let fresh_global_instance = UnivGen.fresh_global_instance
let fresh_global_or_constr_instance = UnivGen.fresh_global_or_constr_instance
let fresh_universe_context_set_instance = UnivGen.fresh_universe_context_set_instance
let global_of_constr = UnivGen.global_of_constr
let constr_of_global_univ = UnivGen.constr_of_global_univ
let extend_context = UnivGen.extend_context
let constr_of_global = UnivGen.constr_of_global
let constr_of_reference = UnivGen.constr_of_global
let type_of_global = UnivGen.type_of_global
