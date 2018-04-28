(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ
open UnivSubst

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
  let open Pp in
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
        let left = CList.uniquize (List.filter (not_lower lower) left) in
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
