(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ
open UnivSubst

(* To disallow minimization to Set *)
let { Goptions.get = get_set_minimization } =
  Goptions.declare_bool_option_and_ref
    ~key:["Universe";"Minimization";"ToSet"]
    ~value:true
    ()

(** Simplification *)

let add_list_map u t map =
  try
    let l = Level.Map.find u map in
    Level.Map.set u (t :: l) map
  with Not_found ->
    Level.Map.add u [t] map

(** Precondition: flexible <= ctx *)
let choose_canonical ctx flexible algebraic s =
  let global = Level.Set.diff s ctx in
  let flexible, rigid = Level.Set.partition flexible (Level.Set.inter s ctx) in
    (* If there is a global universe in the set, choose it *)
    if not (Level.Set.is_empty global) then
      let canon = Level.Set.choose global in
        canon, (Level.Set.remove canon global, rigid, flexible)
    else (* No global in the equivalence class, choose a rigid one *)
        if not (Level.Set.is_empty rigid) then
          let canon = Level.Set.choose rigid in
            canon, (global, Level.Set.remove canon rigid, flexible)
        else (* There are only flexible universes in the equivalence
                 class, choose a non-algebraic. *)
          let algs, nonalgs = Level.Set.partition algebraic flexible in
            if not (Level.Set.is_empty nonalgs) then
              let canon = Level.Set.choose nonalgs in
                canon, (global, rigid, Level.Set.remove canon flexible)
            else
              let canon = Level.Set.choose algs in
                canon, (global, rigid, Level.Set.remove canon flexible)

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

type lowermap = constraint_type Level.Map.t

let lower_union =
  let merge k a b =
    match a, b with
    | Some _, None -> a
    | None, Some _ -> b
    | None, None -> None
    | Some l, Some r ->
       if compare_constraint_type l r >= 0 then a
       else b
  in Level.Map.merge merge

let lower_add l c m =
  try let c' = Level.Map.find l m in
      if compare_constraint_type c c' > 0 then
        Level.Map.add l c m
      else m
  with Not_found -> Level.Map.add l c m

let lower_of_list l =
  List.fold_left (fun acc (d,l) -> Level.Map.add l d acc) Level.Map.empty l

type lbound = { enforce : bool; alg : bool; lbound: Universe.t; lower : lowermap }

module LBMap :
sig
  type t = private { lbmap : lbound Level.Map.t; lbrev : (Level.t * lowermap) Universe.Map.t }
  val empty : t
  val add : Level.t -> lbound -> t -> t
end =
struct
  type t = { lbmap : lbound Level.Map.t; lbrev : (Level.t * lowermap) Universe.Map.t }
  (* lbrev is uniquely given from lbmap as a partial reverse mapping *)
  let empty = { lbmap = Level.Map.empty; lbrev = Universe.Map.empty }
  let add u bnd m =
    let lbmap = Level.Map.add u bnd m.lbmap in
    let lbrev =
      if not bnd.alg && bnd.enforce then
        match Universe.Map.find bnd.lbound m.lbrev with
        | (v, _) ->
          if Level.compare u v <= 0 then
            Universe.Map.add bnd.lbound (u, bnd.lower) m.lbrev
          else m.lbrev
        | exception Not_found ->
          Universe.Map.add bnd.lbound (u, bnd.lower) m.lbrev
      else m.lbrev
    in
    { lbmap; lbrev }
end

let find_inst insts v = Universe.Map.find v insts.LBMap.lbrev

let compute_lbound left =
 (* The universe variable was not fixed yet.
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

let instantiate_with_lbound u lbound lower ~alg ~enforce (ctx, us, insts, cstrs) =
  if enforce then
    let inst = Universe.make u in
    let cstrs' = enforce_leq lbound inst cstrs in
      (ctx, UnivFlex.make_nonalgebraic_variable us u,
       LBMap.add u {enforce;alg;lbound;lower} insts, cstrs'),
      {enforce; alg; lbound=inst; lower}
  else (* Actually instantiate *)
    (Level.Set.remove u ctx, UnivFlex.define u lbound us,
     LBMap.add u {enforce;alg;lbound;lower} insts, cstrs),
    {enforce; alg; lbound; lower}

type constraints_map = (constraint_type * Level.Map.key) list Level.Map.t

let _pr_constraints_map (cmap:constraints_map) =
  let open Pp in
  Level.Map.fold (fun l cstrs acc ->
    Level.raw_pr l ++ str " => " ++
      prlist_with_sep spc (fun (d,r) -> pr_constraint_type d ++ Level.raw_pr r) cstrs ++
      fnl () ++ acc)
    cmap (mt ())

let remove_alg l (ctx, us, insts, cstrs) =
  (ctx, UnivFlex.make_nonalgebraic_variable us l, insts, cstrs)

let not_lower lower (d,l) =
  (* We're checking if (d,l) is already implied by the lower
     constraints on some level u. If it represents l < u (d is Lt
     or d is Le and i > 0, the i < 0 case is impossible due to
     invariants of Univ), and the lower constraints only have l <=
     u then it is not implied. *)
  Universe.exists
    (fun (l,i) ->
       let d =
         if i == 0 then d
         else match d with
           | Le -> Lt
           | d -> d
       in
       try let d' = Level.Map.find l lower in
         (* If d is stronger than the already implied lower
          * constraints we must keep it. *)
         compare_constraint_type d d' > 0
       with Not_found ->
         (* No constraint existing on l *) true) l

exception UpperBoundedAlg

(** [enforce_uppers upper lbound cstrs] interprets [upper] as upper
   constraints to [lbound], adding them to [cstrs].

    @raise UpperBoundedAlg if any [upper] constraints are strict and
   [lbound] algebraic. *)
let enforce_uppers upper lbound cstrs =
  List.fold_left (fun cstrs (d, r) ->
      if d == Le then
        enforce_leq lbound (Universe.make r) cstrs
      else
        match Universe.level lbound with
        | Some lev -> Constraints.add (lev, d, r) cstrs
        | None -> raise UpperBoundedAlg)
    cstrs upper

let minimize_univ_variables ctx us left right cstrs =
  let left, lbounds =
    Level.Map.fold (fun r lower (left, lbounds as acc)  ->
      if UnivFlex.mem r us || not (Level.Set.mem r ctx) then acc
      else (* Fixed universe, just compute its glb for sharing *)
        let lbounds =
          match compute_lbound (List.map (fun (d,l) -> d, Universe.make l) lower) with
          | None -> lbounds
          | Some lbound -> LBMap.add r {enforce=true; alg=false; lbound; lower=lower_of_list lower}
                                   lbounds
        in (Level.Map.remove r left, lbounds))
      left (left, LBMap.empty)
  in
  let rec instance (ctx, us, insts, cstrs as acc) u =
    let acc, left, lower =
      match Level.Map.find u left with
      | exception Not_found -> acc, [], Level.Map.empty
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
          (acc, [], Level.Map.empty, Level.Map.empty) l
        in
        let left = CList.uniquize (List.filter (not_lower lower) left) in
        (acc, left, Level.Map.lunion newlow lower)
    in
    let instantiate_lbound lbound =
      let alg = UnivFlex.is_algebraic u us in
        if Universe.is_type0 lbound && not (get_set_minimization()) then
          (* Minim to Set disabled, do not instantiate with Set *)
          instantiate_with_lbound u lbound lower ~alg ~enforce:true acc
        else if alg then
          (* u is algebraic: we instantiate it with its lower bound, if any,
              or enforce the constraints if it is bounded from the top. *)
          let lower = Level.Set.fold Level.Map.remove (Universe.levels lbound) lower in
          instantiate_with_lbound u lbound lower ~alg:true ~enforce:false acc
        else (* u is non algebraic *)
          match Universe.level lbound with
          | Some l -> (* The lowerbound is directly a level *)
             (* u is not algebraic but has no upper bounds,
                we instantiate it with its lower bound if it is a
                different level, otherwise we keep it. *)
             let lower = Level.Map.remove l lower in
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
                let lower = Level.Map.remove can lower in
                instantiate_with_lbound u (Universe.make can) lower ~alg:false ~enforce:false acc
              | exception Not_found ->
                (* We set u as the canonical universe representing lbound *)
                instantiate_with_lbound u lbound lower ~alg:false ~enforce:true acc
            end
    in
    let enforce_uppers ((ctx,us,insts,cstrs), b as acc) =
      match Level.Map.find u right with
      | exception Not_found -> acc
      | upper ->
        let upper = List.filter (fun (d, r) -> not (UnivFlex.mem r us)) upper in
        let cstrs = enforce_uppers upper b.lbound cstrs in
        (ctx, us, insts, cstrs), b
    in
    if not (Level.Set.mem u ctx)
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
  and aux (ctx, us, seen, cstrs as acc) u =
    try acc, Level.Map.find u seen.LBMap.lbmap
    with Not_found -> instance acc u
  in
    UnivFlex.fold (fun u ~is_defined (ctx, us, seen, cstrs as acc) ->
      if not is_defined then fst (aux acc u)
      else Level.Set.remove u ctx, UnivFlex.make_nonalgebraic_variable us u, seen, cstrs)
      us (ctx, us, lbounds, cstrs)

module UPairs = OrderedType.UnorderedPair(Level)
module UPairSet = Set.Make (UPairs)

type extra = {
  weak_constraints : UPairSet.t;
  above_prop : Level.Set.t;
}

let empty_extra = {
  weak_constraints = UPairSet.empty;
  above_prop = Level.Set.empty;
}

let extra_union a b = {
  weak_constraints = UPairSet.union a.weak_constraints b.weak_constraints;
  above_prop = Level.Set.union a.above_prop b.above_prop;
}

let normalize_context_set g ctx (us:UnivFlex.t) {weak_constraints=weak;above_prop} =
  let (ctx, csts) = ContextSet.levels ctx, ContextSet.constraints ctx in
  (* Keep the Set <= i constraints separate *)
  let smallles, csts =
    Constraints.partition (fun (l,d,r) -> d == Le && Level.is_set l) csts
  in
  (* Process weak constraints: when one side is flexible and the 2
     universes are unrelated unify them. *)
  let smallles, csts, g = UPairSet.fold (fun (u,v) (smallles, csts, g as acc) ->
      let norm = level_subst_of (UnivFlex.normalize_univ_variable us) in
      let u = norm u and v = norm v in
      if (Level.is_set u || Level.is_set v) then begin
        if get_set_minimization() then begin
          if Level.is_set u then (Constraints.add (u,Le,v) smallles,csts,g)
          else (Constraints.add (v,Le,u) smallles,csts,g)
        end else acc
      end else
        let set_to a b =
          (smallles,
           Constraints.add (a,Eq,b) csts,
           UGraph.enforce_constraint (a,Eq,b) g)
        in
        let check_le a b = UGraph.check_constraint g (a,Le,b) in
        if check_le u v || check_le v u
        then acc
        else if UnivFlex.mem u us
        then set_to u v
        else if UnivFlex.mem v us
        then set_to v u
        else acc)
      weak (smallles, csts, g)
  in
  let smallles = if get_set_minimization () then
      Constraints.filter (fun (l,d,r) -> UnivFlex.mem r us) smallles
    else  Constraints.empty (* constraints Set <= u may be dropped *)
  in
  let smallles = if get_set_minimization() then
      let fold u accu = if UnivFlex.mem u us then Constraints.add (Level.set, Le, u) accu else accu in
      Level.Set.fold fold above_prop smallles
    else smallles
  in
  let csts, partition =
    (* We first put constraints in a normal-form: all self-loops are collapsed
       to equalities. *)
    let g = UGraph.initial_universes_with g in
    (* use lbound:Set to collapse [u <= v <= Set] into [u = v = Set] *)
    let g = Level.Set.fold (fun v g -> UGraph.add_universe ~strict:false v g)
        ctx g
    in
    let add_soft u g =
      if not (Level.is_set u || Level.Set.mem u ctx)
      then try UGraph.add_universe ~strict:false u g with UGraph.AlreadyDeclared -> g
      else g
    in
    let g = Constraints.fold
        (fun (l, d, r) g -> add_soft r (add_soft l g))
        csts g
    in
    let g = UGraph.merge_constraints csts g in
      UGraph.constraints_of_universes g
  in
  (* Ignore constraints from lbound:Set *)
  let noneqs =
    Constraints.filter
      (fun (l,d,r) -> not (d == Le && Level.is_set l))
      csts
  in
  (* Put back constraints [Set <= u] from type inference *)
  let noneqs = Constraints.union noneqs smallles in
  let flex x = UnivFlex.mem x us in
  let algebraic x = UnivFlex.is_algebraic x us in
  let ctx, us, eqs = List.fold_left (fun (ctx, us, cstrs) s ->
      let canon, (global, rigid, flexible) = choose_canonical ctx flex algebraic s in
      (* Add equalities for globals which can't be merged anymore. *)
      let cstrs = Level.Set.fold (fun g cst ->
          Constraints.add (canon, Eq, g) cst) global
          cstrs
      in
      (* Also add equalities for rigid variables *)
      let cstrs = Level.Set.fold (fun g cst ->
          Constraints.add (canon, Eq, g) cst) rigid
          cstrs
      in
      let canonu = Universe.make canon in
      let us = Level.Set.fold (fun f -> UnivFlex.define f canonu) flexible us in
      (Level.Set.diff ctx flexible, us, cstrs))
      (ctx, us, Constraints.empty) partition
  in
  (* Noneqs is now in canonical form w.r.t. equality constraints,
     and contains only inequality constraints. *)
  let noneqs =
    let norm = level_subst_of (UnivFlex.normalize_univ_variable us) in
    let fold (u,d,v) noneqs =
      let u = norm u and v = norm v in
      if d != Lt && Level.equal u v then noneqs
      else Constraints.add (u,d,v) noneqs
    in
    Constraints.fold fold noneqs Constraints.empty
  in
  (* Compute the left and right set of flexible variables, constraints
     mentioning other variables remain in noneqs. *)
  let noneqs, ucstrsl, ucstrsr =
    Constraints.fold (fun (l,d,r as cstr) (noneq, ucstrsl, ucstrsr) ->
      let lus = UnivFlex.mem l us and rus = UnivFlex.mem r us in
      let ucstrsl' =
        if lus then add_list_map l (d, r) ucstrsl
        else ucstrsl
      and ucstrsr' =
        add_list_map r (d, l) ucstrsr
      in
      let noneqs =
        if lus || rus then noneq
        else Constraints.add cstr noneq
      in (noneqs, ucstrsl', ucstrsr'))
    noneqs (Constraints.empty, Level.Map.empty, Level.Map.empty)
  in
  (* Now we construct the instantiation of each variable. *)
  let ctx', us, inst, noneqs =
    minimize_univ_variables ctx us ucstrsr ucstrsl noneqs
  in
  let us = UnivFlex.normalize us in
  us, (ctx', Constraints.union noneqs eqs)
