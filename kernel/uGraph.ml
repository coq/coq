(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ

module G = AcyclicGraph.Make(struct
    type t = Level.t
    module Set = LSet
    module Map = LMap
    module Constraint = Constraint

    let equal = Level.equal
    let compare = Level.compare

    type explanation = Univ.explanation
    let error_inconsistency d u v p =
      raise (UniverseInconsistency (d,Universe.make u, Universe.make v, p))

    let pr = Level.pr
  end) [@@inlined] (* without inline, +1% ish on HoTT, compcert. See jenkins 594 vs 596 *)
(* Do not include G to make it easier to control universe specific
   code (eg add_universe with a constraint vs G.add with no
   constraint) *)

type t = { graph: G.t; sprop_cumulative : bool }
type 'a check_function = t -> 'a -> 'a -> bool

let g_map f g =
  let g' = f g.graph in
  if g.graph == g' then g
  else {g with graph=g'}

let make_sprop_cumulative g = {g with sprop_cumulative=true}

let check_smaller_expr g (u,n) (v,m) =
  let diff = n - m in
    match diff with
    | 0 -> G.check_leq g.graph u v
    | 1 -> G.check_lt g.graph u v
    | x when x < 0 -> G.check_leq g.graph u v
    | _ -> false

let exists_bigger g ul l =
  Universe.exists (fun ul' ->
    check_smaller_expr g ul ul') l

let real_check_leq g u v =
  Universe.for_all (fun ul -> exists_bigger g ul v) u

let check_leq g u v =
  Universe.equal u v || (g.sprop_cumulative && Universe.is_sprop u) ||
  (not (Universe.is_sprop u) && not (Universe.is_sprop v) &&
    (is_type0m_univ u ||
     real_check_leq g u v))

let check_eq g u v =
  Universe.equal u v ||
  (not (Universe.is_sprop u || Universe.is_sprop v) &&
   (real_check_leq g u v && real_check_leq g v u))

let check_eq_level g u v =
  u == v ||
  (not (Level.is_sprop u || Level.is_sprop v) && G.check_eq g.graph u v)

let empty_universes = {graph=G.empty; sprop_cumulative=false}

let initial_universes =
  let big_rank = 1000000 in
  let g = G.empty in
  let g = G.add ~rank:big_rank Level.prop g in
  let g = G.add ~rank:big_rank Level.set g in
  {graph=G.enforce_lt Level.prop Level.set g; sprop_cumulative=false}

let enforce_constraint (u,d,v) g =
  match d with
  | Le -> G.enforce_leq u v g
  | Lt -> G.enforce_lt u v g
  | Eq -> G.enforce_eq u v g

let enforce_constraint (u,d,v as cst) g =
  match Level.is_sprop u, d, Level.is_sprop v with
  | false, _, false -> g_map (enforce_constraint cst) g
  | true, (Eq|Le), true -> g
  | true, Le, false when g.sprop_cumulative -> g
  | _ ->  raise (UniverseInconsistency (d,Universe.make u, Universe.make v, None))

let merge_constraints csts g = Constraint.fold enforce_constraint csts g

let check_constraint g (u,d,v) =
  match d with
  | Le -> G.check_leq g u v
  | Lt -> G.check_lt g u v
  | Eq -> G.check_eq g u v

let check_constraint g (u,d,v as cst) =
  match Level.is_sprop u, d, Level.is_sprop v with
  | false, _, false -> check_constraint g.graph cst
  | true, (Eq|Le), true -> true
  | true, Le, false -> g.sprop_cumulative
  | _ -> false

let check_constraints csts g = Constraint.for_all (check_constraint g) csts

let leq_expr (u,m) (v,n) =
  let d = match m - n with
    | 1 -> Lt
    | diff -> assert (diff <= 0); Le
  in
  (u,d,v)

let enforce_leq_alg u v g =
  let open Util in
  let enforce_one (u,v) = function
    | Inr _ as orig -> orig
    | Inl (cstrs,g) as orig ->
      if check_smaller_expr g u v then orig
      else
        (let c = leq_expr u v in
         match enforce_constraint c g with
         | g -> Inl (Constraint.add c cstrs,g)
         | exception (UniverseInconsistency _ as e) -> Inr e)
  in
  (* max(us) <= max(vs) <-> forall u in us, exists v in vs, u <= v *)
  let c = Universe.map (fun u -> Universe.map (fun v -> (u,v)) v) u in
  let c = List.cartesians enforce_one (Inl (Constraint.empty,g)) c in
  (* We pick a best constraint: smallest number of constraints, not an error if possible. *)
  let order x y = match x, y with
    | Inr _, Inr _ -> 0
    | Inl _, Inr _ -> -1
    | Inr _, Inl _ -> 1
    | Inl (c,_), Inl (c',_) ->
      Int.compare (Constraint.cardinal c) (Constraint.cardinal c')
  in
  match List.min order c with
  | Inl x -> x
  | Inr e -> raise e

(* sanity check wrapper *)
let enforce_leq_alg u v g =
  let _,g as cg = enforce_leq_alg u v g in
  assert (check_leq g u v);
  cg

exception AlreadyDeclared = G.AlreadyDeclared
let add_universe u strict g =
  let graph = G.add u g.graph in
  let d = if strict then Lt else Le in
  enforce_constraint (Level.set,d,u) {g with graph}

let add_universe_unconstrained u g = {g with graph=G.add u g.graph}

exception UndeclaredLevel = G.Undeclared
let check_declared_universes g l = G.check_declared g.graph (LSet.remove Level.sprop l)

let constraints_of_universes g = G.constraints_of g.graph
let constraints_for ~kept g = G.constraints_for ~kept:(LSet.remove Level.sprop kept) g.graph

(** Subtyping of polymorphic contexts *)

let check_subtype univs ctxT ctx =
  if AUContext.size ctxT == AUContext.size ctx then
    let (inst, cst) = UContext.dest (AUContext.repr ctx) in
    let cstT = UContext.constraints (AUContext.repr ctxT) in
    let push accu v = add_universe v false accu in
    let univs = Array.fold_left push univs (Instance.to_array inst) in
    let univs = merge_constraints cstT univs in
    check_constraints cst univs
  else false

(** Instances *)

let check_eq_instances g t1 t2 =
  let t1 = Instance.to_array t1 in
  let t2 = Instance.to_array t2 in
  t1 == t2 ||
    (Int.equal (Array.length t1) (Array.length t2) &&
        let rec aux i =
          (Int.equal i (Array.length t1)) || (check_eq_level g t1.(i) t2.(i) && aux (i + 1))
        in aux 0)

let domain g = LSet.add Level.sprop (G.domain g.graph)
let choose p g u = if Level.is_sprop u
  then if p u then Some u else None
  else G.choose p g.graph u

let dump_universes f g = G.dump f g.graph

let check_universes_invariants g = G.check_invariants ~required_canonical:Level.is_small g.graph

let pr_universes prl g = G.pr prl g.graph

let dummy_mp = Names.DirPath.make [Names.Id.of_string "Type"]
let make_dummy i = Level.(make (UGlobal.make dummy_mp i))
let sort_universes g = g_map (G.sort make_dummy [Level.prop;Level.set]) g

(** Profiling *)

let merge_constraints =
  if Flags.profile then
    let key = CProfile.declare_profile "merge_constraints" in
      CProfile.profile2 key merge_constraints
  else merge_constraints
let check_constraints =
  if Flags.profile then
    let key = CProfile.declare_profile "check_constraints" in
      CProfile.profile2 key check_constraints
  else check_constraints

let check_eq =
  if Flags.profile then
    let check_eq_key = CProfile.declare_profile "check_eq" in
      CProfile.profile3 check_eq_key check_eq
  else check_eq

let check_leq =
  if Flags.profile then
    let check_leq_key = CProfile.declare_profile "check_leq" in
      CProfile.profile3 check_leq_key check_leq
  else check_leq
