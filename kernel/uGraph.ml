(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ

module G = AcyclicGraph.Make(struct
    type t = Level.t
    module Set = Level.Set
    module Map = Level.Map

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

type t = {
  graph: G.t;
  sprop_cumulative : bool;
  type_in_type : bool;
}

type 'a check_function = t -> 'a -> 'a -> bool

let g_map f g =
  let g' = f g.graph in
  if g.graph == g' then g
  else {g with graph=g'}

let set_cumulative_sprop b g = {g with sprop_cumulative=b}

let set_type_in_type b g = {g with type_in_type=b}

let type_in_type g = g.type_in_type
let cumulative_sprop g = g.sprop_cumulative

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

(** TODO: enforce this by typing *)
let in_graph u = not (Level.is_prop u) && not (Level.is_sprop u)
let in_graph_univ u = not (Universe.is_type0m u) && not (Universe.is_sprop u)

let check_leq g u v =
  let () = assert (in_graph_univ u && in_graph_univ v) in
  type_in_type g || Universe.equal u v || (real_check_leq g u v)

let check_eq g u v =
  let () = assert (in_graph_univ u && in_graph_univ v) in
  type_in_type g || Universe.equal u v ||
    (real_check_leq g u v && real_check_leq g v u)

let check_eq_level g u v =
  let () = assert (in_graph u && in_graph v) in
  u == v || type_in_type g || G.check_eq g.graph u v

let empty_universes = {graph=G.empty; sprop_cumulative=false; type_in_type=false}

let initial_universes =
  let big_rank = 1000000 in
  let g = G.empty in
  let g = G.add ~rank:big_rank Level.set g in
  {empty_universes with graph=g}

let initial_universes_with g = {g with graph=initial_universes.graph}

let enforce_constraint (u,d,v) g =
  let () = assert (in_graph u && in_graph v) in
  match d with
  | Le -> G.enforce_leq u v g
  | Lt -> G.enforce_lt u v g
  | Eq -> G.enforce_eq u v g

let enforce_constraint cst g =
  g_map (enforce_constraint cst) g

let enforce_constraint cst g =
  if not (type_in_type g) then enforce_constraint cst g
  else try enforce_constraint cst g with UniverseInconsistency _ -> g

let merge_constraints csts g = Constraints.fold enforce_constraint csts g

let check_constraint { graph = g; _ } (u,d,v) =
  let () = assert (in_graph u && in_graph v) in
  match d with
  | Le -> G.check_leq g u v
  | Lt -> G.check_lt g u v
  | Eq -> G.check_eq g u v

let check_constraints csts g = Constraints.for_all (check_constraint g) csts

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
         | g -> Inl (Constraints.add c cstrs,g)
         | exception (UniverseInconsistency _ as e) -> Inr e)
  in
  (* max(us) <= max(vs) <-> forall u in us, exists v in vs, u <= v *)
  let c = List.map (fun u -> List.map (fun v -> (u,v)) (Universe.repr v)) (Universe.repr u) in
  let c = List.cartesians enforce_one (Inl (Constraints.empty,g)) c in
  (* We pick a best constraint: smallest number of constraints, not an error if possible. *)
  let order x y = match x, y with
    | Inr _, Inr _ -> 0
    | Inl _, Inr _ -> -1
    | Inr _, Inl _ -> 1
    | Inl (c,_), Inl (c',_) ->
      Int.compare (Constraints.cardinal c) (Constraints.cardinal c')
  in
  match List.min order c with
  | Inl x -> x
  | Inr e -> raise e

let enforce_leq_alg u v g =
  match Universe.is_sprop u, Universe.is_sprop v with
  | true, true -> Constraints.empty, g
  | false, false -> enforce_leq_alg u v g
  | left, _ ->
    if left && g.sprop_cumulative then Constraints.empty, g
    else raise (UniverseInconsistency (Le, u, v, None))

(* sanity check wrapper *)
let enforce_leq_alg u v g =
  let _,g as cg = enforce_leq_alg u v g in
  assert (check_leq g u v);
  cg

module Bound =
struct
  type t = Prop | Set
end

exception AlreadyDeclared = G.AlreadyDeclared
let add_universe u ~lbound ~strict g = match lbound with
| Bound.Set ->
  let graph = G.add u g.graph in
  let d = if strict then Lt else Le in
  enforce_constraint (Level.set, d, u) { g with graph }
| Bound.Prop ->
  (* Do not actually add any constraint. This is a hack for template. *)
  { g with graph = G.add u g.graph }

exception UndeclaredLevel = G.Undeclared
let check_declared_universes g l =
  G.check_declared g.graph (Level.Set.remove Level.prop (Level.Set.remove Level.sprop l))

let constraints_of_universes g =
  let add cst accu = Constraints.add cst accu in
  G.constraints_of g.graph add Constraints.empty
let constraints_for ~kept g =
  let add cst accu = Constraints.add cst accu in
  G.constraints_for ~kept:(Level.Set.remove Level.prop (Level.Set.remove Level.sprop kept)) g.graph add Constraints.empty

(** Subtyping of polymorphic contexts *)

let check_subtype univs ctxT ctx =
  if AbstractContext.size ctxT == AbstractContext.size ctx then
    let uctx = AbstractContext.repr ctx in
    let inst = UContext.instance uctx in
    let cst = UContext.constraints uctx in
    let cstT = UContext.constraints (AbstractContext.repr ctxT) in
    let push accu v = add_universe v ~lbound:Bound.Set ~strict:false accu in
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

let domain g = Level.Set.add Level.prop (Level.Set.add Level.sprop (G.domain g.graph))
let choose p g u =
  if not (in_graph u) then
    if p u then Some u else None
  else G.choose p g.graph u

let check_universes_invariants g = G.check_invariants ~required_canonical:Level.is_set g.graph

(** Pretty-printing *)

let pr_pmap sep pr map =
  let cmp (u,_) (v,_) = Level.compare u v in
  Pp.prlist_with_sep sep pr (List.sort cmp (Level.Map.bindings map))

let pr_arc prl = let open Pp in
  function
  | u, G.Node ltle ->
    if Level.Map.is_empty ltle then mt ()
    else
      prl u ++ str " " ++
      v 0
        (pr_pmap spc (fun (v, strict) ->
              (if strict then str "< " else str "<= ") ++ prl v)
            ltle) ++
      fnl ()
  | u, G.Alias v ->
    prl u  ++ str " = " ++ prl v ++ fnl ()

type node = G.node =
| Alias of Level.t
| Node of bool Level.Map.t

let repr g = G.repr g.graph

let pr_universes prl g = pr_pmap Pp.mt (pr_arc prl) g
