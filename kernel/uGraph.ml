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
open UVars

module G = AcyclicGraph.Make(struct
    type t = Level.t
    module Set = Level.Set
    module Map = Level.Map

    let equal = Level.equal
    let compare = Level.compare

    let raw_pr = Level.raw_pr
  end)
(* Do not include G to make it easier to control universe specific
   code (eg add_universe with a constraint vs G.add with no
   constraint) *)

type t = {
  graph: G.t;
  type_in_type : bool;
  (* above_prop only for checking template poly! *)
  above_prop_qvars : Sorts.QVar.Set.t;
}

(* Universe inconsistency: error raised when trying to enforce a relation
   that would create a cycle in the graph of universes. *)

type path_explanation = G.explanation Lazy.t

type explanation =
  | Path of path_explanation
  | Other of Pp.t

type univ_variable_printers = (Sorts.QVar.t -> Pp.t) * (Level.t -> Pp.t)
type univ_inconsistency = univ_variable_printers option * (constraint_type * Sorts.t * Sorts.t * explanation option)

exception UniverseInconsistency of univ_inconsistency

type 'a check_function = t -> 'a -> 'a -> bool

let set_type_in_type b g = {g with type_in_type=b}

let type_in_type g = g.type_in_type

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
  type_in_type g || Universe.equal u v || (real_check_leq g u v)

let check_eq g u v =
  type_in_type g || Universe.equal u v ||
    (real_check_leq g u v && real_check_leq g v u)

let check_eq_level g u v =
  u == v || type_in_type g || G.check_eq g.graph u v

let empty_universes = {
  graph=G.empty;
  type_in_type=false;
  above_prop_qvars=Sorts.QVar.Set.empty;
}

let initial_universes =
  let big_rank = 1000000 in
  let g = G.empty in
  let g = G.add ~rank:big_rank Level.set g in
  {empty_universes with graph=g}

let initial_universes_with g = {g with graph=initial_universes.graph}

let enforce_constraint (u,d,v) g =
  match d with
  | Le -> G.enforce_leq u v g
  | Lt -> G.enforce_lt u v g
  | Eq -> G.enforce_eq u v g

let enforce_constraint0 cst g = match enforce_constraint cst g.graph with
| None -> None
| Some g' ->
  if g' == g.graph then Some g
  else Some { g with graph = g' }

let enforce_constraint cst g = match enforce_constraint0 cst g with
| None ->
  if not (type_in_type g) then
    let (u, c, v) = cst in
    let e = lazy (G.get_explanation cst g.graph) in
    let mk u = Sorts.sort_of_univ @@ Universe.make u in
    raise (UniverseInconsistency (None, (c, mk u, mk v, Some (Path e))))
  else g
| Some g -> g

let merge_constraints csts g = Constraints.fold enforce_constraint csts g

let check_constraint { graph = g; type_in_type; _ } (u,d,v) =
  type_in_type
  || match d with
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
         match enforce_constraint0 c g with
         | Some g -> Inl (Constraints.add c cstrs,g)
         | None -> Inr (c, g))
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
  | Inr ((u, c, v), g) ->
    let e = lazy (G.get_explanation (u, c, v) g.graph) in
    let mk u = Sorts.sort_of_univ @@ Universe.make u in
    let e = UniverseInconsistency (None, (c, mk u, mk v, Some (Path e))) in
    raise e

exception AlreadyDeclared = G.AlreadyDeclared
let add_universe u ~strict g =
  let graph = G.add u g.graph in
  let d = if strict then Lt else Le in
  enforce_constraint (Level.set, d, u) { g with graph }

let check_declared_universes g l =
  G.check_declared g.graph l

let constraints_of_universes g =
  let add cst accu = Constraints.add cst accu in
  G.constraints_of g.graph add Constraints.empty
let constraints_for ~kept g =
  let add cst accu = Constraints.add cst accu in
  G.constraints_for ~kept g.graph add Constraints.empty

(** Subtyping of polymorphic contexts *)

let check_subtype univs ctxT ctx =
  (* NB: size check is the only constraint on qualities *)
  if eq_sizes (AbstractContext.size ctxT) (AbstractContext.size ctx) then
    let uctx = AbstractContext.repr ctx in
    let inst = UContext.instance uctx in
    let cst = UContext.constraints uctx in
    let cstT = UContext.constraints (AbstractContext.repr ctxT) in
    let push accu v = add_universe v ~strict:false accu in
    let univs = Array.fold_left push univs (snd (Instance.to_array inst)) in
    let univs = merge_constraints cstT univs in
    check_constraints cst univs
  else false

(** Instances *)

let check_eq_instances g t1 t2 =
  let qt1, ut1 = Instance.to_array t1 in
  let qt2, ut2 = Instance.to_array t2 in
  CArray.equal Sorts.Quality.equal qt1 qt2
  && CArray.equal (check_eq_level g) ut1 ut2

let domain g = G.domain g.graph
let choose p g u = G.choose p g.graph u

let check_universes_invariants g = G.check_invariants ~required_canonical:Level.is_set g.graph

(** Sort comparison *)

(* The functions below rely on the invariant that no universe in the graph
   can be unified with Prop / SProp. This is ensured by UGraph, which only
   contains Set as a "small" level. *)

open Sorts

let get_algebraic = function
| Prop | SProp -> assert false
| Set -> Universe.type0
| Type u | QSort (_, u) -> u

let check_eq_sort ugraph s1 s2 = match s1, s2 with
| (SProp, SProp) | (Prop, Prop) | (Set, Set) -> true
| (SProp, _) | (_, SProp) | (Prop, _) | (_, Prop) ->
  type_in_type ugraph
| (Type _ | Set), (Type _ | Set) ->
  check_eq ugraph (get_algebraic s1) (get_algebraic s2)
| QSort (q1, u1), QSort (q2, u2) ->
  QVar.equal q1 q2 && check_eq ugraph u1 u2
| (QSort _, (Type _ | Set)) | ((Type _ | Set), QSort _) -> false

let is_above_prop ugraph q =
  Sorts.QVar.Set.mem q ugraph.above_prop_qvars

let check_leq_sort ugraph s1 s2 = match s1, s2 with
| (SProp, SProp) | (Prop, Prop) | (Set, Set) -> true
| (SProp, _) -> type_in_type ugraph
| (Prop, SProp) -> type_in_type ugraph
| (Prop, (Set | Type _)) -> true
| (Prop, QSort (q,_)) -> is_above_prop ugraph q
| (_, (SProp | Prop)) -> type_in_type ugraph
| (Type _ | Set), (Type _ | Set) ->
  check_leq ugraph (get_algebraic s1) (get_algebraic s2)
| QSort (q1, u1), QSort (q2, u2) ->
  QVar.equal q1 q2 && check_leq ugraph u1 u2
| QSort (q, _), Set -> is_above_prop ugraph q
| QSort (q, u1), Type u2 -> is_above_prop ugraph q && check_leq ugraph u1 u2
| ((Type _ | Set), QSort _) -> false

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

open Pp

let explain_universe_inconsistency default_prq default_prl (printers, (o,u,v,p) : univ_inconsistency) =
  let prq, prl = match printers with
    | Some (prq, prl) -> prq, prl
    | None -> default_prq, default_prl
  in
  let pr_uni u = match u with
  | Sorts.Set -> str "Set"
  | Sorts.Prop -> str "Prop"
  | Sorts.SProp -> str "SProp"
  | Sorts.Type u -> Universe.pr prl u
  | Sorts.QSort (q, u) -> str "Type@{" ++ prq q ++ str " | " ++ Universe.pr prl u ++ str"}"
  in
  let pr_rel = function
    | Eq -> str"=" | Lt -> str"<" | Le -> str"<="
  in
  let reason = match p with
    | None -> mt()
    | Some (Other p) -> spc() ++ p
    | Some (Path p) ->
      let pstart, p = Lazy.force p in
      if p = [] then mt ()
      else
        str " because" ++ spc() ++ prl pstart ++
        prlist (fun (r,v) -> spc() ++ pr_rel r ++ str" " ++ prl v) p
  in
    str "Cannot enforce" ++ spc() ++ pr_uni u ++ spc() ++
      pr_rel o ++ spc() ++ pr_uni v ++ reason

module Internal = struct

  let add_template_qvars qvars g =
    assert (Sorts.QVar.Set.is_empty g.above_prop_qvars);
    {g with above_prop_qvars=qvars}

  let is_above_prop = is_above_prop
end
