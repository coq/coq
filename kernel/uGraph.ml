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

let _debug_ugraph, debug = CDebug.create_full ~name:"uGraph" ()

module G = Loop_checking
(* Do not include G to make it easier to control universe specific
   code (eg add_universe with a constraint vs G.add with no
   constraint) *)

type t = {
  graph: G.t;
  type_in_type : bool;
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

let graph_check_leq g u v = G.check_leq g.graph u v
let graph_check_eq g u v = G.check_eq g.graph u v

let check_leq g u v =
  type_in_type g || Universe.equal u v || graph_check_leq g u v

let check_leq g u u' =
  let res = check_leq g u u' in
  debug Pp.(fun () -> str"check_leq: " ++ Universe.pr Level.raw_pr u ++
    str" <= " ++ Universe.pr Level.raw_pr u' ++ str" = " ++ bool res);
  res

let check_eq g u v =
  type_in_type g || Universe.equal u v || graph_check_eq g u v

let empty_universes = {graph=G.empty; type_in_type=false}

let initial_universes =
  let big_rank = 1000000 in
  let g = G.empty in
  let g = G.add ~rank:big_rank Level.set g in
  {empty_universes with graph=g }

let set_local g =
  { g with graph = G.set_local g.graph }

let clear_constraints g = {g with graph=G.clear_constraints g.graph}

let enforce_constraint (u,d,v) g =
  match d with
  | Le -> G.enforce_leq u v g.graph
  | Eq -> G.enforce_eq u v g.graph

let enforce_constraint0 cst g = match enforce_constraint cst g with
| None -> None
| Some g' ->
  if g' == g.graph then Some g
  else Some { g with graph = g' }

let enforce_constraint cst g = match enforce_constraint0 cst g with
| None ->
  if not (type_in_type g) then
    let (u, c, v) = cst in
    let e = lazy (G.get_explanation cst g.graph) in
    let mk u = Sorts.sort_of_univ u in
    raise (UniverseInconsistency (None, (c, mk u, mk v, Some (Path e))))
  else g
| Some g -> g

let merge_constraints csts g = Constraints.fold enforce_constraint csts g

let check_constraint { graph = g; type_in_type } (u,d,v) =
  type_in_type
  || match d with
  | Le -> G.check_leq g u v
  | Eq -> G.check_eq g u v

let check_constraints csts g = Constraints.for_all (check_constraint g) csts

exception InconsistentEquality = G.InconsistentEquality
let set l u g =
  { g with graph = G.set l u g.graph }

module Bound =
struct
  type t = Prop | Set
end

exception AlreadyDeclared = G.AlreadyDeclared
let add_universe u ~lbound ~strict g = match lbound with
| Bound.Set ->
  let graph = G.add u g.graph in
  let b = if strict then Universe.type1 else Universe.type0 in
  enforce_constraint (b, Le, Universe.make u) { g with graph }
| Bound.Prop ->
  (* Do not actually add any constraint. This is a hack for template. *)
  { g with graph = G.add u g.graph }

let check_declared_universes g l =
  G.check_declared g.graph l

let minimize l g =
  match G.minimize l g.graph with
  | G.HasSubst (graph, lbound) -> G.HasSubst ({ g with graph }, lbound)
  | G.NoBound -> G.NoBound
  | G.CannotSimplify -> G.CannotSimplify

let maximize l g =
  match G.maximize l g.graph with
  | G.HasSubst (graph, lbound) -> G.HasSubst ({ g with graph }, lbound)
  | G.NoBound -> G.NoBound
  | G.CannotSimplify -> G.CannotSimplify

let remove_set_clauses l g =
  let graph = G.remove_set_clauses l g.graph in
  { g with graph }

let pr_model g = G.pr_model g.graph

let constraints_of_universes ?(only_local=false) g =
  let add cst accu = Constraints.add cst accu in
  G.constraints_of g.graph ~only_local add Constraints.empty
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
    let push accu v = add_universe v ~lbound:Bound.Set ~strict:false accu in
    let univs = Array.fold_left push univs (snd (LevelInstance.to_array inst)) in
    let univs = merge_constraints cstT univs in
    check_constraints cst univs
  else false

(** Instances *)

let check_eq_instances g t1 t2 =
  let qt1, ut1 = Instance.to_array t1 in
  let qt2, ut2 = Instance.to_array t2 in
  CArray.equal Sorts.Quality.equal qt1 qt2
  && CArray.equal (check_eq g) ut1 ut2

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

let check_leq_sort ugraph s1 s2 = match s1, s2 with
| (SProp, SProp) | (Prop, Prop) | (Set, Set) -> true
| (SProp, _) -> type_in_type ugraph
| (Prop, SProp) -> type_in_type ugraph
| (Prop, (Set | Type _)) -> true
| (Prop, QSort _) -> false
| (_, (SProp | Prop)) -> type_in_type ugraph
| (Type _ | Set), (Type _ | Set) ->
  check_leq ugraph (get_algebraic s1) (get_algebraic s2)
| QSort (q1, u1), QSort (q2, u2) ->
  QVar.equal q1 q2 && check_leq ugraph u1 u2
| (QSort _, (Type _ | Set)) | ((Type _ | Set), QSort _) -> false

(** Pretty-printing *)

let pr_pmap sep pr map =
  let cmp (u,_) (v,_) = Level.compare u v in
  Pp.prlist_with_sep sep pr (List.sort cmp (Level.Map.bindings map))

let pr_arc prl = let open Pp in
  function
  | u, G.Node l ->
    if CList.is_empty l then mt ()
    else
      (* In increasing order *)
      let l = List.sort (fun (i, _) (i', _) -> Int.compare i i') l in
      let l = CList.factorize_left Int.equal l in
      let pr_cstrs (i, l) =
        let l = List.sort Universe.compare l in
        let k, is_lt = if i >= 1 then pred i, true else 0, false in
        let u = (u, k) in
        LevelExpr.pr prl u ++ spc () ++ v 0
        (prlist_with_sep spc (fun v -> str (if is_lt then "< " else "<= ") ++ Universe.pr prl v) l)
      in
      prlist_with_sep spc pr_cstrs l ++ fnl ()
  | u, G.Alias v ->
    prl u  ++ str " = " ++ LevelExpr.pr prl v ++ fnl  ()

type node = G.node =
| Alias of LevelExpr.t
| Node of (int * Universe.t) list (** Nodes [(k_i, u_i); ...] s.t. u + k_i <= u_i *)

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
    | Eq -> str"=" | Le -> str"≤"
  in
  let pr_erel = function
    | G.UEq -> str"=" | G.ULe -> str"≤" | G.ULt -> str"<"
  in
  let reason = match p with
    | None -> mt()
    | Some (Other p) -> spc() ++ p
    | Some (Path p) ->
      let pstart, p = Lazy.force p in
      if p = [] then mt ()
      else
        str " because" ++ spc() ++ Universe.pr prl pstart ++
        prlist (fun (r,v) -> spc() ++ pr_erel r ++ str" " ++ Universe.pr prl v) p
  in
    str "Cannot enforce" ++ spc() ++ pr_uni u ++ spc() ++
      pr_rel o ++ spc() ++ pr_uni v ++ reason
