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
open UnivConstraint

let _debug_ugraph, debug = CDebug.create_full ~name:"uGraph" ()

module G = Loop_checking
(* Do not include G to make it easier to control universe specific
   code (eg add_universe with a constraint vs G.add with no
   constraint) *)

type t = {
  graph: G.t;
  type_in_type: bool;
  above_prop_qvars: Sorts.QVar.Set.t;
}

type locality = Loop_checking.locality = Global | Local

(* Universe inconsistency: error raised when trying to enforce a relation
   that would create a cycle in the graph of universes. *)

type path_explanation = G.explanation Lazy.t

type explanation =
  | Path of path_explanation
  | Other of Pp.t

type univ_inconsistency = Sorts.printer option * (UnivConstraint.kind * Sorts.t * Sorts.t * explanation option)

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

let empty_universes = {
  graph=G.empty;
  type_in_type=false;
  above_prop_qvars=Sorts.QVar.Set.empty;
}

let initial_universes =
  let g = G.empty in
  let g = G.add ~rigid:true Level.set g in
  {empty_universes with graph=g }

let set_local g =
  { g with graph = G.set_local g.graph }

type level_equivalences = (Level.t * (Level.t * int)) list

let enforce_constraint (u,d,v) g =
  match d with
  | Le -> G.enforce_leq u v g.graph
  | Eq -> G.enforce_eq u v g.graph

let enforce_constraint0 cst g = match enforce_constraint cst g with
| None -> None
| Some (g', equivs) ->
  if g' == g.graph then Some (g, equivs)
  else Some ({ g with graph = g' }, equivs)

let enforce_constraint cst g = match enforce_constraint0 cst g with
| None ->
  if not (type_in_type g) then
    let (u, c, v) = cst in
    let e = lazy (G.get_explanation cst g.graph) in
    let mk u = Sorts.sort_of_univ u in
    raise (UniverseInconsistency (None, (c, mk u, mk v, Some (Path e))))
  else g, []
| Some g -> g

let merge_constraints csts g =
  UnivConstraints.fold (fun cst (g, equivs) ->
    let g, equivs' = enforce_constraint cst g in
    g, equivs' @ equivs) csts (g, [])

let check_constraint { graph = g; type_in_type; _ } (u,d,v) =
  type_in_type
  || match d with
  | Le -> G.check_leq g u v
  | Eq -> G.check_eq g u v

let check_constraints csts g = UnivConstraints.for_all (check_constraint g) csts

let is_above_prop ugraph q =
  Sorts.QVar.Set.mem q ugraph.above_prop_qvars

let check_eq_sort qeq univs s1 s2 =
  let u1 = Sorts.univ_of_sort s1 in
  let u2 = Sorts.univ_of_sort s2 in
  let q1 = Sorts.quality s1 in
  let q2 = Sorts.quality s2 in
  qeq q1 q2 && (type_in_type univs || check_eq univs u1 u2)

let check_leq_sort qeq univs s1 s2 =
  if type_in_type univs then
    let q1 = Sorts.quality s1 in
    let q2 = Sorts.quality s2 in
    let open Sorts.Quality in
    match q1, q2 with
    | QConstant QProp, QConstant QType -> true
    | _ -> qeq q1 q2
  else
    match s1, s2 with
    | (SProp, SProp) | (Prop, Prop) | (Set, Set) -> true
    | (Prop, (Set | Type _)) -> true
    | (Prop, VSort (q, _)) -> is_above_prop univs q
    | (Type _ | Set), (Set | Type _) -> check_leq univs (Sorts.univ_of_sort s1) (Sorts.univ_of_sort s2)
    | (GSort (s1, u1), GSort (s2, u2)) ->
      qeq (QGlobal s1) (QGlobal s2) && check_leq univs u1 u2
    | (VSort (s1, u1), VSort (s2, u2)) ->
      qeq (QVar s1) (QVar s2) && check_leq univs u1 u2
    | (GSort (s1, u1), VSort (s2, u2)) ->
      qeq (QGlobal s1) (QVar s2) && check_leq univs u1 u2
    | (VSort (s1, u1), GSort (s2, u2)) ->
      qeq (QVar s1) (QGlobal s2) && check_leq univs u1 u2
    | (VSort (q, u1), Type u2) -> is_above_prop univs q && check_leq univs u1 u2
    | ((SProp | Prop | Set | Type _ | GSort _ | VSort _), _) -> false

let normalize { graph = g; _ } l = G.normalize g l

exception InconsistentEquality = G.InconsistentEquality
exception OccurCheck = G.OccurCheck

let set l u g =
  let g', equivs = G.set l u g.graph in
  { g with graph = g' }, equivs

exception AlreadyDeclared = G.AlreadyDeclared
let add_universe u ~strict ~rigid g =
  let graph = G.add ~rigid u g.graph in
  let b = if strict then Universe.type1 else Universe.type0 in
  fst (enforce_constraint (b, Le, Universe.make u) { g with graph })

let switch_locality u g = { g with graph = G.switch_locality u g.graph }

let check_declared_universes g l =
  G.check_declared g.graph l

let is_declared g l =
  G.is_declared g.graph l

let minimize l g =
  match G.minimize l g.graph with
  | G.HasSubst (graph, equivs, lbound) -> G.HasSubst ({ g with graph }, equivs, lbound)
  | G.NoBound -> G.NoBound
  | G.CannotSimplify -> G.CannotSimplify

let maximize l g =
  match G.maximize l g.graph with
  | G.HasSubst (graph, equivs, lbound) -> G.HasSubst ({ g with graph }, equivs, lbound)
  | G.NoBound -> G.NoBound
  | G.CannotSimplify -> G.CannotSimplify

let remove_set_clauses l g =
  let graph = G.remove_set_clauses l g.graph in
  { g with graph }

let pr_model ?local g = G.pr_model ?local g.graph

let constraints_of_universes ?(only_local=false) g =
  let add cst accu = UnivConstraints.add cst accu in
  G.constraints_of g.graph ~only_local add UnivConstraints.empty
let constraints_for ~kept g =
  let add cst accu = UnivConstraints.add cst accu in
  G.constraints_for ~kept g.graph add UnivConstraints.empty

let remove removed g =
  { g with graph = G.remove removed g.graph }

let subst ?(local=false) g = G.subst ~local g.graph

(** Instances *)

let check_eq_instances qeq univs t1 t2 =
  let qt1, ut1 = Instance.to_array t1 in
  let qt2, ut2 = Instance.to_array t2 in
  CArray.equal qeq qt1 qt2
  && CArray.equal (check_eq univs) ut1 ut2

let domain g = G.domain g.graph

let variables ~local ~with_subst g = G.variables ~local ~with_subst g.graph

let check_universes_invariants g = G.check_invariants ~required_canonical:Level.is_set g.graph

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
        LevelExpr.pr prl u ++ str " " ++ v 0
        (prlist_with_sep spc (fun v -> str (if is_lt then "< " else "<= ") ++ Universe.pr prl v) l)
      in
      prlist_with_sep fnl pr_cstrs l ++ fnl ()
  | u, G.Alias u' ->
    prl u  ++ str " = " ++ Universe.pr prl u' ++ fnl  ()

type node = G.node =
| Alias of Universe.t
| Node of (int * Universe.t) list (** Nodes [(k_i, u_i); ...] s.t. u + k_i <= u_i *)

let repr ?(local=false) g = G.repr ~local g.graph

let pr_universes prl g = pr_pmap Pp.mt (pr_arc prl) g

let pr ?(local=false) prl g = pr_universes prl (repr ~local g)

open Pp

let explain_universe_inconsistency default_printer (printer, (o,u,v,p) : univ_inconsistency) =
  let printer = Option.default default_printer printer in
  let pr_uni u = match u with
  | Sorts.Set -> str "Set"
  | Sorts.Prop -> str "Prop"
  | Sorts.SProp -> str "SProp"
  | Sorts.Type u -> Universe.pr printer.pru u
  | Sorts.VSort _ | GSort _ -> Sorts.pr printer u
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
        str " because" ++ spc() ++ Universe.pr printer.pru pstart ++
        prlist (fun (r,v) -> spc() ++ pr_erel r ++ str" " ++ Universe.pr printer.pru v) p
  in
    str "Cannot enforce" ++ spc() ++ pr_uni u ++ spc() ++
      pr_rel o ++ spc() ++ pr_uni v ++ reason

module Internal = struct
  let add_template_qvars qvars g =
    assert (Sorts.QVar.Set.is_empty g.above_prop_qvars);
    {g with above_prop_qvars=qvars}

  let is_above_prop = is_above_prop
end
