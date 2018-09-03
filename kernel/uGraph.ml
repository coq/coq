(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open Univ

(* Created in Caml by Gérard Huet for CoC 4.8 [Dec 1988] *)
(* Functional code by Jean-Christophe Filliâtre for Coq V7.0 [1999] *)
(* Extension with algebraic universes by HH for Coq V7.0 [Sep 2001] *)
(* Additional support for sort-polymorphic inductive types by HH [Mar 2006] *)
(* Support for universe polymorphism by MS [2014] *)

(* Revisions by Bruno Barras, Hugo Herbelin, Pierre Letouzey, Matthieu
   Sozeau, Pierre-Marie Pédrot, Jacques-Henri Jourdan *)

let error_inconsistency o u v p =
  raise (UniverseInconsistency (o,Universe.make u,Universe.make v,p))

(* Universes are stratified by a partial ordering $\le$.
   Let $\~{}$ be the associated equivalence. We also have a strict ordering
   $<$ between equivalence classes, and we maintain that $<$ is acyclic,
   and contained in $\le$ in the sense that $[U]<[V]$ implies $U\le V$.

   At every moment, we have a finite number of universes, and we
   maintain the ordering in the presence of assertions $U<V$ and $U\le V$.

   The equivalence $\~{}$ is represented by a tree structure, as in the
   union-find algorithm. The assertions $<$ and $\le$ are represented by
   adjacency lists.

   We use the algorithm described in the paper:

   Bender, M. A., Fineman, J. T., Gilbert, S., & Tarjan, R. E. (2011). A
   new approach to incremental cycle detection and related
   problems. arXiv preprint arXiv:1112.0784.

 *)

open Universe

module UMap = LMap

type status = NoMark | Visited | WeakVisited | ToMerge

(* Comparison on this type is pointer equality *)
type canonical_node =
    { univ: Level.t;
      ltle: bool UMap.t;  (* true: strict (lt) constraint.
                             false: weak  (le) constraint. *)
      gtge: LSet.t;
      rank : int;
      klvl: int;
      ilvl: int;
      mutable status: status
    }

let big_rank = 1000000

(* A Level.t is either an alias for another one, or a canonical one,
   for which we know the universes that are above *)

type univ_entry =
    Canonical of canonical_node
  | Equiv of Level.t

type universes =
  { entries : univ_entry UMap.t;
    index : int;
    n_nodes : int; n_edges : int }

type t = universes

(** Used to cleanup universes if a traversal function is interrupted before it
    has the opportunity to do it itself. *)
let unsafe_cleanup_universes g =
  let iter _ n = match n with
  | Equiv _ -> ()
  | Canonical n -> n.status <- NoMark
  in
  UMap.iter iter g.entries

let rec cleanup_universes g =
  try unsafe_cleanup_universes g
  with e ->
    (** The only way unsafe_cleanup_universes may raise an exception is when
        a serious error (stack overflow, out of memory) occurs, or a signal is
        sent. In this unlikely event, we relaunch the cleanup until we finally
        succeed. *)
    cleanup_universes g; raise e

(* Every Level.t has a unique canonical arc representative *)

(* Low-level function : makes u an alias for v.
   Does not removes edges from n_edges, but decrements n_nodes.
   u should be entered as canonical before.  *)
let enter_equiv g u v =
  { entries =
      UMap.modify u (fun _ a ->
        match a with
        | Canonical n ->
          n.status <- NoMark;
          Equiv v
        | _ -> assert false) g.entries;
    index = g.index;
    n_nodes = g.n_nodes - 1;
    n_edges = g.n_edges }

(* Low-level function : changes data associated with a canonical node.
   Resets the mutable fields in the old record, in order to avoid breaking
   invariants for other users of this record.
   n.univ should already been inserted as a canonical node. *)
let change_node g n =
  { g with entries =
      UMap.modify n.univ
        (fun _ a ->
          match a with
          | Canonical n' ->
            n'.status <- NoMark;
            Canonical n
          | _ -> assert false)
        g.entries }

(* repr : universes -> Level.t -> canonical_node *)
(* canonical representative : we follow the Equiv links *)
let rec repr g u =
  let a =
    try UMap.find u g.entries
    with Not_found -> CErrors.anomaly ~label:"Univ.repr"
        (str"Universe " ++ Level.pr u ++ str" undefined.")
  in
  match a with
    | Equiv v -> repr g v
    | Canonical arc -> arc

let get_set_arc g = repr g Level.set
let is_set_arc u = Level.is_set u.univ
let is_prop_arc u = Level.is_prop u.univ

exception AlreadyDeclared

(* Reindexes the given universe, using the next available index. *)
let use_index g u =
  let u = repr g u in
  let g = change_node g { u with ilvl = g.index } in
  assert (g.index > min_int);
  { g with index = g.index - 1 }

(* [safe_repr] is like [repr] but if the graph doesn't contain the
   searched universe, we add it. *)
let safe_repr g u =
  let rec safe_repr_rec entries u =
    match UMap.find u entries with
    | Equiv v -> safe_repr_rec entries v
    | Canonical arc -> arc
  in
  try g, safe_repr_rec g.entries u
  with Not_found ->
    let can =
      { univ = u;
        ltle = UMap.empty; gtge = LSet.empty;
        rank = if Level.is_small u then big_rank else 0;
        klvl = 0; ilvl = 0;
        status = NoMark }
    in
    let g = { g with
      entries = UMap.add u (Canonical can) g.entries;
      n_nodes = g.n_nodes + 1 }
    in
    let g = use_index g u in
    g, repr g u

(* Returns 1 if u is higher than v in topological order.
           -1        lower
           0 if u = v *)
let topo_compare u v =
  if u.klvl > v.klvl then 1
  else if u.klvl < v.klvl then -1
  else if u.ilvl > v.ilvl then 1
  else if u.ilvl < v.ilvl then -1
  else (assert (u==v); 0)

(* Checks most of the invariants of the graph. For debugging purposes. *)
let check_universes_invariants g =
  let n_edges = ref 0 in
  let n_nodes = ref 0 in
  UMap.iter (fun l u ->
    match u with
    | Canonical u ->
      UMap.iter (fun v strict ->
          incr n_edges;
          let v = repr g v in
          assert (topo_compare u v = -1);
          if u.klvl = v.klvl then
            assert (LSet.mem u.univ v.gtge ||
                    LSet.exists (fun l -> u == repr g l) v.gtge))
        u.ltle;
      LSet.iter (fun v ->
        let v = repr g v in
        assert (v.klvl = u.klvl &&
            (UMap.mem u.univ v.ltle ||
             UMap.exists (fun l _ -> u == repr g l) v.ltle))
      ) u.gtge;
      assert (u.status = NoMark);
      assert (Level.equal l u.univ);
      assert (u.ilvl > g.index);
      assert (not (UMap.mem u.univ u.ltle));
      incr n_nodes
    | Equiv _ -> assert (not (Level.is_small l)))
    g.entries;
  assert (!n_edges = g.n_edges);
  assert (!n_nodes = g.n_nodes)

let clean_ltle g ltle =
  UMap.fold (fun u strict acc ->
      let uu = (repr g u).univ in
      if Level.equal uu u then acc
      else (
        let acc = UMap.remove u (fst acc) in
        if not strict && UMap.mem uu acc then (acc, true)
        else (UMap.add uu strict acc, true)))
    ltle (ltle, false)

let clean_gtge g gtge =
  LSet.fold (fun u acc ->
      let uu = (repr g u).univ in
      if Level.equal uu u then acc
      else LSet.add uu (LSet.remove u (fst acc)), true)
    gtge (gtge, false)

(* [get_ltle] and [get_gtge] return ltle and gtge arcs.
   Moreover, if one of these lists is dirty (e.g. points to a
   non-canonical node), these functions clean this node in the
   graph by removing some duplicate edges *)
let get_ltle g u =
  let ltle, chgt_ltle = clean_ltle g u.ltle in
  if not chgt_ltle then u.ltle, u, g
  else
    let sz = UMap.cardinal u.ltle in
    let sz2 = UMap.cardinal ltle in
    let u = { u with ltle } in
    let g = change_node g u in
    let g = { g with n_edges = g.n_edges + sz2 - sz } in
    u.ltle, u, g

let get_gtge g u =
  let gtge, chgt_gtge = clean_gtge g u.gtge in
  if not chgt_gtge then u.gtge, u, g
  else
    let u = { u with gtge } in
    let g = change_node g u in
    u.gtge, u, g

(* [revert_graph] rollbacks the changes made to mutable fields in
   nodes in the graph.
   [to_revert] contains the touched nodes. *)
let revert_graph to_revert g =
  List.iter (fun t ->
    match UMap.find t g.entries with
    | Equiv _ -> ()
    | Canonical t ->
      t.status <- NoMark) to_revert

exception AbortBackward of universes
exception CycleDetected

(* Implementation of the algorithm described in § 5.1 of the following paper:

   Bender, M. A., Fineman, J. T., Gilbert, S., & Tarjan, R. E. (2011). A
   new approach to incremental cycle detection and related
   problems. arXiv preprint arXiv:1112.0784.

   The "STEP X" comments contained in this file refers to the
   corresponding step numbers of the algorithm described in Section
   5.1 of this paper.  *)

(* [delta] is the timeout for backward search. It might be
    useful to tune a multiplicative constant. *)
let get_delta g =
  int_of_float
    (min (float_of_int g.n_edges ** 0.5)
        (float_of_int g.n_nodes ** (2./.3.)))

let rec backward_traverse to_revert b_traversed count g x =
  let x = repr g x in
  let count = count - 1 in
  if count < 0 then begin
    revert_graph to_revert g;
    raise (AbortBackward g)
  end;
  if x.status = NoMark then begin
    x.status <- Visited;
    let to_revert = x.univ::to_revert in
    let gtge, x, g = get_gtge g x in
    let to_revert, b_traversed, count, g =
      LSet.fold (fun y (to_revert, b_traversed, count, g) ->
        backward_traverse to_revert b_traversed count g y)
        gtge (to_revert, b_traversed, count, g)
    in
    to_revert, x.univ::b_traversed, count, g
  end
  else to_revert, b_traversed, count, g

let rec forward_traverse f_traversed g v_klvl x y =
  let y = repr g y in
  if y.klvl < v_klvl then begin
    let y = { y with klvl = v_klvl;
                      gtge = if x == y then LSet.empty
                            else LSet.singleton x.univ }
    in
    let g = change_node g y in
    let ltle, y, g = get_ltle g y in
    let f_traversed, g =
      UMap.fold (fun z _ (f_traversed, g) ->
        forward_traverse f_traversed g v_klvl y z)
      ltle (f_traversed, g)
    in
    y.univ::f_traversed, g
    end else if y.klvl = v_klvl && x != y then
      let g = change_node g
        { y with gtge = LSet.add x.univ y.gtge } in
      f_traversed, g
    else f_traversed, g

let rec find_to_merge to_revert g x v =
  let x = repr g x in
  match x.status with
  | Visited -> false, to_revert   | ToMerge -> true, to_revert
  | NoMark ->
    let to_revert = x::to_revert in
    if Level.equal x.univ v then
      begin x.status <- ToMerge; true, to_revert end
    else
      begin
        let merge, to_revert = LSet.fold
          (fun y (merge, to_revert) ->
            let merge', to_revert = find_to_merge to_revert g y v in
            merge' || merge, to_revert) x.gtge (false, to_revert)
        in
        x.status <- if merge then ToMerge else Visited;
        merge, to_revert
      end
  | _ -> assert false

let get_new_edges g to_merge =
  (* Computing edge sets. *)
  let to_merge_lvl =
    List.fold_left (fun acc u -> UMap.add u.univ u acc)
      UMap.empty to_merge
  in
  let ltle =
    let fold _ n acc =
      let fold u strict acc =
        if strict then UMap.add u strict acc
        else if UMap.mem u acc then acc
        else UMap.add u false acc
      in
      UMap.fold fold n.ltle acc
    in
    UMap.fold fold to_merge_lvl UMap.empty
  in
  let ltle, _ = clean_ltle g ltle in
  let ltle =
    UMap.merge (fun _ a strict ->
      match a, strict with
      | Some _, Some true ->
        (* There is a lt edge inside the new component. This is a
            "bad cycle". *)
        raise CycleDetected
      | Some _, Some false -> None
      | _, _ -> strict
    ) to_merge_lvl ltle
  in
  let gtge =
    UMap.fold (fun _ n acc -> LSet.union acc n.gtge)
      to_merge_lvl LSet.empty
  in
  let gtge, _ = clean_gtge g gtge in
  let gtge = LSet.diff gtge (UMap.domain to_merge_lvl) in
  (ltle, gtge)


let reorder g u v =
  (* STEP 2: backward search in the k-level of u. *)
  let delta = get_delta g in

  (* [v_klvl] is the chosen future level for u, v and all
      traversed nodes. *)
  let b_traversed, v_klvl, g =
    try
      let to_revert, b_traversed, _, g = backward_traverse [] [] delta g u in
      revert_graph to_revert g;
      let v_klvl = (repr g u).klvl in
      b_traversed, v_klvl, g
    with AbortBackward g ->
      (* Backward search was too long, use the next k-level. *)
      let v_klvl = (repr g u).klvl + 1 in
      [], v_klvl, g
  in
  let f_traversed, g =
    (* STEP 3: forward search. Contrary to what is described in
        the paper, we do not test whether v_klvl = u.klvl nor we assign
        v_klvl to v.klvl. Indeed, the first call to forward_traverse
        will do all that. *)
    forward_traverse [] g v_klvl (repr g v) v
  in

  (* STEP 4: merge nodes if needed. *)
  let to_merge, b_reindex, f_reindex =
    if (repr g u).klvl = v_klvl then
      begin
        let merge, to_revert = find_to_merge [] g u v in
        let r =
          if merge then
            List.filter (fun u -> u.status = ToMerge) to_revert,
            List.filter (fun u -> (repr g u).status <> ToMerge) b_traversed,
            List.filter (fun u -> (repr g u).status <> ToMerge) f_traversed
          else [], b_traversed, f_traversed
        in
        List.iter (fun u -> u.status <- NoMark) to_revert;
        r
      end
    else [], b_traversed, f_traversed
  in
  let to_reindex, g =
    match to_merge with
    | [] -> List.rev_append f_reindex b_reindex, g
    | n0::q0 ->
      (* Computing new root. *)
      let root, rank_rest =
        List.fold_left (fun ((best, rank_rest) as acc) n ->
          if n.rank >= best.rank then n, best.rank else acc)
          (n0, min_int) q0
      in
      let ltle, gtge = get_new_edges g to_merge in
      (* Inserting the new root. *)
      let g = change_node g
        { root with ltle; gtge;
          rank = max root.rank (rank_rest + 1); }
      in

      (* Inserting shortcuts for old nodes. *)
      let g = List.fold_left (fun g n ->
        if Level.equal n.univ root.univ then g else enter_equiv g n.univ root.univ)
        g to_merge
      in

      (* Updating g.n_edges *)
      let oldsz =
        List.fold_left (fun sz u -> sz+UMap.cardinal u.ltle)
          0 to_merge
      in
      let sz = UMap.cardinal ltle in
      let g = { g with n_edges = g.n_edges + sz - oldsz } in

      (* Not clear in the paper: we have to put the newly
          created component just between B and F. *)
      List.rev_append f_reindex (root.univ::b_reindex), g

  in

  (* STEP 5: reindex traversed nodes. *)
  List.fold_left use_index g to_reindex

(* Assumes [u] and [v] are already in the graph. *)
(* Does NOT assume that ucan != vcan. *)
let insert_edge strict ucan vcan g =
  try
    let u = ucan.univ and v = vcan.univ in
    (* STEP 1: do we need to reorder nodes ? *)
    let g = if topo_compare ucan vcan <= 0 then g else reorder g u v in

    (* STEP 6: insert the new edge in the graph. *)
    let u = repr g u in
    let v = repr g v in
    if u == v then
      if strict then raise CycleDetected else g
    else
      let g =
        try let oldstrict = UMap.find v.univ u.ltle in
            if strict && not oldstrict then
              change_node g { u with ltle = UMap.add v.univ true u.ltle }
            else g
        with Not_found ->
          { (change_node g { u with ltle = UMap.add v.univ strict u.ltle })
            with n_edges = g.n_edges + 1 }
      in
      if u.klvl <> v.klvl || LSet.mem u.univ v.gtge then g
      else
        let v = { v with gtge = LSet.add u.univ v.gtge } in
        change_node g v
  with
  | CycleDetected as e -> raise e
  | e ->
    (** Unlikely event: fatal error or signal *)
    let () = cleanup_universes g in
    raise e

let add_universe_gen vlev g =
  try
    let _arcv = UMap.find vlev g.entries in
      raise AlreadyDeclared
  with Not_found ->
    assert (g.index > min_int);
    let v = {
      univ = vlev;
      ltle = LMap.empty;
      gtge = LSet.empty;
      rank = 0;
      klvl = 0;
      ilvl = g.index;
      status = NoMark;
    }
    in
    let entries = UMap.add vlev (Canonical v) g.entries in
    { entries; index = g.index - 1; n_nodes = g.n_nodes + 1; n_edges = g.n_edges }, v

let add_universe vlev strict g =
  let g, v = add_universe_gen vlev g in
  insert_edge strict (get_set_arc g) v g

let add_universe_unconstrained vlev g =
  fst (add_universe_gen vlev g)

exception UndeclaredLevel of Univ.Level.t
let check_declared_universes g us =
  let check l = if not (UMap.mem l g.entries) then raise (UndeclaredLevel l) in
  Univ.LSet.iter check us

exception Found_explanation of explanation

let get_explanation strict u v g =
  let v = repr g v in
  let visited_strict = ref UMap.empty in
  let rec traverse strict u =
    if u == v then
      if strict then None else Some []
    else if topo_compare u v = 1 then None
    else
      let visited =
        try not (UMap.find u.univ !visited_strict) || strict
        with Not_found -> false
      in
      if visited then None
      else begin
        visited_strict := UMap.add u.univ strict !visited_strict;
        try
          UMap.iter (fun u' strictu' ->
            match traverse (strict && not strictu') (repr g u') with
            | None -> ()
            | Some exp ->
              let typ = if strictu' then Lt else Le in
              raise (Found_explanation ((typ, make u') :: exp)))
            u.ltle;
          None
        with Found_explanation exp -> Some exp
      end
  in
  let u = repr g u in
  if u == v then [(Eq, make v.univ)]
  else match traverse strict u with Some exp -> exp | None -> assert false

let get_explanation strict u v g =
  Some (lazy (get_explanation strict u v g))

(* To compare two nodes, we simply do a forward search.
   We implement two improvements:
   - we ignore nodes that are higher than the destination;
   - we do a BFS rather than a DFS because we expect to have a short
       path (typically, the shortest path has length 1)
*)
exception Found of canonical_node list
let search_path strict u v g =
  let rec loop to_revert todo next_todo =
    match todo, next_todo with
    | [], [] -> to_revert (* No path found *)
    | [], _ -> loop to_revert next_todo []
    | (u, strict)::todo, _ ->
      if u.status = Visited || (u.status = WeakVisited && strict)
      then loop to_revert todo next_todo
      else
        let to_revert =
          if u.status = NoMark then u::to_revert else to_revert
        in
        u.status <- if strict then WeakVisited else Visited;
        if try UMap.find v.univ u.ltle || not strict
           with Not_found -> false
        then raise (Found to_revert)
        else
          begin
            let next_todo =
              UMap.fold (fun u strictu next_todo ->
                let strict = not strictu && strict in
                let u = repr g u in
                if u == v && not strict then raise (Found to_revert)
                else if topo_compare u v = 1 then next_todo
                else (u, strict)::next_todo)
               u.ltle next_todo
            in
            loop to_revert todo next_todo
          end
  in
  if u == v then not strict
  else
    try
      let res, to_revert =
        try false, loop [] [u, strict] []
        with Found to_revert -> true, to_revert
      in
      List.iter (fun u -> u.status <- NoMark) to_revert;
      res
    with e ->
      (** Unlikely event: fatal error or signal *)
      let () = cleanup_universes g in
      raise e

(** Uncomment to debug the cycle detection algorithm. *)
(*let insert_edge strict ucan vcan g =
  check_universes_invariants g;
  let g = insert_edge strict ucan vcan g in
  check_universes_invariants g;
  let ucan = repr g ucan.univ in
  let vcan = repr g vcan.univ in
  assert (search_path strict ucan vcan g);
  g*)

(** First, checks on universe levels *)

let check_equal g u v =
  let arcu = repr g u and arcv = repr g v in
    arcu == arcv

let check_eq_level g u v = u == v || check_equal g u v

let check_smaller g strict u v =
  let arcu = repr g u and arcv = repr g v in
  if strict then
    search_path true arcu arcv g
  else
    is_prop_arc arcu 
    || (is_set_arc arcu && not (is_prop_arc arcv))
    || search_path false arcu arcv g

(** Then, checks on universes *)

type 'a check_function = universes -> 'a -> 'a -> bool

let check_smaller_expr g (u,n) (v,m) =
  let diff = n - m in
    match diff with
    | 0 -> check_smaller g false u v
    | 1 -> check_smaller g true u v
    | x when x < 0 -> check_smaller g false u v
    | _ -> false

let exists_bigger g ul l =
  Universe.exists (fun ul' -> 
    check_smaller_expr g ul ul') l

let real_check_leq g u v =
  Universe.for_all (fun ul -> exists_bigger g ul v) u
    
let check_leq g u v =
  Universe.equal u v ||
    is_type0m_univ u ||
    real_check_leq g u v

let check_eq_univs g l1 l2 =
  real_check_leq g l1 l2 && real_check_leq g l2 l1

let check_eq g u v =
  Universe.equal u v || check_eq_univs g u v

(* enforce_univ_eq g u v will force u=v if possible, will fail otherwise *)

let rec enforce_univ_eq u v g =
  let ucan = repr g u in
  let vcan = repr g v in
  if topo_compare ucan vcan = 1 then enforce_univ_eq v u g
  else
    let g = insert_edge false ucan vcan g in  (* Cannot fail *)
    try insert_edge false vcan ucan g
    with CycleDetected ->
      error_inconsistency Eq v u (get_explanation true u v g)

(* enforce_univ_leq g u v will force u<=v if possible, will fail otherwise *)
let enforce_univ_leq u v g =
  let ucan = repr g u in
  let vcan = repr g v in
  try insert_edge false ucan vcan g
  with CycleDetected ->
    error_inconsistency Le u v (get_explanation true v u g)

(* enforce_univ_lt u v will force u<v if possible, will fail otherwise *)
let enforce_univ_lt u v g =
  let ucan = repr g u in
  let vcan = repr g v in
  try insert_edge true ucan vcan g
  with CycleDetected ->
    error_inconsistency Lt u v (get_explanation false v u g)

let empty_universes =
  { entries = UMap.empty; index = 0; n_nodes = 0; n_edges = 0 }

let initial_universes =
  let set_arc = Canonical {
    univ = Level.set;
    ltle = LMap.empty;
    gtge = LSet.empty;
    rank = big_rank;
    klvl = 0;
    ilvl = (-1);
    status = NoMark;
  } in
  let prop_arc = Canonical {
    univ = Level.prop;
    ltle = LMap.empty;
    gtge = LSet.empty;
    rank = big_rank;
    klvl = 0;
    ilvl = 0;
    status = NoMark;
  } in
  let entries = UMap.add Level.set set_arc (UMap.singleton Level.prop prop_arc) in
  let empty = { entries; index = (-2); n_nodes = 2; n_edges = 0 } in
  enforce_univ_lt Level.prop Level.set empty

let is_initial_universes g = UMap.equal (==) g.entries initial_universes.entries

let enforce_constraint cst g =
  match cst with
    | (u,Lt,v) -> enforce_univ_lt u v g
    | (u,Le,v) -> enforce_univ_leq u v g
    | (u,Eq,v) -> enforce_univ_eq u v g

let merge_constraints c g =
  Constraint.fold enforce_constraint c g

let check_constraint g (l,d,r) =
  match d with
  | Eq -> check_equal g l r
  | Le -> check_smaller g false l r
  | Lt -> check_smaller g true l r

let check_constraints c g =
  Constraint.for_all (check_constraint g) c

let leq_expr (u,m) (v,n) =
  let d = match m - n with
    | 1 -> Lt
    | diff -> assert (diff <= 0); Le
  in
  (u,d,v)

let enforce_leq_alg u v g =
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

(* Normalization *)

(** [normalize_universes g] returns a graph where all edges point
    directly to the canonical representent of their target. The output
    graph should be equivalent to the input graph from a logical point
    of view, but optimized. We maintain the invariant that the key of
    a [Canonical] element is its own name, by keeping [Equiv] edges. *)
let normalize_universes g =
  let g =
    { g with
      entries = UMap.map (fun entry ->
        match entry with
        | Equiv u -> Equiv ((repr g u).univ)
        | Canonical ucan -> Canonical { ucan with rank = 1 })
        g.entries }
  in
  UMap.fold (fun _ u g ->
    match u with
    | Equiv u -> g
    | Canonical u ->
      let _, u, g = get_ltle g u in
      let _, _, g = get_gtge g u in
      g)
    g.entries g

let constraints_of_universes g =
  let module UF = Unionfind.Make (LSet) (LMap) in
  let uf = UF.create () in
  let constraints_of u v acc =
    match v with
    | Canonical {univ=u; ltle} ->
      UMap.fold (fun v strict acc->
        let typ = if strict then Lt else Le in
        Constraint.add (u,typ,v) acc) ltle acc
    | Equiv v -> UF.union u v uf; acc
  in
  let csts = UMap.fold constraints_of g.entries Constraint.empty in
  csts, UF.partition uf

(* domain g.entries = kept + removed *)
let constraints_for ~kept g =
  (* rmap: partial map from canonical universes to kept universes *)
  let rmap, csts = LSet.fold (fun u (rmap,csts) ->
      let arcu = repr g u in
      if LSet.mem arcu.univ kept then
        LMap.add arcu.univ arcu.univ rmap, enforce_eq_level u arcu.univ csts
      else
        match LMap.find arcu.univ rmap with
        | v -> rmap, enforce_eq_level u v csts
        | exception Not_found -> LMap.add arcu.univ u rmap, csts)
      kept (LMap.empty,Constraint.empty)
  in
  let rec add_from u csts todo = match todo with
    | [] -> csts
    | (v,strict)::todo ->
      let v = repr g v in
      (match LMap.find v.univ rmap with
       | v ->
         let d = if strict then Lt else Le in
         let csts = Constraint.add (u,d,v) csts in
         add_from u csts todo
       | exception Not_found ->
         (* v is not equal to any kept universe *)
         let todo = LMap.fold (fun v' strict' todo ->
             (v',strict || strict') :: todo)
             v.ltle todo
         in
         add_from u csts todo)
  in
  LSet.fold (fun u csts ->
      let arc = repr g u in
      LMap.fold (fun v strict csts -> add_from u csts [v,strict])
        arc.ltle csts)
    kept csts

(** [sort_universes g] builds a totally ordered universe graph.  The
    output graph should imply the input graph (and the implication
    will be strict most of the time), but is not necessarily minimal.
    Moreover, it adds levels [Type.n] to identify universes at level
    n. An artificial constraint Set < Type.2 is added to ensure that
    Type.n and small universes are not merged. Note: the result is
    unspecified if the input graph already contains [Type.n] nodes
    (calling a module Type is probably a bad idea anyway). *)
let sort_universes g =
  let cans =
    UMap.fold (fun _ u l ->
      match u with
      | Equiv _ -> l
      | Canonical can -> can :: l
    ) g.entries []
  in
  let cans = List.sort topo_compare cans in
  let lowest_levels =
    UMap.mapi (fun u _ -> if Level.is_small u then 0 else 2)
      (UMap.filter
         (fun _ u -> match u with Equiv _ -> false | Canonical _ -> true)
         g.entries)
  in
  let lowest_levels =
    List.fold_left (fun lowest_levels can ->
      let lvl = UMap.find can.univ lowest_levels in
      UMap.fold (fun u' strict lowest_levels ->
        let cost = if strict then 1 else 0 in
        let u' = (repr g u').univ in
        UMap.modify u' (fun _ lvl0 -> max lvl0 (lvl+cost)) lowest_levels)
       can.ltle lowest_levels)
     lowest_levels cans
  in
  let max_lvl = UMap.fold (fun _ a b -> max a b) lowest_levels 0 in
  let mp = Names.DirPath.make [Names.Id.of_string "Type"] in
  let types = Array.init (max_lvl + 1) (function
    | 0 -> Level.prop
    | 1 -> Level.set
    | n -> Level.make mp (n-2))
  in
  let g = Array.fold_left (fun g u ->
    let g, u = safe_repr g u in
    change_node g { u with rank = big_rank }) g types
  in
  let g = if max_lvl >= 2 then enforce_univ_lt Level.set types.(2) g else g in
  let g =
    UMap.fold (fun u lvl g -> enforce_univ_eq u (types.(lvl)) g)
      lowest_levels g
  in
  normalize_universes g

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

(** Pretty-printing *)

let pr_arc prl = function
  | _, Canonical {univ=u; ltle} ->
    if UMap.is_empty ltle then mt ()
    else
      prl u ++ str " " ++
      v 0
        (pr_sequence (fun (v, strict) ->
          (if strict then str "< " else str "<= ") ++ prl v)
           (UMap.bindings ltle)) ++
      fnl ()
  | u, Equiv v ->
      prl u  ++ str " = " ++ prl v ++ fnl ()

let pr_universes prl g =
  let graph = UMap.fold (fun u a l -> (u,a)::l) g.entries [] in
  prlist (pr_arc prl) graph

(* Dumping constraints to a file *)

let dump_universes output g =
  let dump_arc u = function
    | Canonical {univ=u; ltle} ->
        let u_str = Level.to_string u in
        UMap.iter (fun v strict ->
          let typ = if strict then Lt else Le in
          output typ u_str (Level.to_string v)) ltle;
    | Equiv v ->
      output Eq (Level.to_string u) (Level.to_string v)
  in
  UMap.iter dump_arc g.entries

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

