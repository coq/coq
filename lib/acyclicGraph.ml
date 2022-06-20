(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type constraint_type = Lt | Le | Eq

module type Point = sig
  type t

  module Set : CSig.SetS with type elt = t
  module Map : CMap.ExtS with type key = t and module Set := Set

  val equal : t -> t -> bool
  val compare : t -> t -> int

  val pr : t -> Pp.t
end

module Make (Point:Point) = struct

  (* Created in Caml by Gérard Huet for CoC 4.8 [Dec 1988] *)
  (* Functional code by Jean-Christophe Filliâtre for Coq V7.0 [1999] *)
  (* Extension with algebraic universes by HH for Coq V7.0 [Sep 2001] *)
  (* Additional support for sort-polymorphic inductive types by HH [Mar 2006] *)
  (* Support for universe polymorphism by MS [2014] *)

  (* Revisions by Bruno Barras, Hugo Herbelin, Pierre Letouzey, Matthieu
     Sozeau, Pierre-Marie Pédrot, Jacques-Henri Jourdan *)

  (* Points are stratified by a partial ordering $\le$.
     Let $\~{}$ be the associated equivalence. We also have a strict ordering
     $<$ between equivalence classes, and we maintain that $<$ is acyclic,
     and contained in $\le$ in the sense that $[U]<[V]$ implies $U\le V$.

     At every moment, we have a finite number of points, and we
     maintain the ordering in the presence of assertions $U<V$ and $U\le V$.

     The equivalence $\~{}$ is represented by a tree structure, as in the
     union-find algorithm. The assertions $<$ and $\le$ are represented by
     adjacency lists.

     We use the algorithm described in the paper:

     Bender, M. A., Fineman, J. T., Gilbert, S., & Tarjan, R. E. (2011). A
     new approach to incremental cycle detection and related
     problems. arXiv preprint arXiv:1112.0784.

  *)

  module Index :
  sig
    type t
    val equal : t -> t -> bool
    module Set : CSig.SetS with type elt = t
    module Map : CMap.ExtS with type key = t and module Set := Set
    type table
    val empty : table
    val fresh : Point.t -> table -> t * table
    val mem : Point.t -> table -> bool
    val find : Point.t -> table -> t
    val repr : t -> table -> Point.t
    val hash : t -> int
  end =
  struct
    type t = int
    let equal = Int.equal
    module Set = Int.Set
    module Map = Int.Map

    type table = {
      tab_len : int;
      tab_fwd : Point.t Int.Map.t;
      tab_bwd : int Point.Map.t
    }

    let empty = {
      tab_len = 0;
      tab_fwd = Int.Map.empty;
      tab_bwd = Point.Map.empty;
    }
    let mem x t = Point.Map.mem x t.tab_bwd
    let find x t = Point.Map.find x t.tab_bwd
    let repr n t = Int.Map.find n t.tab_fwd

    let fresh x t =
      let () = assert (not @@ mem x t) in
      let n = t.tab_len in
      n, {
        tab_len = n + 1;
        tab_fwd = Int.Map.add n x t.tab_fwd;
        tab_bwd = Point.Map.add x n t.tab_bwd;
      }
    let hash x = x
  end

  module PMap = Index.Map
  module PSet = Index.Set

  (* Comparison on this type is pointer equality *)
  type canonical_node =
    { canon: Index.t;
      ltle: bool PMap.t;  (* true: strict (lt) constraint.
                             false: weak  (le) constraint. *)
      gtge: PSet.t;
      rank : int;
      klvl: int;
      ilvl: int;
    }

  (* A Point.t is either an alias for another one, or a canonical one,
     for which we know the points that are above *)

  type entry =
    | Canonical of canonical_node
    | Equiv of Index.t

  type t =
    { entries : entry PMap.t;
      index : int;
      n_nodes : int; n_edges : int;
      table : Index.table }

  module CN = struct
    type t = canonical_node
    let equal x y = x.canon == y.canon
    let hash x = Index.hash x.canon
  end

  module Status = struct
    module Internal = Hashtbl.Make(CN)

    (** we could experiment with creation size based on the size of [g] *)
    let create (g:t) = Internal.create 17

    let mem = Internal.mem
    let find = Internal.find
    let replace = Internal.replace
    let fold = Internal.fold
  end

  (* Every Point.t has a unique canonical arc representative *)

  (* Low-level function : makes u an alias for v.
     Does not removes edges from n_edges, but decrements n_nodes.
     u should be entered as canonical before.  *)
  let enter_equiv g u v =
    { entries =
        PMap.modify u (fun _ a ->
            match a with
            | Canonical n ->
              Equiv v
            | _ -> assert false) g.entries;
      index = g.index;
      n_nodes = g.n_nodes - 1;
      n_edges = g.n_edges;
      table = g.table }

  (* Low-level function : changes data associated with a canonical node.
     Resets the mutable fields in the old record, in order to avoid breaking
     invariants for other users of this record.
     n.canon should already been inserted as a canonical node. *)
  let change_node g n =
    { g with entries =
               PMap.modify n.canon
                 (fun _ a ->
                    match a with
                    | Canonical _ ->
                      Canonical n
                    | _ -> assert false)
                 g.entries }

  (* canonical representative : we follow the Equiv links *)
  let rec repr g u =
    match PMap.find u g.entries with
    | Equiv v -> repr g v
    | Canonical arc -> arc

  let repr_node g u =
    try repr g (Index.find u g.table)
    with Not_found ->
      CErrors.anomaly ~label:"Univ.repr"
        Pp.(str"Universe " ++ Point.pr u ++ str" undefined.")

  exception AlreadyDeclared

  (* Reindexes the given point, using the next available index. *)
  let use_index g u =
    let u = repr g u in
    let g = change_node g { u with ilvl = g.index } in
    assert (g.index > min_int);
    { g with index = g.index - 1 }

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
  let check_invariants ~required_canonical g =
    let required_canonical u = required_canonical (Index.repr u g.table) in
    let n_edges = ref 0 in
    let n_nodes = ref 0 in
    PMap.iter (fun l u ->
        match u with
        | Canonical u ->
          PMap.iter (fun v _strict ->
              incr n_edges;
              let v = repr g v in
              assert (topo_compare u v = -1);
              if u.klvl = v.klvl then
                assert (PSet.mem u.canon v.gtge ||
                        PSet.exists (fun l -> u == repr g l) v.gtge))
            u.ltle;
          PSet.iter (fun v ->
              let v = repr g v in
              assert (v.klvl = u.klvl &&
                      (PMap.mem u.canon v.ltle ||
                       PMap.exists (fun l _ -> u == repr g l) v.ltle))
            ) u.gtge;
          assert (Index.equal l u.canon);
          assert (u.ilvl > g.index);
          assert (not (PMap.mem u.canon u.ltle));
          incr n_nodes
        | Equiv _ -> assert (not (required_canonical l)))
      g.entries;
    assert (!n_edges = g.n_edges);
    assert (!n_nodes = g.n_nodes)

  let clean_ltle g ltle =
    PMap.fold (fun u strict acc ->
        let uu = (repr g u).canon in
        if Index.equal uu u then acc
        else (
          let acc = PMap.remove u (fst acc) in
          if not strict && PMap.mem uu acc then (acc, true)
          else (PMap.add uu strict acc, true)))
      ltle (ltle, false)

  let clean_gtge g gtge =
    PSet.fold (fun u acc ->
        let uu = (repr g u).canon in
        if Index.equal uu u then acc
        else PSet.add uu (PSet.remove u (fst acc)), true)
      gtge (gtge, false)

  (* [get_ltle] and [get_gtge] return ltle and gtge arcs.
     Moreover, if one of these lists is dirty (e.g. points to a
     non-canonical node), these functions clean this node in the
     graph by removing some duplicate edges *)
  let get_ltle g u =
    let ltle, chgt_ltle = clean_ltle g u.ltle in
    if not chgt_ltle then u.ltle, u, g
    else
      let sz = PMap.cardinal u.ltle in
      let sz2 = PMap.cardinal ltle in
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

  exception AbortBackward of t
  exception CycleDetected

  (* Implementation of the algorithm described in § 5.1 of the following paper:

     Bender, M. A., Fineman, J. T., Gilbert, S., & Tarjan, R. E. (2011). A
     new approach to incremental cycle detection and related
     problems. arXiv preprint arXiv:1112.0784.

     The "STEP X" comments contained in this file refers to the
     corresponding step numbers of the algorithm described in Section
     5.1 of this paper.  *)

  let rec backward_traverse status b_traversed count g x =
    let count = count - 1 in
    if count < 0 then begin
      raise_notrace (AbortBackward g)
    end;
    if Status.mem status x then b_traversed, count, g
    else begin
      Status.replace status x ();
      let gtge, x, g = get_gtge g x in
      let b_traversed, count, g =
        PSet.fold (fun y (b_traversed, count, g) ->
            let y = repr g y in
            backward_traverse status b_traversed count g y)
          gtge (b_traversed, count, g)
      in
      x.canon::b_traversed, count, g
    end

  let backward_traverse count g x = backward_traverse (Status.create g) [] count g x

  let rec forward_traverse f_traversed g v_klvl x y =
    let y = repr g y in
    if y.klvl < v_klvl then begin
      let y = { y with klvl = v_klvl;
                       gtge = if x == y then PSet.empty
                         else PSet.singleton x.canon }
      in
      let g = change_node g y in
      let ltle, y, g = get_ltle g y in
      let f_traversed, g =
        PMap.fold (fun z _ (f_traversed, g) ->
            forward_traverse f_traversed g v_klvl y z)
          ltle (f_traversed, g)
      in
      y.canon::f_traversed, g
    end else if y.klvl = v_klvl && x != y then
      let g = change_node g
          { y with gtge = PSet.add x.canon y.gtge } in
      f_traversed, g
    else f_traversed, g

  let rec find_to_merge status g x v =
    let x = repr g x in
    match Status.find status x with
    | merge -> merge
    | exception Not_found ->
      if Index.equal x.canon v then begin
        Status.replace status x true;
        true
      end
      else
        begin
          let merge = PSet.fold
              (fun y merge ->
                 let merge' = find_to_merge status g y v in
                 merge' || merge) x.gtge false
          in
          Status.replace status x merge;
          merge
        end

  let find_to_merge g x v =
    let status = Status.create g in
    status, find_to_merge status g x v

  let get_new_edges g to_merge =
    (* Computing edge sets. *)
    let ltle =
      let fold acc n =
        let fold u strict acc =
          match PMap.find u acc with
          | true -> acc
          | false -> if strict then PMap.add u true acc else acc
          | exception Not_found -> PMap.add u strict acc
        in
        PMap.fold fold n.ltle acc
      in
      match to_merge with
      | [] -> assert false
      | hd :: tl -> List.fold_left fold hd.ltle tl
    in
    let ltle, _ = clean_ltle g ltle in
    let fold accu a =
      match PMap.find a.canon ltle with
      | true ->
        (* There is a lt edge inside the new component. This is a
            "bad cycle". *)
        raise_notrace CycleDetected
      | false -> PMap.remove a.canon accu
      | exception Not_found -> accu
    in
    let ltle = List.fold_left fold ltle to_merge in
    let gtge =
      List.fold_left (fun acc n -> PSet.union acc n.gtge)
        PSet.empty to_merge
    in
    let gtge, _ = clean_gtge g gtge in
    let gtge = List.fold_left (fun acc n -> PSet.remove n.canon acc) gtge to_merge in
    (ltle, gtge)


  let reorder g u v =
    (* STEP 2: backward search in the k-level of u. *)

    (* [v_klvl] is the chosen future level for u, v and all
        traversed nodes. *)
    let b_traversed, v_klvl, g =
      let u = repr g u in
      try
        let b_traversed, _, g = backward_traverse (u.klvl + 1) g u in
        let v_klvl = u.klvl in
        b_traversed, v_klvl, g
      with AbortBackward g ->
        (* Backward search was too long, use the next k-level. *)
        let v_klvl = u.klvl + 1 in
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
          let status, merge = find_to_merge g u v in
          if merge then
            let not_merged u = try not (Status.find status (repr g u)) with Not_found -> true in
            Status.fold (fun u merged acc -> if merged then u::acc else acc) status [],
            List.filter not_merged b_traversed,
            List.filter not_merged f_traversed
          else [], b_traversed, f_traversed
        end
      else [], b_traversed, f_traversed
    in
    let to_reindex, g =
      match to_merge with
      | [] -> List.rev_append f_reindex b_reindex, g
      | n0::q0 ->
        (* Computing new root. *)
        let root, rank_rest =
          List.fold_left (fun ((best, _rank_rest) as acc) n ->
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
            if Index.equal n.canon root.canon then g else enter_equiv g n.canon root.canon)
            g to_merge
        in

        (* Updating g.n_edges *)
        let oldsz =
          List.fold_left (fun sz u -> sz+PMap.cardinal u.ltle)
            0 to_merge
        in
        let sz = PMap.cardinal ltle in
        let g = { g with n_edges = g.n_edges + sz - oldsz } in

        (* Not clear in the paper: we have to put the newly
            created component just between B and F. *)
        List.rev_append f_reindex (root.canon::b_reindex), g

    in

    (* STEP 5: reindex traversed nodes. *)
    List.fold_left use_index g to_reindex

  (* Assumes [u] and [v] are already in the graph. *)
  (* Does NOT assume that ucan != vcan. *)
  let insert_edge strict ucan vcan g =
    try
      let u = ucan.canon and v = vcan.canon in
      (* STEP 1: do we need to reorder nodes ? *)
      let g = if topo_compare ucan vcan <= 0 then g else reorder g u v in

      (* STEP 6: insert the new edge in the graph. *)
      let u = repr g u in
      let v = repr g v in
      if u == v then
        if strict then raise_notrace CycleDetected else g
      else
        let g =
          try let oldstrict = PMap.find v.canon u.ltle in
            if strict && not oldstrict then
              change_node g { u with ltle = PMap.add v.canon true u.ltle }
            else g
          with Not_found ->
            { (change_node g { u with ltle = PMap.add v.canon strict u.ltle })
              with n_edges = g.n_edges + 1 }
        in
        if u.klvl <> v.klvl || PSet.mem u.canon v.gtge then g
        else
          let v = { v with gtge = PSet.add u.canon v.gtge } in
          change_node g v
    with
    | CycleDetected as e -> raise_notrace e

  let add ?(rank=0) v g =
    if Index.mem v g.table then raise AlreadyDeclared
    else
      let () = assert (g.index > min_int) in
      let v, table = Index.fresh v g.table in
      let node = {
        canon = v;
        ltle = PMap.empty;
        gtge = PSet.empty;
        rank;
        klvl = 0;
        ilvl = g.index;
      }
      in
      let entries = PMap.add v (Canonical node) g.entries in
      { entries; index = g.index - 1; n_nodes = g.n_nodes + 1; n_edges = g.n_edges; table }

  exception Undeclared of Point.t
  let check_declared g us =
    let check l = if not (Index.mem l g.table) then raise (Undeclared l) in
    Point.Set.iter check us

  exception Found_explanation of (constraint_type * Point.t) list

  let get_explanation strict u v g =
    let u = Index.find u g.table in
    let v = repr_node g v in
    let visited_strict = ref PMap.empty in
    let rec traverse strict u =
      if u == v then
        if strict then None else Some []
      else if topo_compare u v = 1 then None
      else
        let visited =
          try not (PMap.find u.canon !visited_strict) || strict
          with Not_found -> false
        in
        if visited then None
        else begin
          visited_strict := PMap.add u.canon strict !visited_strict;
          try
            PMap.iter (fun u' strictu' ->
                match traverse (strict && not strictu') (repr g u') with
                | None -> ()
                | Some exp ->
                  let typ = if strictu' then Lt else Le in
                  let u' = Index.repr u' g.table in
                  raise_notrace (Found_explanation ((typ, u') :: exp)))
              u.ltle;
            None
          with Found_explanation exp -> Some exp
        end
    in
    let u = repr g u in
    if u == v then [(Eq, Index.repr v.canon g.table)]
    else match traverse strict u with Some exp -> exp | None -> assert false

  (* To compare two nodes, we simply do a forward search.
     We implement two improvements:
     - we ignore nodes that are higher than the destination;
     - we do a BFS rather than a DFS because we expect to have a short
         path (typically, the shortest path has length 1)
  *)
  exception Found
  type visited = WeakVisited | Visited
  let search_path strict u v g =
    let rec loop status todo next_todo =
      match todo, next_todo with
      | [], [] -> () (* No path found *)
      | [], _ -> loop status next_todo []
      | (u, strict)::todo, _ ->
        let is_visited = match Status.find status u with
          | Visited -> true
          | WeakVisited -> strict
          | exception Not_found -> false
        in
        if is_visited
        then loop status todo next_todo
        else begin
          Status.replace status u (if strict then WeakVisited else Visited);
          if try PMap.find v.canon u.ltle || not strict
            with Not_found -> false
          then raise_notrace Found
          else
            begin
              let next_todo =
                PMap.fold (fun u strictu next_todo ->
                    let strict = not strictu && strict in
                    let u = repr g u in
                    if u == v && not strict then raise_notrace Found
                    else if topo_compare u v = 1 then next_todo
                    else (u, strict)::next_todo)
                  u.ltle next_todo
              in
              loop status todo next_todo
            end
        end
    in
    if u == v then not strict
    else
      try loop (Status.create g) [u, strict] []; false
      with Found -> true

  (** Uncomment to debug the cycle detection algorithm. *)
  (*let insert_edge strict ucan vcan g =
    let check_invariants = check_invariants ~required_canonical:(fun _ -> false) in
    check_invariants g;
    let g = insert_edge strict ucan vcan g in
    check_invariants g;
    let ucan = repr g ucan.canon in
    let vcan = repr g vcan.canon in
    assert (search_path strict ucan vcan g);
    g*)

  (** User interface *)

  type 'a check_function = t -> 'a -> 'a -> bool

  let check_eq g u v =
    u == v ||
    let arcu = repr_node g u and arcv = repr_node g v in
    arcu == arcv

  let check_smaller g strict u v =
    search_path strict (repr_node g u) (repr_node g v) g

  let check_leq g u v = check_smaller g false u v
  let check_lt g u v = check_smaller g true u v

  let get_explanation (u, c, v) g = match c with
  | Eq ->
    (* Redo the search, not important because this is only used for display. *)
    if check_lt g u v then get_explanation true u v g else get_explanation true v u g
  | Le -> get_explanation true v u g
  | Lt -> get_explanation false v u g

  (* enforce_eq g u v will force u=v if possible, will fail otherwise *)

  let enforce_eq u v g =
    let ucan = repr_node g u in
    let vcan = repr_node g v in
    if ucan == vcan then Some g
    else if topo_compare ucan vcan = 1 then
      let ucan = vcan and vcan = ucan in
      let g = insert_edge false ucan vcan g in  (* Cannot fail *)
      try Some (insert_edge false vcan ucan g)
      with CycleDetected -> None
    else
      let g = insert_edge false ucan vcan g in  (* Cannot fail *)
      try Some (insert_edge false vcan ucan g)
      with CycleDetected -> None

  (* enforce_leq g u v will force u<=v if possible, will fail otherwise *)
  let enforce_leq u v g =
    let ucan = repr_node g u in
    let vcan = repr_node g v in
    try Some (insert_edge false ucan vcan g)
    with CycleDetected -> None

  (* enforce_lt u v will force u<v if possible, will fail otherwise *)
  let enforce_lt u v g =
    let ucan = repr_node g u in
    let vcan = repr_node g v in
    try Some (insert_edge true ucan vcan g)
    with CycleDetected -> None

  let empty =
    { entries = PMap.empty; index = 0; n_nodes = 0; n_edges = 0; table = Index.empty }

  (* Normalization *)

  type 'a constraint_fold = Point.t * constraint_type * Point.t -> 'a -> 'a

  let constraints_of g fold accu =
    let module UF = Unionfind.Make (Point.Set) (Point.Map) in
    let uf = UF.create () in
    let constraints_of u v acc =
      match v with
      | Canonical {canon=u; ltle; _} ->
        PMap.fold (fun v strict acc->
            let typ = if strict then Lt else Le in
            let u = Index.repr u g.table in
            let v = Index.repr v g.table in
            fold (u,typ,v) acc) ltle acc
      | Equiv v ->
        let u = Index.repr u g.table in
        let v = Index.repr v g.table in
        UF.union u v uf; acc
    in
    let csts = PMap.fold constraints_of g.entries accu in
    csts, UF.partition uf

  (* domain g.entries = kept + removed *)
  let constraints_for ~kept g fold accu =
    (* rmap: partial map from canonical points to kept points *)
    let add_cst u knd v cst =
      fold (Index.repr u g.table, knd, Index.repr v g.table) cst
    in
    let kept = Point.Set.fold (fun u accu -> PSet.add (Index.find u g.table) accu) kept PSet.empty in
    let rmap, csts = PSet.fold (fun u (rmap,csts) ->
        let arcu = repr g u in
        if PSet.mem arcu.canon kept then
          let csts = if Index.equal u arcu.canon then csts
            else add_cst u Eq arcu.canon csts
          in
          PMap.add arcu.canon arcu.canon rmap, csts
        else
          match PMap.find arcu.canon rmap with
          | v -> rmap, add_cst u Eq v csts
          | exception Not_found -> PMap.add arcu.canon u rmap, csts)
        kept (PMap.empty, accu)
    in
    let rec add_from u csts todo = match todo with
      | [] -> csts
      | (v,strict)::todo ->
        let v = repr g v in
        (match PMap.find v.canon rmap with
         | v ->
           let d = if strict then Lt else Le in
           let csts = add_cst u d v csts in
           add_from u csts todo
         | exception Not_found ->
           (* v is not equal to any kept point *)
           let todo = PMap.fold (fun v' strict' todo ->
               (v',strict || strict') :: todo)
               v.ltle todo
           in
           add_from u csts todo)
    in
    PSet.fold (fun u csts ->
        let arc = repr g u in
        PMap.fold (fun v strict csts -> add_from u csts [v,strict])
          arc.ltle csts)
      kept csts

  let domain g =
    let fold u _ accu = Point.Set.add (Index.repr u g.table) accu in
    PMap.fold fold g.entries Point.Set.empty

  let choose p g u =
    let exception Found of Point.t in
    let ru = (repr_node g u).canon in
    let ruv = Index.repr ru g.table in
    if p ruv then Some ruv
    else
      try PMap.iter (fun v -> function
          | Canonical _ -> () (* we already tried [p ru] *)
          | Equiv v' ->
            let rv = (repr g v').canon in
            if rv == ru then
              let v = Index.repr v g.table in
              if p v then raise_notrace (Found v)
            (* NB: we could also try [p v'] but it will come up in the
               rest of the iteration regardless. *)
        ) g.entries; None
      with Found v -> Some v

  type node = Alias of Point.t | Node of bool Point.Map.t
  type repr = node Point.Map.t

  let repr g =
    let fold u n accu =
      let n = match n with
      | Canonical n ->
        let fold u lt accu = Point.Map.add (Index.repr u g.table) lt accu in
        let ltle = PMap.fold fold n.ltle Point.Map.empty in
        Node ltle
      | Equiv u -> Alias (Index.repr u g.table)
      in
      Point.Map.add (Index.repr u g.table) n accu
    in
    PMap.fold fold g.entries Point.Map.empty

end
