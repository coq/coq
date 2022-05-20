type constraint_type = Lt | Le | Eq

let debug_loop_checking_invariants, debug_invariants = CDebug.create_full ~name:"loop-checking-invariants" ()
let _debug_loop_checking_model, debug_model = CDebug.create_full ~name:"loop-checking-model" ()
let _debug_loop_checking_clauses, _debug_clauses = CDebug.create_full ~name:"loop-checking-clauses" ()
(* let _debug_loop_checking_bwdclauses, debug_bwdclauses = CDebug.create_full ~name:"loop-checking-bwdclauses" () *)
let _debug_loop_checking_flag, debug = CDebug.create_full ~name:"loop-checking" ()
let debug_loop_checking_timing_flag, debug_timing = CDebug.create_full ~name:"loop-checking-timing" ()
let _debug_loop_checking_loop, debug_loop = CDebug.create_full ~name:"loop-checking-loop" ()
let _debug_loop_checking_check_model, debug_check_model = CDebug.create_full ~name:"loop-checking-check-model" ()

module type Point = sig
  type t

  module Set : CSig.SetS with type elt = t
  module Map : CMap.ExtS with type key = t and module Set := Set

  val equal : t -> t -> bool
  val compare : t -> t -> int

  val keep_canonical : t -> bool
  val pr : t -> Pp.t
end

let _time prefix =
  let accum = ref 0. in
  fun f x ->
  if CDebug.(get_flag debug_loop_checking_timing_flag) then
    let start = Unix.gettimeofday () in
    let res = f x in
    let stop = Unix.gettimeofday () in
    let time = stop -. start in
    let () = accum := time +. !accum in
    let () = debug_timing Pp.(fun () -> prefix ++ str " executed in: " ++ Pp.real time ++ str "s") in
    let () = debug_timing Pp.(fun () -> prefix ++ str " total execution time is: " ++ Pp.real !accum ++ str "s") in
    res
  else f x

let time2 prefix f =
  let accum = ref 0. in
  let calls = ref 0 in
  fun x y ->
  if CDebug.(get_flag debug_loop_checking_timing_flag) then
    let start = Unix.gettimeofday () in
    let res = f x y in
    let stop = Unix.gettimeofday () in
    let time = stop -. start in
    let () = accum := time +. !accum in
    incr calls;
    let () = debug_timing Pp.(fun () -> prefix ++ str " executed in: " ++ Pp.real time ++ str "s") in
    let () = debug_timing Pp.(fun () -> prefix ++ str " total execution time is: " ++ Pp.real !accum ++ str "s" ++
      str " in " ++ int !calls ++ str " calls") in
    res
  else f x y

let time3 prefix f =
  let accum = ref 0. in
  fun x y z ->
  if CDebug.(get_flag debug_loop_checking_timing_flag) then
    let start = Unix.gettimeofday () in
    let res = f x y z in
    let stop = Unix.gettimeofday () in
    let time = stop -. start in
    let () = accum := time +. !accum in
    let () = debug_timing Pp.(fun () -> prefix ++ str " executed in: " ++ Pp.real time ++ str "s") in
    let () = debug_timing Pp.(fun () -> prefix ++ str " total execution time is: " ++ Pp.real !accum ++ str "s") in
    res
  else f x y z

let time4 prefix f =
  let accum = ref 0. in
  let calls = ref 0 in
  fun x y z w ->
  if CDebug.(get_flag debug_loop_checking_timing_flag) then
    let start = Unix.gettimeofday () in
    let res = f x y z w in
    let stop = Unix.gettimeofday () in
    let time = stop -. start in
    let () = accum := time +. !accum in
    incr calls;
    let () = debug_timing Pp.(fun () -> prefix ++ str " executed in: " ++ Pp.real time ++ str "s") in
    let () = debug_timing Pp.(fun () -> prefix ++ str " total execution time is: " ++ Pp.real !accum ++ str "s" ++
      str " in " ++ int !calls ++ str " calls") in
    res
  else f x y z w

let filter_map_same f l =
  let rec aux l =
    match l with
    | [] -> l
    | hd :: tl ->
      match f hd with
      | Some hd' ->
        let tl' = aux tl in
        if hd == hd' && tl == tl' then l
        else hd' :: tl'
      | None -> aux tl
  in aux l

module Make (Point : Point) = struct

  module Index :
  sig
    type t
    val equal : t -> t -> bool
    val compare : t -> t -> int
    module Set : CSig.SetS with type elt = t
    module Map : CMap.ExtS with type key = t and module Set := Set
    type table
    val empty : table
    val fresh : Point.t -> table -> t * table
    val mem : Point.t -> table -> bool
    val find : Point.t -> table -> t
    val repr : t -> table -> Point.t
    val dom : table -> Point.Set.t
  end =
  struct
    type t = int
    let equal = Int.equal
    let compare = Int.compare
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

    let dom t = Point.Map.domain t.tab_bwd
  end

module PMap = Index.Map
module PSet = Index.Set

type univ_constraint = Point.t * constraint_type * Point.t

module Premises =
struct

  module Premise =
  struct
    type t = Index.t * int

    let equal x y : bool =
      let (idx, k) = x in
      let (idx', k') = y in
      if Index.equal idx idx' then
        Int.equal k k'
      else false

    let compare x y : int =
      let (idx, k) = x in
      let (idx', k') = y in
      match Index.compare idx idx' with
      | 0 -> Int.compare k k'
      | x -> x

  end

  (* Invariant: sorted, non-empty *)
  type t = Premise.t list

  let fold f g l =
    match l with
    | [] -> assert false
    | [hd] -> g hd
    | hd :: tl -> List.fold_left f (g hd) tl

  let iter = List.iter
  let for_all = List.for_all
  (* let exists = List.exists *)
  let _add prem (x : t) : t = CList.merge_set Premise.compare [prem] x
  let _union (x : t) (y : t) : t = CList.merge_set Premise.compare x y
  let compare : t -> t -> int = CList.compare Premise.compare
  let equal : t -> t -> bool = CList.equal Premise.equal

  let of_list l = l

end

let pr_with f (l, n) =
  if Int.equal n 0 then f l
  else Pp.(f l ++ Pp.str"+" ++ int n)

module ClausesOf = struct
  module ClauseInfo = struct
    type t = int * Premises.t

    let _equal x y : bool =
      let (k, prems) = x in
      let (k', prems') = y in
      if Int.equal k k' then
        Premises.equal prems prems'
      else false

    let compare x y : int =
      let (k, prems) = x in
      let (k', prems') = y in
      match Int.compare k k' with
      | 0 -> Premises.compare prems prems'
      | x -> x

    let of_list (k, prems) = (k, Premises.of_list prems)

    let pr pr_pointint concl (k, prem) =
      let open Pp in
      hov 0 (prlist_with_sep (fun () -> str ",") pr_pointint prem ++ str " → " ++ pr_pointint (concl, k))
    (* let has_bound m idx (_k, prems) = *)
      (* List.exists (fun (l, _) -> (repr m l) == idx) prems *)
  end

  module S = Set.Make(ClauseInfo)
  include S

  let pr pr_pointint concl cls =
    let open Pp in
    v 0 (prlist_with_sep spc (ClauseInfo.pr pr_pointint concl) (elements cls))

  (* Ocaml >= 4.11 has a more efficient version. *)
  let filter_map p l =
    fold (fun x acc ->
      match p x with
      | None ->  remove x acc
      | Some x' -> if x' == x then acc else add x' (remove x acc)) l l

end

type clause_info = (int * Premises.t)
type clause = Index.t * ClausesOf.t

let _is_empty_clause ((_, kprem) : clause) = ClausesOf.is_empty kprem

type mark = NoMark | Visited

(* Comparison on this type is pointer equality *)
type canonical_node =
  { canon: Index.t;
    value : int;
    clauses_bwd : ClausesOf.t;
    clauses_fwd : ClausesOf.t PMap.t;
    mutable mark : mark }

let unset_mark can = can.mark <- NoMark

(* A Point.t is either an alias for another one, or a canonical one,
    for which we know the points that are above *)

type entry =
  | Canonical of canonical_node
  | Equiv of Index.t

type model = {
  entries : entry PMap.t;
  table : Index.table }

(* let unset_marks m =
  PMap.iter (fun _ e ->
    match e with
    | Equiv _ -> ()
    | Canonical can -> unset_mark can) m.entries *)

let empty_model = {
  entries = PMap.empty;
  table = Index.empty
}

let enter_equiv m u v =
  { entries = PMap.modify u (fun _ a ->
          match a with
          | Canonical _ -> Equiv v
          | _ -> assert false) m.entries;
    table = m.table }

let change_node m n =
  { m with entries =
    PMap.modify n.canon
      (fun _ a ->
        match a with
        | Canonical _ -> Canonical n
        | _ -> assert false)
      m.entries }

(* canonical representative : we follow the Equiv links *)
let rec repr m u =
  match PMap.find u m.entries with
  | Equiv v -> repr m v
  | Canonical arc -> arc

let repr_node m u =
  try repr m (Index.find u m.table)
  with Not_found ->
    CErrors.anomaly ~label:"Univ.repr"
      Pp.(str"Universe " ++ Point.pr u ++ str" undefined.")


let pr_index_point m idx =
  let idx = try (repr m idx).canon with Not_found -> idx in
  try Point.pr (Index.repr idx m.table)
  with Not_found -> Pp.str"<point not in table>"

let pr_pointint m = pr_with (pr_index_point m)

let pr_clause_info m concl cl = ClausesOf.ClauseInfo.pr (pr_pointint m) concl cl

let pr_clauses_of m = ClausesOf.pr (pr_pointint m)

let repr_premise m (idx, k as x) =
  let idx' = (repr m idx).canon in
  if Index.equal idx idx' then x
  else (idx', k)

let repr_premises m (x : Premises.t) : Premises.t =
  CList.Smart.map (repr_premise m) x

let repr_clauses_of m ((k, prems as x) : ClausesOf.ClauseInfo.t) : ClausesOf.ClauseInfo.t =
  let prems' = repr_premises m prems in
  if prems' == prems then x
  else (k, prems')

let repr_clauses_of m x =
  ClausesOf.map (repr_clauses_of m) x

module ClausesOfRepr =
struct
  open ClausesOf
  let premise_equal_upto m (idx, k) (idx', k') =
    Int.equal k k' && repr m idx == repr m idx'

  let premises_equal_upto m prems prems' =
    CList.equal (premise_equal_upto m) prems prems'

  let premises_equal_upto m (k, prems) (k', prems') =
    k <= k' &&
    premises_equal_upto m prems prems'

  let mem_upto m (cl : ClauseInfo.t) cls =
    let eq cl' = premises_equal_upto m cl cl' in
    exists eq cls

  let subset_upto m cls cls' =
    for_all (fun cl -> mem_upto m cl cls') cls

  let filter_trivial_clause m l ((k, prems) as kprems) =
    let prems' = filter_map_same (fun (l', k' as x) ->
      let canl' = repr m l' in
      if Index.equal canl'.canon l && k' >= k then None
      else if Index.equal l' canl'.canon then Some x
      else Some (canl'.canon, k')) prems
    in
    match prems' with
    | [] -> None
    | _ ->
      if prems' == prems then Some kprems
      else Some (k, prems')

  let filter_trivial (m : model) l kprem =
    filter_map (filter_trivial_clause m l) kprem

  let union_upto m idx x y =
    union (filter_trivial m idx x) (filter_trivial m idx y)
end

module ClausesBackward =
struct
  type t = ClausesOf.t PMap.t

  let add ((idx, kprem) : clause) clauses : t =
    PMap.update idx
      (fun cls ->
        match cls with
        | None -> Some kprem
        | Some cls -> Some (ClausesOf.union kprem cls))
      clauses

  (* let union (clauses : t) (clauses' : t) : t = *)
    (* PMap.fold (fun idx cls acc -> add (idx, cls) acc) clauses clauses' *)

  let _union (clauses : t) (clauses' : t) : t =
    let merge _idx cls cls' =
      match cls, cls' with
      | None, None -> cls
      | None, Some _ -> cls'
      | Some _, None -> cls
      | Some cls, Some cls' -> Some (ClausesOf.union cls cls')
    in
    PMap.merge merge clauses clauses'

  let cardinal (cls : t) : int =
    PMap.fold (fun _ cls card ->
      ClausesOf.cardinal cls + card)
      cls 0

  let empty = PMap.empty

  let singleton cl = add cl empty

  let fold = PMap.fold


  let find idx clauses : ClausesOf.t =
    try PMap.find idx clauses
    with Not_found -> ClausesOf.empty

  let _add_upto (m : model) (l, kprem as cl : clause) (cls : t) : t =
    if ClausesOfRepr.subset_upto m kprem (find l cls) then cls
    else add cl cls

  let union_upto (m : model) (clauses : t) (clauses' : t) : t =
    let merge idx cls cls' =
      match cls, cls' with
      | None, None -> cls
      | None, Some _ -> cls'
      | Some _, None -> cls
      | Some cls, Some cls' ->
        Some (ClausesOfRepr.union_upto m idx cls cls')
    in
    PMap.merge merge clauses clauses'

  let repr m (clauses : t) : t =
    PMap.fold (fun idx clsof acc ->
      let idx' = (repr m idx).canon in
      let clsof' = repr_clauses_of m clsof in
      if Index.equal idx' idx && clsof' == clsof then acc
      else PMap.remove idx (PMap.add idx' clsof' acc))
      clauses clauses

  let _repr_clausesof m x =
    PMap.map (repr_clauses_of m) x

  let partition (p : Index.t -> ClausesOf.t -> bool) (cls : t) : t * t = PMap.partition p cls
  let _filter (p : Index.t -> ClausesOf.t -> bool) (cls : t) : t = PMap.filter p cls

end

let pr_clauses_bwd m (cls : ClausesBackward.t) =
  let open Pp in
  PMap.fold (fun concl cls acc -> pr_clauses_of m concl cls ++ spc () ++ acc) cls (Pp.mt())

let pr_clause m ((concl, kprem) : clause) =
  pr_clauses_of m concl kprem

module Clauses =
struct

  module ClauseOrd =
  struct
    open Premises
    type t = Premises.t * (Index.t * int)
    let compare x y : int =
      let (prems, concl) = x in
      let (prems', concl') = y in
      match Premise.compare concl concl' with
      | 0 -> Premises.compare prems prems'
      | x -> x
  end

  module S = Set.Make(ClauseOrd)
  include S

  (* type clause = ClauseOrd.t *)

end

type clauses = Clauses.t

(* Invariant: clauses map only canonical points in the model to their clauses *)
type t = {
  model : model;
  updates : PSet.t; (* The set of universes that required an update from the beginning *)
  clauses : clauses;
}

let check_invariants ~(required_canonical:Point.t -> bool) { model; updates; _ } =
  let required_canonical u = required_canonical (Index.repr u model.table) in
  let n_canon = ref 0 in
  PMap.iter (fun idx e ->
    match e with
    | Canonical can ->
      assert (Index.equal idx can.canon);
      assert (Index.mem (Index.repr idx model.table) model.table);
      assert (can.value >= 0);
      let cls = can.clauses_bwd in
      ClausesOf.iter
        (fun (k, prems) ->
          assert (k >= 0);
          let check_prem (l, k) =
            assert (k >= 0);
            assert (PMap.mem l model.entries)
          in
          Premises.iter check_prem prems) cls;
      assert (PMap.for_all (fun _ kprems ->
          ClausesOf.for_all (fun (_, prems) ->
            List.exists (fun (idx', _) -> can == repr model idx') prems) kprems) can.clauses_fwd);
      incr n_canon
    | Equiv idx' ->
      assert (PMap.mem idx' model.entries);
      assert (Index.mem (Index.repr idx' model.table) model.table);
      (* The clauses should not mention aliases *)
      assert (not (required_canonical idx)))
    model.entries;
  assert (PSet.subset updates (PMap.domain model.entries))

let model_max (m : model) : int =
  PMap.fold (fun _ k acc ->
    match k with Equiv _ -> acc | Canonical can -> max can.value acc)
    m.entries 0
let model_min (m : model) : int =
  PMap.fold (fun _ k acc ->
    match k with Equiv _ -> acc | Canonical can -> min can.value acc)
    m.entries 0

let canonical_universes (m : model) : int =
  PMap.fold (fun _ k acc ->
    match k with Equiv _ -> acc | Canonical _ -> succ acc)
    m.entries 0

let without_bound (m : model) : int =
  PMap.fold (fun _ k acc ->
    match k with Equiv _ -> acc | Canonical can ->
      let cls = can.clauses_bwd in
      if ClausesOf.is_empty cls then succ acc else acc)
    m.entries 0

let _pr_updates m s =
  let open Pp in
  prlist_with_sep spc (fun idx -> Point.pr (Index.repr idx m.table)) (PSet.elements s)


let statistics { model; updates; clauses } =
  let open Pp in
  str" " ++ int (PMap.cardinal model.entries) ++ str" universes" ++
  str", " ++ int (canonical_universes model) ++ str" canonical universes" ++
  str ", maximal value in the model is " ++ int (model_max model) ++
  str ", minimal value is " ++ int (model_min model) ++
  str", " ++ int (Clauses.cardinal clauses) ++ str" clauses." ++ spc () ++
  int (without_bound model) ++ str" canonical universes are not bounded above" ++
  str", " ++ int (PSet.cardinal updates) ++ str" updates"

let debug_check_invariants m =
  if CDebug.get_flag debug_loop_checking_invariants then
    (debug_invariants Pp.(fun () -> str"Checking invariants, " ++ statistics m);
      check_invariants ~required_canonical:(fun _ -> false) m)

(* PMaps are purely functional hashmaps *)

let model_value m l =
  try (repr m l).value
  with Not_found -> 0

let min_premise (m : model) prem =
  let g (l, k) = model_value m l - k in
  let f minl prem = min minl (g prem) in
  Premises.fold f g prem


module CanSet =
struct
  type t = (ClausesOf.t * ClausesBackward.t) PMap.t

  let fold f l acc = PMap.fold f l acc

  let add = PMap.add

  let mem = PMap.mem

  let empty = PMap.empty

  let is_empty = PMap.is_empty

  let cardinal = PMap.cardinal

  let pr m w =
    let open Pp in
    prlist_with_sep spc (fun (idx, _) -> Point.pr (Index.repr idx m.table)) (PMap.bindings w)

  let _pr_clauses m w =
    let open Pp in
    prlist_with_sep spc (fun (idx, (bwd, fwd)) ->
      Point.pr (Index.repr idx m.table) ++ str": " ++ spc () ++
      str" Backward clauses " ++ pr_clauses_of m idx bwd ++
      str" Forward clauses " ++ pr_clauses_bwd m fwd)
      (PMap.bindings w)


  let domain = PMap.domain

  let _of_pset model w = PSet.fold (fun idx ->
    let can = repr model idx in
    add can.canon (can.clauses_bwd, can.clauses_fwd)) w empty

end

let pr_w m w = CanSet.pr m w

let update_value (c, m) clause : (canonical_node * model) option =
  let (k, premises) = clause in
  let k0 = min_premise m premises in
  if k0 < 0 then None
  else
    let newk = k + k0 in
    if newk <= c.value then None
    else
      let c' = { c with value = newk } in
      Some (c', change_node m c')

let pr_can m can =
  Point.pr (Index.repr can.canon m.table)

let check_model_clauses_of_aux m can cls =
  let (can', m') =
    ClausesOf.fold (fun cls cwm ->
    match update_value cwm cls with
    | None -> cwm
    | Some (can, _ as cwm') ->
      debug Pp.(fun () -> str"Updated value of " ++ pr_can m can ++ str " to " ++ int can.value);
      debug Pp.(fun () -> str" due to clauses " ++ pr_clauses_bwd m (ClausesBackward.singleton (can.canon, ClausesOf.singleton cls)));
      cwm')
    cls (can, m)
  in (can', m')

(** Check a set of forward clauses *)
let check_model_fwd_clauses_aux (cls : ClausesBackward.t) acc =
  PMap.fold (fun concl cls (modified, w, m) ->
    let can = repr m concl in
    let can', m' = check_model_clauses_of_aux m can cls in
    if can == can' then (* not modifed *) (modified, w, m')
    else (true, CanSet.add can.canon (can.clauses_bwd, can.clauses_fwd) w, m')
    )
    cls acc

let check_model_fwd_aux (w, m) =
  CanSet.fold (fun _ (_, fwd) acc ->
    check_model_fwd_clauses_aux fwd acc)
  w (false, w, m)

let check_clauses_with_premises (updates : CanSet.t) model : (CanSet.t * model) option =
  let (modified, updates, model) = check_model_fwd_aux (updates, model) in
  if modified then Some (updates, model) else
    (debug Pp.(fun () -> str"Found a model"); None)

(* let _check_model_bwd = check_model *)
let cardinal_fwd w =
  CanSet.fold (fun _idx (_, fwd) acc -> ClausesBackward.cardinal fwd + acc) w 0

let check_clauses_with_premises (updates : CanSet.t) model : (CanSet.t * model) option =
  let open Pp in
  debug_check_model (fun () -> str"check_model on " ++ int (CanSet.cardinal updates) ++ str" universes, " ++
  int (cardinal_fwd updates) ++ str " clauses");
  check_clauses_with_premises updates model

let check_clauses_with_premises = time2 (Pp.str"check_clauses_with_premises") check_clauses_with_premises

(* let check_model = time3 (Pp.str "check_model") check_model *)

type 'a result = Loop | Model of 'a * model

let canonical_cardinal m =
  PMap.fold (fun _ e acc ->
    match e with
    | Equiv _ -> acc
    | Canonical _ -> succ acc)
    m.entries 0

let can_all_premises_in m w prem =
  Premises.for_all (fun (l, _) -> CanSet.mem (repr m l).canon w) prem

(* Partition the clauses according to the presence of w in the premises, and only w in the conclusions *)
let partition_clauses_fwd model (w : CanSet.t) : CanSet.t * CanSet.t * CanSet.t =
  CanSet.fold (fun idx (bwd, fwd) (allw, conclw, conclnw) ->
    let bwdw, bwdnw = ClausesOf.partition (fun (_k, prems) -> can_all_premises_in model w prems) bwd in
    let fwdw, fwdnw = ClausesBackward.partition (fun concl _clsinfo -> CanSet.mem (repr model concl).canon w) fwd in
    let allw = CanSet.add idx (bwdw, fwdw) allw (* Premises and conclusions in w *)
    and conclw = CanSet.add idx (bwdnw, ClausesBackward.empty) conclw (* Conclusions in w, premises not in w *)
    and conclnw = CanSet.add idx (ClausesOf.empty, fwdnw) conclnw in (* Conclusions not in w, Premises in w *)
    (allw, conclw, conclnw))
    w (CanSet.empty, CanSet.empty, CanSet.empty)

let partition_clauses_fwd = time2 (Pp.str"partition clauses fwd") partition_clauses_fwd

let check { model; updates; clauses } (w : CanSet.t) =
  let cV = canonical_cardinal model in
  debug_check_invariants { model; updates; clauses };
  let rec inner_loop premconclw conclw m =
    (* Should consider only clauses with conclusions in w *)
    (* Partition the clauses according to the presence of w in the premises *)
    let cardW = CanSet.cardinal premconclw in
    debug_loop Pp.(fun () -> str "Inner loop on " ++ int cardW ++ str" universes: " ++
      str " Premises and conclusions in w: " ++ pr_w m premconclw ++
      str " Conclusions in w: " ++ pr_w m conclw);
    let rec inner_loop_partition w m =
      debug_loop Pp.(fun () -> str "w = " ++ pr_w m w);
      match loop cardW w m with
      | Loop -> Loop
      | Model (wr, mr) ->
        debug_loop Pp.(fun () -> str "wr = " ++ pr_w mr wr);
        (match check_clauses_with_premises conclw mr with
        | Some (wconcl, mconcl) ->
          debug_loop Pp.(fun () -> str "wconcl = " ++ pr_w mconcl wconcl);
          inner_loop_partition wconcl mconcl
        | None ->
          debug_loop Pp.(fun () -> str"Inner loop found a model");
          Model (wr, mr))
      in inner_loop_partition premconclw m
  and loop cV u m =
    debug_loop Pp.(fun () -> str"loop iteration on "  ++ CanSet.pr m u);
    match check_clauses_with_premises u m with
    | None -> Model (u, m)
    | Some (w, m) ->
      if Int.equal (CanSet.cardinal w) cV
      then (debug_loop Pp.(fun () -> str"Found a loop"); Loop)
      else
        let (premconclw, conclw, premw) = partition_clauses_fwd m w in
        debug_loop Pp.(fun () -> str"partitioned clauses: forward from and to w " ++ spc () ++
          CanSet.pr { m with entries = PMap.empty } premconclw);
        debug_loop Pp.(fun () -> str"partitioned clauses: forward to w not from w: " ++ spc () ++
          CanSet.pr { m with entries = PMap.empty } conclw);
        debug_loop Pp.(fun () -> str"partitioned clauses: backward not from w, forward to w " ++ spc () ++
          CanSet.pr { m with entries = PMap.empty } premw);

        (* debug_check_invariants { model = m; updates = w; clauses = conclnW }; *)
        (match inner_loop premconclw conclw m with
        | Loop -> Loop
        | Model (wc, mc) ->
          debug_loop Pp.(fun () -> str "wc = " ++ pr_w mc wc);
          (* wc is a subset of w *)
          (match check_clauses_with_premises premw mc with
          (* check_model_compare conclnW wc mc with *)
          | None -> Model (wc, mc)
          | Some (wcls, mcls) -> loop cV wcls mcls))
  in
  match loop cV w model with
  | Loop -> Loop
  | Model (wc, mc) -> Model (PSet.union (CanSet.domain wc) updates, mc)

(* let check m w = *)
  (* debug Pp.(fun () -> str"Calling loop-checking"); *)
  (* check m w *)
  (* debug Pp.(fun () -> str"Loop-checking terminated"); *)
  (* with Stack_overflow -> *)
    (* CErrors.anomaly (Pp.str "check raised a stack overflow") *)

let entry_value m e =
  match e with
  | Equiv idx -> (repr m idx).value
  | Canonical can -> can.value

let pr_levelmap (m : model) : Pp.t =
  let open Pp in
  h (prlist_with_sep fnl (fun (u, v) ->
    let value = entry_value m v in
    let point = Index.repr u m.table in
    Point.pr point ++ str" -> " ++ int value) (PMap.bindings m.entries))
  (* Point.Map.pr Pp.int m  *)

let pr_model { model; _ } =
  Pp.(str "model: " ++ pr_levelmap model)

let debug_model m =
  debug_model Pp.(fun () -> str"Model is " ++ pr_levelmap m)

let _repr_clause m (concl, prem as cl : clause) =
  let concl' = (repr m concl).canon in
  let prem' = repr_clauses_of m prem in
  if concl' == concl && prem' == prem then cl
  else (concl', prem')

(* let add_clause_model m cl : t = *)
  (* { m with clauses = Clauses.add cl m.clauses } *)

let modify_can canidx (f : Index.t -> canonical_node -> canonical_node) =
  PMap.modify canidx
    (fun idx entry ->
    match entry with
    | Equiv _ -> assert false
    | Canonical can -> let can' = f idx can in
      if can' == can then entry else Canonical can')

let add_clause_model m (prems, (l, k)) : model =
  let canl = (repr m l).canon in
  let clof = (k, prems) in
  let entries = (* Add clause to the backwards clauses of l *)
    modify_can canl (fun _ ({ clauses_bwd; _ } as can) ->
      let bwd =
        (* if ClausesOfRepr.mem_upto m clof clauses_bwd then clauses_bwd else  *)
          ClausesOf.add clof clauses_bwd in
      if bwd == clauses_bwd then can
      else { can with clauses_bwd = bwd })
    m.entries
  in
  let entries = (* Add clause to the forward clauses from the premises *)
    List.fold_left (fun entries (idx, _) ->
      let canidx = (repr m idx).canon in
      modify_can canidx (fun _idx ({ clauses_fwd; _ } as can) ->
        (* let fwd = ClausesBackward.add_upto m (canl, ClausesOf.singleton clof) clauses_fwd in  *)
        let fwd = ClausesBackward.add (canl, ClausesOf.singleton clof) clauses_fwd in
        if fwd == clauses_fwd then can
        else { can with clauses_fwd = fwd })
        entries)
      entries prems
  in { m with entries }

(** Assumes premise and conclusion already in canonical form *)
let add_clauses_of_model m (l, kprems) =
  ClausesOf.fold (fun (k, prems) m ->
    let cl = (prems, (l, k)) in
    { m with model = add_clause_model m.model cl; clauses = m.clauses }) kprems m

let repr_model m =
  let entries' =
    PMap.Smart.map (function
    | Equiv _ as entry -> entry
    | Canonical can as entry ->
      let bwd = repr_clauses_of m can.clauses_bwd in
      let fwd = ClausesBackward.repr m can.clauses_fwd in
      if bwd == can.clauses_bwd && fwd == can.clauses_fwd then entry
      else Canonical { can with clauses_bwd = bwd; clauses_fwd = fwd })
    m.entries
  in
  if entries' == m.entries then m
  else { m with entries = entries' }

let _repr_all m =
  { m with model = repr_model m.model }

let _clauses_levels cls =
  PMap.fold (fun concl _ acc -> PSet.add concl acc)
    (* (ClausesOf.fold (fun cli acc ->
      let (_, prems) = cli in
      List.fold_left (fun acc (l, _k') -> PSet.add (repr m l).canon acc) acc prems)
      cls acc)) *)
    cls PSet.empty

let infer_clauses_extension w m =
  debug_check_invariants m;
  (* debug_check_invariants model clauses; *)
  debug Pp.(fun () -> str"Calling loop-checking" ++ statistics m);
  (* debug Pp.(fun () -> str"Filtered clauses " ++ int (Clauses.cardinal filtered_clauses)); *)
  (* Clauses.mark m.clauses ClausesOf.ClauseInfo.Skip;  *)
  (* match check_model clauses (clauses_levels m.model clauses) m.model with
  | None -> Some m
  | Some (w, m') ->
    let inw = clauses_forward m' m.clauses w in
    debug Pp.(fun () -> str"After one check model: " ++ int (Clauses.cardinal inw) ++ str" having premises in w");*)
  (* let levels = PSet.union w (clauses_levels clauses.Clauses.clauses_fwd) in *)
  match check m w with
  | Loop ->
    debug Pp.(fun () -> str"loop-checking found a loop");
    None
  | Model (updates, model) ->
    let m = { model; updates; clauses = m.clauses } in
    debug_check_invariants m;
    debug_model model;
    debug Pp.(fun () -> str"loop-checking found a model");
    Some m

let infer_clauses_extension = time2 Pp.(str"infer_clauses_extension") infer_clauses_extension
let empty = { model = empty_model; updates = PSet.empty; clauses = Clauses.empty }

let _filter_trivial_can_clause canl ((k, prems) as kprems) =
  let prems' = CList.filter (fun (l', k') -> not (Index.equal l' canl.canon && k' >= k)) prems in
  match prems' with
  | [] -> None
  | _ ->
    if prems' == prems then Some kprems
    else Some (k, prems')

(* let add_can_clause (m : model) canl kprem (cls : clauses) : clauses =
  match filter_trivial_can_clause canl kprem with
  | None -> cls
  | Some kprem ->
    let kprem = ClausesOf.ClauseInfo.of_list kprem in
    if ClausesOfRepr.mem_upto m kprem canl.clauses_bwd then cls
    else Clauses.add (canl.canon, ClausesOf.singleton kprem) cls *)


type pclause_info = (int * (Point.t * int) list)

let _to_clause_info m (k, prems : pclause_info) : clause_info =
  let trans_prem (p, k) =
    let can = repr_node m p in
    (can.canon, k)
  in
  (k, List.map trans_prem prems)

(* let _check_leq (m : t) u v = *)
  (* let cls = clauses_of_le_constraint m.model u v Clauses.empty in *)
  (* check_clauses m.model cls *)

(* let _is_bound (m : t) can cano : bool =
  PMap.exists (fun concl clsc ->
    if Index.equal concl can.canon then false
    else ClausesOf.has_bound m.model cano clsc) m.clauses *)

(* let inspect_bwd m (cls : ClausesBackward.t) : unit =
  ClausesBackward.fold (fun idx prems _ ->
    let triv = filter_trivial_clause m (idx, prems) in
    debug Pp.(fun () -> str "Clause " ++ pr_clause m triv ++ str" is trivial? " ++ bool (is_empty_clause triv)))
    cls () *)

(* Precondition: canu.value == canv.value, so no new model needs to be computed *)
let enforce_eq_can { model; updates; clauses } canu canv : canonical_node * t =
  assert (canu.value == canv.value);
  assert (canu != canv);
  (* v := u or u := v, depending on the cardinal of attached constraints
     (heuristically, keeps the representant of Set a canonical node) *)
  debug_check_invariants { model; updates; clauses = clauses };
  let can, other, model =
    if Point.keep_canonical (Index.repr canu.canon model.table) then
      canu, canv, enter_equiv model canv.canon canu.canon
    else
      canv, canu, enter_equiv model canu.canon canv.canon
  in
  let model =
    let bwd = ClausesOfRepr.union_upto model can.canon can.clauses_bwd other.clauses_bwd in
    let fwd = ClausesBackward.union_upto model can.clauses_fwd other.clauses_fwd in
    let modeln = { model with entries = PMap.empty } in
      debug Pp.(fun () -> str"Add forward clauses for " ++
        pr_can model can ++ str": " ++ spc () ++
        pr_clauses_bwd modeln fwd);
      debug Pp.(fun () -> str"Previous forward clauses for " ++
        pr_can model can ++ str": " ++ spc () ++
        pr_clauses_bwd modeln can.clauses_fwd);
      debug Pp.(fun () -> str"Other forward clauses for " ++
        pr_can model can ++ str": " ++ spc () ++
        pr_clauses_bwd modeln other.clauses_fwd);
      change_node model { can with clauses_bwd = bwd; clauses_fwd = fwd }
  in
  let updates = PSet.remove other.canon updates in
  let m = { model; updates; clauses } in
  debug_check_invariants m;
  can, m

let enforce_eq_can = time3 (Pp.str"enforce_eq_can") enforce_eq_can


let _enforce_eq_indices (m : t) u v =
  let canu = repr m.model u in
  let canv = repr m.model v in
  if canu == canv then m
  else snd (enforce_eq_can m canu canv)

(* let _pr_can_constraints m can =
  let cls = Clauses.of_bwd can.canon m.clauses in
  pr_clauses_of m.model can.canon cls *)

let make_equiv m equiv =
  debug Pp.(fun () -> str"Unifying universes: " ++
    prlist_with_sep spc (fun can -> pr_can m.model can) equiv);
  match equiv with
  | can :: can' :: tl ->
    (* We are about to merge all these universes as they should be equal in the model,
      they should hence have the same values *)
    if CDebug.(get_flag debug_loop_checking_invariants) then
      assert (List.for_all (fun x -> x.value = can.value) (can' :: tl));
    let can, m =
      List.fold_left (fun (can, m) can' -> enforce_eq_can m can can')
        (enforce_eq_can m can can') tl
    in
    debug Pp.(fun () -> str"Chosen canonical universe: " ++ pr_can m.model can);
          (* str"Constraints:" ++ pr_can_constraints m can); *)
    m
  | _ -> assert false

let simplify_clauses_between ({ model; _ } as m) v u =
  let canv = repr model v in
  let canu = repr model u in
  if canv == canu then Some m else
  let rec forward prev acc visited canv : canonical_node list * canonical_node list =
    if canv.mark == Visited then acc, visited else
    let () = canv.mark <- Visited in
    let visited = canv :: visited in
    let cls = canv.clauses_bwd in
    ClausesOf.fold (fun cli acc ->
      let (k, prems) = cli in
      List.fold_left (fun (acc, visited) (l, _k') ->
        let canl = repr model l in
        if canl.mark == Visited then acc, visited
        else
          if canl == canu then begin
            assert (Int.equal k 0); (* there would be a loop otherwise *)
            (CList.unionq (canu :: canv :: prev) acc), visited
          end
        else if Int.equal k 0 then forward (canv :: prev) acc visited canl
        else (acc, visited))
        acc prems) cls (acc, visited)
  in
  let equiv, visited = forward [] [] [] canv in
  let () = List.iter unset_mark visited in
  if CList.is_empty equiv then Some m
  else Some (make_equiv m equiv)
    (* if recheck then
      match check m.clauses m.model with
      | Loop -> CErrors.anomaly Pp.(str"Equating universes resulted in a loop")
      | Model (_w, model) ->
        debug (fun () -> Pp.(str"Equating universes resulted in a model"));
        debug_check_invariants model m.clauses;
        Some { model; clauses = m.clauses }
    else Some m *)

let simplify_clauses_between =
  time3 (Pp.str "simplify_clauses_between") simplify_clauses_between
(*

let enforce_eq_points ({ model; clauses } as m : t) u v =
  debug Pp.(fun () -> str"Enforce equal points");
  let canu = repr_node model u in
  let canv = repr_node model v in
  if canu == canv then ((false, canu), m)
  else
    if Int.equal canu.value canv.value then
    enforce_eq_can m canu canv
  else

    let clauses' = add_clauses model canv (ClausesOf.singleton (0, [(canu.canon, 0)])) clauses in
    let clauses'' = add_clauses model canu (ClausesOf.singleton (0, [(canv.canon, 0)])) clauses' in
    ((true, canu), { model; clauses = clauses'' }) *)

type nat = int
type can_constraint = (canonical_node * nat * canonical_node)

let clause_of_can_constraint (cstr : can_constraint) =
  let (l, k, r) = cstr in (* l + k <= r *)
  ([(r.canon, 0)], (l.canon, k))

let make_clause (prems, (l, k)) : clause =
  (l, ClausesOf.singleton (ClausesOf.ClauseInfo.of_list (k, prems)))

let clauses_of_can_constraint (cstr : can_constraint) : clause =
  make_clause (clause_of_can_constraint cstr)

let clauses_of_univ_constraint (m : t) (cstr : univ_constraint) clauses : ClausesBackward.t =
  let (l, k, r) = cstr in (* l + k <= r *)
  let canl = repr_node m.model l in
  let canr = repr_node m.model r in
  match k with
  | Le -> ClausesBackward.add (clauses_of_can_constraint (canl, 0, canr)) clauses
  | Lt -> ClausesBackward.add (clauses_of_can_constraint (canl, 1, canr)) clauses
  | Eq -> ClausesBackward.add (clauses_of_can_constraint (canl, 0, canr))
      (ClausesBackward.add (clauses_of_can_constraint (canr, 0, canl)) clauses)

let filter_trivial_clause m (l, kprems as x) =
  let prems' =
    ClausesOf.filter_map (fun kprems -> ClausesOfRepr.filter_trivial_clause m l kprems) kprems
  in
  if ClausesOf.is_empty prems' then None
  else if prems' == kprems then Some x
  else Some (l, prems')

let mem_clause m ((l, kprem) : clause) : bool =
  ClausesOfRepr.subset_upto m.model kprem (repr m.model l).clauses_bwd

(* let enforce_Clauses.of_bwd_can_constraint = *)
  (* time2 (Pp.str "Enforcing clauses") enforce_Clauses.of_bwd_can_constraint *)

type 'a check_function = t -> 'a -> 'a -> bool

let check_clause_holds m can clause =
  let (k, premises) = clause in
  let canp = List.map (fun (idx, k) -> repr m idx, k) premises in
  let rec aux (canv, kpath) =
      try let k' = List.assq canv canp in kpath <= k'
      with Not_found ->
        let bwd = canv.clauses_bwd in
        ClausesOf.exists
          (fun (kp, premises) ->
            List.exists (fun (idx, k') ->
              let gidx = repr m idx in
              aux (gidx, kp - k' + kpath)) premises)
            bwd
  in aux (can, k)

let _check_clause_holds_fwd m can clause =
  let (k, premises) = clause in
  let canp = List.map (fun (idx, k) -> repr m idx, k) premises in
  let rec aux (canv, kpath) =
    let fwd = canv.clauses_fwd in (* Constraints canv -> ? *)
    try let cls = PMap.find can.canon fwd in
      (* Constraints canv -> can *)
      ClausesOf.exists (fun (kp, premises) ->
        let (_, kcanv) = List.hd premises in
        (* canv + kcanv -> can + kp, does (canv + kpath) -> (can + k) holds *)
        kcanv + kpath >= k - kp) cls
    with Not_found ->
      PMap.exists (fun idx cls ->
        let canidx = repr m idx in
        ClausesOf.exists (fun (kp, premises) ->
          List.exists (fun (_, kcanv) -> aux (canidx, kcanv - kp + kpath)) premises)
        cls) fwd
  in List.exists aux canp

(* Checks that a clause currently holds in the model *)
let check_clause_of m conclv clause =
  let (k, premises) = clause in
  let k0 = min_premise m premises in
  if k0 < 0 then false (* We do not allow vacuously true constraints *)
  else
    (debug Pp.(fun () -> str"check_clause_of: k = " ++ int k ++ str" k0 = " ++ int k0 ++ str" conclv = " ++ int conclv);
    k + k0 <= conclv)

(* A clause x -> y might hold in the current minimal model without being valid in all
   its extensions. We check that the "inverse" clause y -> x + 1 does *not* hold as
   well to ensure that x -> y will really hold in all extensions.
   Both clauses cannot be valid at the same time as this would imply a loop. *)
let _check_inv_clause_of m concl clause =
  let (k, premises) = clause in
  let chk = List.for_all (fun (idx, idxk) ->
    let vidx = model_value m idx in
    check_clause_of m (vidx + idxk) (1, [concl, k]))
    premises
  in
  debug Pp.(fun () -> str"check_inv_clause_of: " ++  pr_clause_info m concl clause ++ str " = " ++ bool chk);
  chk

let check_clauses m (cls : ClausesBackward.t) =
  PMap.for_all (fun concl cls ->
    let can = repr m concl in
    ClausesOf.for_all (fun cl ->
      if check_clause_of m can.value cl then check_clause_holds m (repr m concl) cl
      else false) cls)
    cls

let check_clauses m cls =
  if check_clauses m cls then
    (debug Pp.(fun () -> str"check_clauses succeeded on: " ++ pr_clauses_bwd m cls ++
    str" and model " ++ pr_levelmap m); true)
  else (debug Pp.(fun () -> str"check_clauses failed on: " ++ pr_clauses_bwd m cls ++
    str" and model " ++ pr_levelmap m); false)

let check_clause m (concl, cl) =
  let conclv = repr m concl in
  ClausesOf.for_all (fun cl -> check_clause_holds m conclv cl) cl

let _check_clause = time2 (Pp.str"check_clause") check_clause

let check_lt (m : t) u v =
  let cls = clauses_of_univ_constraint m (u, Lt, v) ClausesBackward.empty in
  check_clauses m.model cls

let check_leq (m : t) u v =
  let cls = clauses_of_univ_constraint m (u, Le, v) ClausesBackward.empty in
  check_clauses m.model cls

let check_eq m u v =
  let cls = clauses_of_univ_constraint m (u, Eq, v) ClausesBackward.empty in
  check_clauses m.model cls


(* let pr_clauses m cls = Clauses.pr pr_clause m cls.Clauses.clauses_bwd *)

let _mem_clause = time2 (Pp.str"mem_clause") mem_clause
let add_clauses_of_model = time2 (Pp.str "add_clauses_of_model") add_clauses_of_model

let update_model_value (m : model) can k' : model =
  let k' = max can.value k' in
  if Int.equal k' can.value then m
  else
    (debug Pp.(fun () -> str"Updated value of " ++ pr_can m can ++ str " to " ++ int k');
    change_node m { can with value = k' })


let update_model ((concl, kprems) : clause) (m : model) : CanSet.t * model =
  ClausesOf.fold (fun (k, prems) (w, m as acc) ->
    let k0 = min_premise m prems in
    let can = repr m concl in
    let m' = update_model_value m can (k + k0) in
    if m' != m then (CanSet.add can.canon (can.clauses_bwd, can.clauses_fwd) w, m') else acc)
    kprems (CanSet.empty, m)

let infer_clause_extension cl m =
  (* debug Pp.(fun () -> str "current model is: " ++ pr_levelmap m.model); *)
  debug_check_invariants m;
  debug Pp.(fun () -> str"Enforcing clause " ++ pr_clause m.model cl);
  match filter_trivial_clause m.model cl with
  | None -> Some m
  | Some cl ->
    (* if mem_clause m cl then Some m else *)
    let w, model = update_model cl m.model in
    if CanSet.is_empty w then begin
      (* The clause is already true in the current model,
        but might not be in an extension, so we add it still *)
      debug Pp.(fun () -> str"Clause is valid in the current model");
      let m = add_clauses_of_model { m with model } cl in
      (* debug_clauses Pp.(fun () -> str"Clauses: " ++ pr_clauses m.model m.clauses); *)
      Some m
    end else begin
      (* The clauses are not valid in the current model, we have to find a new one *)
      debug Pp.(fun () -> str"Enforcing clauses requires a new inference");
      let m = add_clauses_of_model { m with model } cl in
      match infer_clauses_extension w m with
      | None ->
        debug Pp.(fun () -> str"Enforcing clauses " ++ pr_clause m.model cl ++ str" resulted in a loop");
        None
      | Some _ as x -> x
        (* assert (check_clause m.model cl); *)
    end

let infer_extension x k y m =
  let cl = clauses_of_can_constraint (x, k, y) in
  infer_clause_extension cl m

let infer_extension =
  time4 Pp.(str "infer_extension") infer_extension

(* Enforce u <= v and check if v <= u already held, in that case, enforce u = v *)
let enforce_leq_can u v m =
  match infer_extension u 0 v m with
  | None -> None
  | Some m' ->
    if m' != m then simplify_clauses_between m' v.canon u.canon
    else Some m (* The clause was already present so we already checked for v <= u *)

let enforce_leq u v m =
  let canu = repr_node m.model u in
  let canv = repr_node m.model v in
  enforce_leq_can canu canv m

let enforce_lt u v m =
  let canu = repr_node m.model u in
  let canv = repr_node m.model v in
  infer_extension canu 1 canv m

let enforce_eq u v m =
  let canu = repr_node m.model u in
  let canv = repr_node m.model v in
  if canu == canv then Some m
  else begin
    debug Pp.(fun () -> str"enforce_eq: " ++ pr_can m.model canu ++ str" = " ++ pr_can m.model canv);
    match Int.compare canu.value canv.value with
    | 0 -> Some (snd (enforce_eq_can m canu canv))
    | x when x < 0 ->
      (* canu.value < canv.value, so v <= u is trivial and we cannot have u < v,
         only u <= v in the clauses.
         The first enforce will be fast, the second can involve an inference *)
      (* let cls = clauses_forward m.model m.clauses (PSet.singleton canu.canon) in *)
      (* debug Pp.(fun () -> str"enforce_eq: clauses to move " ++ pr_clauses m.model cls); *)
      Option.bind (infer_extension canv 0 canu m)
        (fun m' ->
          let canu' = repr m'.model canu.canon in
          let canv' =  repr m'.model canv.canon in
          enforce_leq_can canu' canv' m')
    | _ ->
      (* canv.value < canu.value, so u <= v is trivial.
          The first enforce will be fast, the second can involve an inference *)
      (* let cls = clauses_forward m.model m.clauses (PSet.singleton canv.canon) in *)
      (* debug Pp.(fun () -> str"enforce_eq: clauses to move " ++ pr_clauses m.model cls); *)
      Option.bind (infer_extension canu 0 canv m)
        (fun m' ->
          let canu' = repr m'.model canu.canon in
          let canv' =  repr m'.model canv.canon in
          enforce_leq_can canv' canu' m')
  end

type lub = (Point.t * int) list
type ilub = (Index.t * int) list

(* max u_i <= v <-> ∧_i u_i <= v *)
let clauses_of_le_constraint (u : ilub) (v : ilub) cls : clauses =
  List.fold_left (fun cls (u, k) ->
    Clauses.add (v, (u, k)) cls) cls u

let clauses_of_constraint m (u : lub) k (v : lub) cls =
  let u = List.map (fun (p, k) -> Index.find p m.table, k) u in
  let v = List.map (fun (p, k) -> Index.find p m.table, k) v in
  match k with
  | Le -> clauses_of_le_constraint u v cls
  | Lt -> clauses_of_le_constraint (List.map (fun (l, k) -> (l, k + 1)) u) v cls
  | Eq -> clauses_of_le_constraint u v (clauses_of_le_constraint v u cls)

let enforce_constraint u k v (m : t) =
  let cls = clauses_of_constraint m.model u k v Clauses.empty in
  Clauses.fold (fun (prems, (concl, k)) m ->
    match m with
    | None -> None
    | Some m -> infer_clause_extension (concl, ClausesOf.singleton (k, prems)) m) cls (Some m)

exception AlreadyDeclared

let add_model u { entries; table } =
  if Index.mem u table then raise AlreadyDeclared
  else
    let idx, table = Index.fresh u table in
    let can = Canonical { canon = idx; value = 0; mark = NoMark;
      clauses_fwd = PMap.empty; clauses_bwd = ClausesOf.empty } in
    let entries = PMap.add idx can entries in
    idx, { entries; table }

let add ?(rank:int option) u { model; updates; clauses } =
  let _r = rank in
  debug Pp.(fun () -> str"Declaring level " ++ Point.pr u);
  let _idx, model = add_model u model in
  { model; updates; clauses }

exception Undeclared of Point.t

let check_declared { model; _ } us =
  let check l = if not (Index.mem l model.table) then raise (Undeclared l) in
  Point.Set.iter check us

let get_explanation (cstr : Point.t * constraint_type * Point.t) _ : (constraint_type * Point.t) list =
  let _cstr = cstr in
  (* TODO *)
  []

let pr_constraint_type k =
  let open Pp in
  match k with
  | Eq -> str " = "
  | Le -> str " ≤ "
  | Lt -> str " < "

let constraint_type_ord c1 c2 = match c1, c2 with
| Lt, Lt -> 0
| Lt, _ -> -1
| Le, Lt -> 1
| Le, Le -> 0
| Le, Eq -> -1
| Eq, Eq -> 0
| Eq, _ -> 1

module UConstraintOrd =
struct
type t = univ_constraint
let compare (u,c,v) (u',c',v') =
  let i = constraint_type_ord c c' in
  if not (Int.equal i 0) then i
  else
    let i' = Point.compare u u' in
    if not (Int.equal i' 0) then i'
    else Point.compare v v'
end


module Constraints =
struct
  module S = Set.Make(UConstraintOrd)
  include S

  let _pr prl c =
    let open Pp in
    v 0 (prlist_with_sep spc (fun (u1,op,u2) ->
      hov 0 (prl u1 ++ pr_constraint_type op ++ prl u2))
       (elements c))
end

(* This only works for level (+1) <= level constraints *)
let constraints_of_clauses m clauses =
  ClausesBackward.fold (fun concl cls cstrs ->
    let conclp = Index.repr concl m.table in
    ClausesOf.fold (fun cli cstrs ->
      let (k, prems) = cli in
      match prems with
      | [(v, 0)] ->
        let vp = Index.repr v m.table in
        if k = 0 then Constraints.add (conclp, Le, vp) cstrs
        else if k = 1 then Constraints.add (conclp, Lt, vp) cstrs
        else assert false
      | _ -> assert false) cls cstrs)
    clauses Constraints.empty

let constraints_of { model; _ } fold acc =
  let module UF = Unionfind.Make (Point.Set) (Point.Map) in
  let uf = UF.create () in
  let bwd = ref ClausesBackward.empty in
  let constraints_of u v =
    match v with
    | Canonical can ->
      bwd := ClausesBackward.add (can.canon, can.clauses_bwd) !bwd
    | Equiv v ->
      let u = Index.repr u model.table in
      let v = Index.repr v model.table in
      UF.union u v uf
  in
  let () = PMap.iter constraints_of model.entries in
  let cstrs = constraints_of_clauses model !bwd in
  Constraints.fold fold cstrs acc, UF.partition uf

type 'a constraint_fold = Point.t * constraint_type * Point.t -> 'a -> 'a

let constraints_for ~(kept:Point.Set.t) { model; _ } (fold : 'a constraint_fold) (accu : 'a) =
  (* rmap: partial map from canonical points to kept points *)
  let add_cst u knd v (cst : 'a) =
    fold (Index.repr u model.table, knd, Index.repr v model.table) cst
  in
  let kept = Point.Set.fold (fun u accu -> PSet.add (Index.find u model.table) accu) kept PSet.empty in
  let rmap, csts = PSet.fold (fun u (rmap,csts) ->
      let arcu = repr model u in
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
    | (prems,k)::todo ->
      let v = match prems with [v, 0] -> v | _ -> assert false in
      (* constraints cannot have premisses of other shapes *)
      let v = repr model v in
      (match PMap.find v.canon rmap with
      | v ->
        let d = if k > 0 then Lt else Le in
        let csts = add_cst u d v csts in
        add_from u csts todo
      | exception Not_found ->
        let cls = v.clauses_bwd in
        (* v is not equal to any kept point *)
        let todo =
          ClausesOf.fold (fun cli todo -> let (k', prems') = cli in (prems', k + k') :: todo)
            cls todo
        in
        add_from u csts todo)
  in
  PSet.fold (fun u csts ->
      let arc = repr model u in
      let cls = arc.clauses_bwd in
      ClausesOf.fold (fun cli csts -> let (k, prems) = cli in add_from u csts [prems,k]) cls csts)
    kept csts

(*
  let cstrs = constraints_of_clauses model clauses in
  let cstrs = Constraints.filter (fun (l, _, r) -> Point.Set.mem l kept || Point.Set.mem r kept) cstrs in
  Constraints.fold fold cstrs acc *)

let domain { model; _ } = Index.dom model.table

let choose p { model; _} p' =
  let canp' = repr_node model p' in
  let pointp' = Index.repr canp'.canon model.table in
  if p pointp' then Some pointp'
  else PMap.fold (fun idx e acc ->
      match acc with
      | Some _ -> acc
      | None ->
        match e with
        | Equiv idx' ->
          let canp'' = repr model idx' in
          if canp' == canp'' then
            let pointp' = Index.repr idx model.table in
            if p pointp' then Some pointp'
            else acc
          else acc
        | Canonical _ -> acc)
      model.entries None

type node =
  | Alias of Point.t
  | Node of bool Point.Map.t (** Nodes v s.t. u < v (true) or u <= v (false) *)

type repr = node Point.Map.t
let repr { model; _ } =
  PMap.fold (fun idx e acc ->
    let conclp = Index.repr idx model.table in
    let node = match e with
    | Equiv idx -> Alias (Index.repr idx model.table)
    | Canonical can ->
      let prems = can.clauses_bwd in
      let map =
        ClausesOf.fold (fun cli map ->
          let (k, prem) = cli in
          match prem with
          | [(v, 0)] ->
            let canv = repr model v in
            let vp = Index.repr canv.canon model.table in
            if k = 0 then Point.Map.add vp false map
            else if k = 1 then Point.Map.add vp true map
            else assert false
          | _ -> assert false) prems Point.Map.empty
      in
      Node map
    in
    Point.Map.add conclp node acc)
  model.entries Point.Map.empty

let pmap_to_point_map table pmap =
  PMap.fold (fun idx v acc ->
    let p = Index.repr idx table in
    Point.Map.add p v acc)
    pmap Point.Map.empty

let valuation_of_model (m : model) =
  let max = model_max m in
  let valm = PMap.map (fun e -> max - entry_value m e) m.entries in
  pmap_to_point_map m.table valm

let valuation { model; _ } = valuation_of_model model

end
