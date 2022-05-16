type constraint_type = Lt | Le | Eq

let debug_loop_checking_invariants, debug_invariants = CDebug.create_full ~name:"loop-checking-invariants" ()
let _debug_loop_checking_model, debug_model = CDebug.create_full ~name:"loop-checking-model" ()
let _debug_loop_checking_clauses, debug_clauses = CDebug.create_full ~name:"loop-checking-clauses" ()
let _debug_loop_checking_flag, debug = CDebug.create_full ~name:"loop-checking" ()
let debug_loop_checking_timing_flag, debug_timing = CDebug.create_full ~name:"loop-checking-timing" ()

module type Point = sig
  type t

  module Set : CSig.SetS with type elt = t
  module Map : CMap.ExtS with type key = t and module Set := Set

  val equal : t -> t -> bool
  val compare : t -> t -> int

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
  fun x y ->
  if CDebug.(get_flag debug_loop_checking_timing_flag) then
    let start = Unix.gettimeofday () in
    let res = f x y in
    let stop = Unix.gettimeofday () in
    let time = stop -. start in
    let () = accum := time +. !accum in
    let () = debug_timing Pp.(fun () -> prefix ++ str " executed in: " ++ Pp.real time ++ str "s") in
    let () = debug_timing Pp.(fun () -> prefix ++ str " total execution time is: " ++ Pp.real !accum ++ str "s") in
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
  fun x y z w ->
  if CDebug.(get_flag debug_loop_checking_timing_flag) then
    let start = Unix.gettimeofday () in
    let res = f x y z w in
    let stop = Unix.gettimeofday () in
    let time = stop -. start in
    let () = accum := time +. !accum in
    let () = debug_timing Pp.(fun () -> prefix ++ str " executed in: " ++ Pp.real time ++ str "s") in
    let () = debug_timing Pp.(fun () -> prefix ++ str " total execution time is: " ++ Pp.real !accum ++ str "s") in
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

type mark = NoMark | Visited

(* Comparison on this type is pointer equality *)
type canonical_node =
  { canon: Index.t;
    value : int;
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

    let equal_upto m (idx, k) (idx', k') =
      Int.equal k k' && repr m idx == repr m idx'
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
  let _add prem (x : t) : t = CList.merge_set Premise.compare [prem] x
  let compare : t -> t -> int = CList.compare Premise.compare
  let equal : t -> t -> bool = CList.equal Premise.equal

  let of_list l = l

  let equal_upto m prems prems' =
    CList.equal (Premise.equal_upto m) prems prems'

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

    let of_list (k, prems) =
      (k, Premises.of_list prems)

    let equal_upto m (k, prems) (k', prems') =
      Int.equal k k' &&
      Premises.equal_upto m prems prems'

    let has_bound m idx (_k, prems) =
      List.exists (fun (l, _) -> (repr m l) == idx) prems

  end

  module S = Set.Make(ClauseInfo)
  include S

  let pr pr_pointint concl cls =
    let open Pp in
    v 0 (prlist_with_sep spc (fun (k, prem) ->
      hov 0 (prlist_with_sep (fun () -> str ",") pr_pointint prem ++ str " → " ++ pr_pointint (concl, k)))
        (elements cls))

  let mem_upto m (cl : ClauseInfo.t) cls =
    let eq cl' = ClauseInfo.equal_upto m cl cl' in
    exists eq cls

  let subset_upto m cls cls' =
    for_all (fun cl -> mem_upto m cl cls') cls

  (* Ocaml >= 4.11 has a more efficient version. *)
  let filter_map p l =
    fold (fun x acc ->
      match p x with
      | None ->  remove x acc
      | Some x' -> if x' == x then acc else add x' (remove x acc)) l l

  let has_bound m idx cls =
    exists (fun cl -> ClauseInfo.has_bound m idx cl) cls

end

type clause_info = (int * Premises.t)
type clauses_info = ClausesOf.t
type clauses = clauses_info PMap.t

(* Invariant: clauses map only canonical points in the model to their clauses *)
type t = {
  model : model;
  clauses : clauses;
}

let clauses_of idx clauses : clauses_info =
  try PMap.find idx clauses
  with Not_found -> ClausesOf.empty

let check_invariants ~(required_canonical:Point.t -> bool) { model; clauses } =
  let required_canonical u = required_canonical (Index.repr u model.table) in
  let n_canon = ref 0 in
  PMap.iter (fun idx e ->
    match e with
    | Canonical can ->
      assert (Index.equal idx can.canon);
      assert (Index.mem (Index.repr idx model.table) model.table);
      assert (can.value >= 0);
      let cls = clauses_of idx clauses in
      ClausesOf.iter
        (fun (k, prems) ->
          assert (k >= 0);
          let check_prem (l, k) =
            assert (k >= 0);
            assert (PMap.mem l model.entries)
          in
          Premises.iter check_prem prems) cls;
      incr n_canon
    | Equiv idx' ->
      assert (PMap.mem idx' model.entries);
      assert (Index.mem (Index.repr idx' model.table) model.table);
      (* The clauses should not mention aliases *)
      assert (not (PMap.mem idx clauses));
      assert (not (required_canonical idx)))
    model.entries;
  (* We don't necessarily have clauses for all levels *)
    assert (PMap.cardinal clauses <= !n_canon)

let clauses_cardinal (cls : clauses) : int =
  PMap.fold (fun _ cls card ->
    ClausesOf.cardinal cls + card)
    cls 0

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

let without_bound (m : model) (cls : clauses) : int =
  PMap.fold (fun _ k acc ->
    match k with Equiv _ -> acc | Canonical can ->
      let cls = clauses_of can.canon cls in
      if ClausesOf.is_empty cls then succ acc else acc)
    m.entries 0

let statistics { model; clauses } =
  let open Pp in
  str" " ++ int (PMap.cardinal model.entries) ++ str" universes" ++
  str", " ++ int (canonical_universes model) ++ str" canonical universes" ++
  str ", maximal value in the model is " ++ int (model_max model) ++
  str ", minimal value is " ++ int (model_min model) ++
  str", " ++ int (clauses_cardinal clauses) ++ str" clauses." ++ spc () ++
  int (without_bound model clauses) ++ str" canonical universes are not bounded above"

let debug_check_invariants model clauses =
  if CDebug.get_flag debug_loop_checking_invariants then
    (debug_invariants Pp.(fun () -> str"Checking invariants, " ++ statistics { model; clauses });
      check_invariants ~required_canonical:(fun _ -> false) { model ; clauses })

(* PMaps are purely functional hashmaps *)

let model_value m l =
  try (repr m l).value
  with Not_found -> 0

let min_premise (m : model) prem =
  let g (l, k) = model_value m l - k in
  let f minl prem = min minl (g prem) in
  Premises.fold f g prem

let update_value (c, w, m) (k, premises) : (canonical_node * PSet.t * model) option =
  let k0 = min_premise m premises in
  if k0 < 0 then None
  else
    let newk = k + k0 in
    if newk <= c.value then None
    else
      let c' = { c with value = newk } in
      Some (c', PSet.add c.canon w, change_node m c')

let pr_can m can =
  Point.pr (Index.repr can.canon m.table)

let check_model_aux (cls : clauses) (w, m) =
  PMap.fold (fun idx cls (modified, w, m) ->
    let can = repr m idx in
    let (can', w', m') =
      ClausesOf.fold (fun cls cwm ->
        match update_value cwm cls with
        | None -> cwm
        | Some (can, _, _ as cwm') ->
          debug Pp.(fun () -> str"Updated value of " ++ pr_can m can ++ str " to " ++ int can.value);
          cwm')
        cls (can, w, m)
    in ((modified || can != can'), w', m'))
  cls (false, w, m)

let check_model cls w m =
  let (modified, w, m') = check_model_aux cls (w, m) in
  debug_check_invariants m cls;
  if modified then Some (w, m') else None

let check_model = time3 (Pp.str "check_model") check_model

let premises_in m w prem =
  Premises.for_all (fun (l, _) -> PSet.mem (repr m l).canon w) prem

let partition_clauses m (cls : clauses) w : clauses * clauses =
  let add_ne concl cls clsm =
    if ClausesOf.is_empty cls then clsm
    else PMap.add concl cls clsm
  in
  PMap.fold (fun concl cls (inl, inr) ->
    let (clsW, clsnW) = ClausesOf.partition (fun kprem -> premises_in m w (snd kprem)) cls in
    (add_ne concl clsW inl, add_ne concl clsnW inr))
  cls (PMap.empty, PMap.empty)

(* let partition_clauses = time3 Pp.(str "partition_clauses") partition_clauses *)

let partition_clauses_concl (cls : clauses) (w : PSet.t) : clauses * clauses =
  PMap.fold (fun concl cls (inl, inr) ->
    if PSet.mem concl w then (PMap.add concl cls inl, PMap.remove concl inr)
    else (inl, inr))
    cls (PMap.empty, cls)

let partition_clauses_concl = time2 Pp.(str "partition_clauses_concl") partition_clauses_concl

type result = Loop | Model of PSet.t * model

let canonical_cardinal m =
  PMap.fold (fun _ e acc ->
    match e with
    | Equiv _ -> acc
    | Canonical _ -> succ acc)
    m.entries 0

let pr_w m w =
  let open Pp in
  prlist_with_sep spc (fun idx -> Point.pr (Index.repr idx m.table)) (PSet.elements w)

let check cls m =
  let cV = canonical_cardinal m in
  let rec inner_loop w m cls =
    let (premconclW, conclW) = partition_clauses m cls w in
    let cardW = PSet.cardinal w in
    debug Pp.(fun () -> str "Inner loop on " ++ int cardW ++ str" universes: " ++ pr_w m w);
    let rec inner_loop_partition w m =
      match loop cardW w m premconclW with
      | Loop -> Loop
      | Model (wr, mr) ->
        debug Pp.(fun () -> str "wr = " ++ pr_w mr wr);
        (match check_model conclW wr mr with
        | Some (wconcl, mconcl) ->
          debug Pp.(fun () -> str "wconcl = " ++ pr_w mr wr);
          inner_loop_partition wconcl mconcl
        | None -> Model (wr, mr))
      in inner_loop_partition w m
  and loop cV u m cls =
    match check_model cls u m with
    | None -> Model (u, m)
    | Some (w, m) ->
      if Int.equal (PSet.cardinal w) cV
      then Loop
      else
        let conclW, conclnW = partition_clauses_concl cls w in
        (match inner_loop w m conclW with
        | Loop -> Loop
        | Model (wc, mc) ->
          (match check_model conclnW wc mc with
          | None -> Model (wc, mc)
          | Some (wcls, mcls) -> loop cV wcls mcls cls))
  in
  let res = loop cV PSet.empty m cls in
  (* unset_marks m; *)
  res


let check cls m =
  debug Pp.(fun () -> str"Calling loop-checking");
  try let res = check cls m in
    debug Pp.(fun () -> str"Loop-checking terminated");
    res
  with Stack_overflow ->
    CErrors.anomaly (Pp.str "check raised a stack overflow")

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

let update_model_value (m : model) l k' : model =
  let can = repr m l in
  let k' = max can.value k' in
  if Int.equal k' can.value then m
  else change_node m { can with value = k' }

let update_model (cls : clauses) (m : model) : model =
  PMap.fold (fun _concl cls m ->
    ClausesOf.fold (fun (_k, prems) m ->
      List.fold_left (fun m (l, k) -> update_model_value m l k) m prems)
      cls m)
    cls m

let pr_index_point m idx =
  let point = Index.repr idx m.table in
  Point.pr point

let pr_pointint m = pr_with (pr_index_point m)

let pr_clauses_info m = ClausesOf.pr (pr_pointint m)

let pr_clauses m (cls : clauses) =
  let open Pp in
  PMap.fold (fun concl cls acc -> pr_clauses_info m concl cls ++ spc () ++ acc) cls (Pp.mt())

let debug_model m =
  debug_model Pp.(fun () -> str"Model is " ++ pr_levelmap m)

(* let model_remove idx (m : model) =
  { entries = PMap.remove idx m.entries; table = m.table } *)


(* Filters the set of clauses to remove those of shape [l + k -> l' + k] where
  [l] itself does not have any constraint [... -> l + k], hence can not be updated. *)
(* let filter_with_bound (m : model) (cls : clauses) : clauses  =
  let unbounded =
    PMap.fold (fun _ k unbounded ->
    match k with Equiv _ -> unbounded | Canonical can ->
      let cancls = clauses_of can.canon cls in
      if ClausesOf.is_empty cancls then PSet.add can.canon unbounded
      else unbounded)
    m.entries PSet.empty
  in
  PMap.fold (fun concl clsc cls ->
    let clsc' = ClausesOf.filter (fun (_, prems) -> not (premises_in m unbounded prems)) clsc in
    if clsc' == clsc then cls
    else PMap.add concl clsc' cls)
    cls cls

let filter_with_bound = time2 (Pp.str"Filtering clauses") filter_with_bound *)

let infer_clauses_extension (model : model) (clauses : clauses) =
  debug_check_invariants model clauses;
  let model = update_model clauses model in
  debug_check_invariants model clauses;
  debug Pp.(fun () -> str"Calling loop-checking" ++ statistics { model; clauses });
  (* let filtered_clauses = filter_with_bound model clauses in *)
  (* debug Pp.(fun () -> str"Filtered clauses " ++ int (clauses_cardinal filtered_clauses)); *)
  match check clauses model with
  | Loop -> None
  | Model (_w', model) ->
    let m = { model; clauses } in
    debug_check_invariants model clauses;
    debug_model model;
    Some m

let check_clause m conclv (k, prem) =
  let k0 = min_premise m prem in
  if k0 < 0 then false (* We do not allow vacuously true constraints *)
  else
    let newk = k + k0 in
     if newk <= conclv then true
     else false

let check_clauses m (cls : clauses) =
  PMap.for_all (fun concl cls ->
    let conclv = model_value m concl in
    ClausesOf.for_all (fun cl -> check_clause m conclv cl) cls)
    cls

let empty_clauses = PMap.empty
let empty = { model = empty_model; clauses = empty_clauses }

let add_clause_aux can kprem clauses =
  PMap.update can.canon
      (fun cls ->
        match cls with
        | None -> Some (ClausesOf.singleton kprem)
        | Some cls -> Some (ClausesOf.add kprem cls))
      clauses

let filter_trivial_clause m canl ((k, prems) as kprems) =
  let prems' = filter_map_same (fun (l', k' as x) ->
    let canl' = repr m l' in
    if canl' == canl && k' >= k then None
    else if Index.equal l' canl'.canon then Some x
    else Some (canl'.canon, k')) prems
  in
  match prems' with
  | [] -> None
  | _ ->
    if prems' == prems then Some kprems
    else Some (k, prems')

let filter_trivial_pclause m canl (k, prems) =
  let prems = List.filter_map (fun (l', k') ->
    let canl' = repr_node m l' in
    if canl' == canl && k' >= k then None
    else Some (canl'.canon, k')) prems in
  match prems with
  | [] -> None
  | prems -> Some (k, prems)

let add_clause (m : model) l kprem (cls : clauses) : clauses =
  let canl = repr_node m l in
  match filter_trivial_pclause m canl kprem with
  | None -> cls
  | Some kprem ->
    let kprem = ClausesOf.ClauseInfo.of_list kprem in
    if ClausesOf.mem_upto m kprem (clauses_of canl.canon cls) then cls
    else add_clause_aux canl kprem cls


let filter_trivial_can_clause canl ((k, prems) as kprems) =
  let prems' = CList.filter (fun (l', k') -> not (Index.equal l' canl.canon && k' >= k)) prems in
  match prems' with
  | [] -> None
  | _ ->
    if prems' == prems then Some kprems
    else Some (k, prems')


let add_can_clause (m : model) canl kprem (cls : clauses) : clauses =
  match filter_trivial_can_clause canl kprem with
  | None -> cls
  | Some kprem ->
    let kprem = ClausesOf.ClauseInfo.of_list kprem in
    if ClausesOf.mem_upto m kprem (clauses_of canl.canon cls) then cls
    else add_clause_aux canl kprem cls


let add_clauses_aux can kprem clauses =
  PMap.update can.canon
    (fun cls ->
    match cls with
    | None -> Some kprem
    | Some cls -> Some (ClausesOf.union kprem cls))
    clauses

let add_clauses (m : model) canl kprem (cls : clauses) : clauses =
  let kprem = ClausesOf.filter_map (filter_trivial_clause m canl) kprem in
  if ClausesOf.subset_upto m kprem (clauses_of canl.canon cls) then cls
  else add_clauses_aux canl kprem cls

type pclause_info = (int * (Point.t * int) list)

let _to_clause_info m (k, prems : pclause_info) : clause_info =
  let trans_prem (p, k) =
    let can = repr_node m p in
    (can.canon, k)
  in
  (k, List.map trans_prem prems)

(* max u_i <= v <-> ∧_i u_i <= v *)
let clauses_of_le_constraint (m : model) u v cls : clauses =
  List.fold_left (fun cls (u, k) -> add_clause m u (k, v) cls) cls u

let _check_leq (m : t) u v =
  let cls = clauses_of_le_constraint m.model u v empty_clauses in
  check_clauses m.model cls

let _is_bound (m : model) can cano (cls : clauses) : bool =
  PMap.exists (fun concl clsc ->
    if Index.equal concl can.canon then false
    else ClausesOf.has_bound m cano clsc) cls

(* Precondition: canu.value == canv.value, so no new model needs to be computed *)
let enforce_eq_can { model; clauses } canu canv : canonical_node * t =
  assert (canu.value == canv.value);
  (* v := u *)
  let can, other, model =
    canu, canv.canon, enter_equiv model canv.canon canu.canon
  in
  let clauses =
    match PMap.find other clauses with
    | clsother ->
      let clauses' = add_clauses model can clsother clauses in
      PMap.remove other clauses'
    | exception Not_found -> clauses
  in
  debug_check_invariants model clauses;
  can, { model; clauses }

let _enforce_eq_indices (m : t) u v =
  let canu = repr m.model u in
  let canv = repr m.model v in
  if canu == canv then m
  else snd (enforce_eq_can m canu canv)

let pr_can_constraints m can =
  let cls = clauses_of can.canon m.clauses in
  pr_clauses_info m.model can.canon cls

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
    debug Pp.(fun () -> str"Chosen canonical universe: " ++ pr_can m.model can ++ spc () ++
      str"Constraints:" ++ pr_can_constraints m can);
    m
  | _ -> assert false

let simplify_clauses_between ({ model; clauses } as m) v u =
  let canv = repr model v in
  let canu = repr model u in
  if canv == canu then Some m else
  let rec forward prev acc visited canv : canonical_node list * canonical_node list =
    if canv.mark == Visited then acc, visited else
    let () = canv.mark <- Visited in
    let visited = canv :: visited in
    let cls = clauses_of canv.canon clauses in
    ClausesOf.fold (fun (k, prems) acc ->
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


let clauses_of_univ_constraint (m : t) (cstr : univ_constraint) clauses : clauses =
  let (l, k, r) = cstr in (* l + k <= r *)
  match k with
  | Le -> add_clause m.model l (0, [(r, 0)]) clauses
  | Lt -> add_clause m.model l (1, [(r, 0)]) clauses
  | Eq -> add_clause m.model l (0, [(r, 0)]) (add_clause m.model r (0, [(l, 0)]) clauses)

let clauses_of_can_constraint (m : t) (cstr : can_constraint) clauses : clauses =
  let (l, k, r) = cstr in (* l + k <= r *)
  add_can_clause m.model l (k, [(r.canon, 0)]) clauses

let enforce_clauses_of_can_constraint (cstr : can_constraint) ({ model; clauses } as m) : bool * t =
  let (l, k, r) = cstr in (* l + k <= r *)
  let clauses' = add_can_clause m.model l (k, [(r.canon, 0)]) clauses in
  if clauses' == clauses then false, m
  else true, { model; clauses = clauses' }

let enforce_clauses_of_can_constraint =
  time2 (Pp.str "Enforcing clauses") enforce_clauses_of_can_constraint

type 'a check_function = t -> 'a -> 'a -> bool

let check_lt (m : t) u v =
  let cls = clauses_of_univ_constraint m (u, Lt, v) empty_clauses in
  check_clauses m.model cls

let check_leq (m : t) u v =
  let cls = clauses_of_univ_constraint m (u, Le, v) empty_clauses in
  check_clauses m.model cls

let check_eq m u v =
  let cls = clauses_of_univ_constraint m (u, Eq, v) empty_clauses in
  check_clauses m.model cls

let infer_extension x k y m =
  debug Pp.(fun () -> str"Enforcing constraint " ++ pr_with (pr_can m.model) (x, k) ++ str " ≤ " ++ pr_can m.model y);
  (* debug Pp.(fun () -> str "current model is: " ++ pr_levelmap m.model); *)
  debug_check_invariants m.model m.clauses;
  debug Pp.(fun () ->
    let newcls = clauses_of_can_constraint m (x, k, y) empty_clauses in
    str"Enforcing clauses " ++ pr_clauses m.model newcls);
  let clauses = clauses_of_can_constraint m (x, k, y) empty_clauses in
  if check_clauses m.model clauses then begin
    (* The clauses are already true in the current model,
       but might not be in an extension, so we add them still *)
    debug Pp.(fun () -> str"Clause is valid in the current model");
    let _recheck, m = enforce_clauses_of_can_constraint (x, k, y) m in
    (* If the clauses were already present in the set of clauses of [m],
      then it will be unchanged, physically *)
    if CDebug.(get_flag debug_loop_checking_invariants) then
      assert (check_clauses m.model clauses);
    debug_clauses Pp.(fun () -> str"Clauses: " ++ pr_clauses m.model m.clauses);
    Some m
  end else
    (* The clauses are not valid in the current model, we have to find a new one *)
    let check, m = enforce_clauses_of_can_constraint (x, k, y) m in
    if check then begin
      debug Pp.(fun () -> str"Enforcing clauses requires a new inference");
      match infer_clauses_extension m.model m.clauses with
      | None ->
        debug Pp.(fun () -> str"Enforcing clauses " ++ pr_clauses m.model clauses ++ str" resulted in a loop");
        None
      | Some _ as x -> x end
    else ((* No need to update the model *)
      debug Pp.(fun () -> str"Enforcing clauses " ++ pr_clauses m.model clauses ++ str" did not change the model");
      Some m)

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
  else match Int.compare canu.value canv.value with
    | 0 -> Some (snd (enforce_eq_can m canu canv))
    | x when x < 0 ->
      (* canu.value <= canv.value, so v <= u is trivial.
         The first enforce will be fast, the second can involve an inference *)
      Option.bind (enforce_leq_can canv canu m)
        (fun m' -> enforce_leq_can (repr m'.model canu.canon) (repr m'.model canv.canon) m')
    | _ ->
      (* canv.value <= canu.value, so u <= v is trivial.
          The first enforce will be fast, the second can involve an inference *)
      Option.bind (enforce_leq_can canu canv m)
        (fun m' -> enforce_leq_can (repr m'.model canv.canon) (repr m'.model canu.canon) m')

type lub = (Point.t * int) list

let clauses_of_constraint m (u : lub) k (v : lub) cls =
  match k with
  | Le -> clauses_of_le_constraint m u v cls
  | Lt -> clauses_of_le_constraint m (List.map (fun (l, k) -> (l, k + 1)) u) v cls
  | Eq -> clauses_of_le_constraint m u v (clauses_of_le_constraint m v u cls)

let enforce_constraint u k v (m : t) =
  let cls = clauses_of_constraint m.model u k v empty_clauses in
  infer_clauses_extension m.model cls

exception AlreadyDeclared

let add_model u { entries; table } =
  if Index.mem u table then raise AlreadyDeclared
  else
    let idx, table = Index.fresh u table in
    let can = Canonical { canon = idx; value = 0; mark = NoMark } in
    let entries = PMap.add idx can entries in
    idx, { entries; table }

let add ?(rank:int option) u { model; clauses } =
  let _r = rank in
  debug Pp.(fun () -> str"Declaring level " ++ Point.pr u);
  let _idx, model = add_model u model in
  { model; clauses }

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
let constraints_of_clauses m (clauses : clauses) =
  PMap.fold (fun concl cls cstrs ->
    let conclp = Index.repr concl m.table in
    ClausesOf.fold (fun (k, prems) cstrs ->
      match prems with
      | [(v, 0)] ->
        let vp = Index.repr v m.table in
        if k = 0 then Constraints.add (conclp, Le, vp) cstrs
        else if k = 1 then Constraints.add (conclp, Lt, vp) cstrs
        else assert false
      | _ -> assert false) cls cstrs)
    clauses Constraints.empty

let constraints_of { model; clauses } fold acc =
  let module UF = Unionfind.Make (Point.Set) (Point.Map) in
  let uf = UF.create () in
  let constraints_of u v =
    match v with
    | Canonical _ -> ()
    | Equiv v ->
      let u = Index.repr u model.table in
      let v = Index.repr v model.table in
      UF.union u v uf
  in
  let cstrs = constraints_of_clauses model clauses in
  let () = PMap.iter constraints_of model.entries in
  Constraints.fold fold cstrs acc, UF.partition uf

type 'a constraint_fold = Point.t * constraint_type * Point.t -> 'a -> 'a

let constraints_for ~(kept:Point.Set.t) { model; clauses } (fold : 'a constraint_fold) (accu : 'a) =
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
        let cls = clauses_of v.canon clauses in
        (* v is not equal to any kept point *)
        let todo =
          ClausesOf.fold (fun (k', prems') todo -> (prems', k + k') :: todo)
            cls todo
        in
        add_from u csts todo)
  in
  PSet.fold (fun u csts ->
      let arc = repr model u in
      let cls = clauses_of arc.canon clauses in
      ClausesOf.fold (fun (k, prems) csts -> add_from u csts [prems,k]) cls csts)
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
let repr { clauses; model } =
  PMap.fold (fun idx e acc ->
    let conclp = Index.repr idx model.table in
    let node = match e with
    | Equiv idx -> Alias (Index.repr idx model.table)
    | Canonical can ->
      let prems = clauses_of can.canon clauses in
      let map =
        ClausesOf.fold (fun (k, prem) map ->
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


(*
let clauses_of_constraints cstr =
  Univ.Constraints.fold clauses_of_can_constraint cstr Point.Map.empty


let initial_universes =
  { model = Point.Map.add Level.set 0 Point.Map.empty;
    clauses = empty_clauses;
    points = Point.Set.singleton Level.set }

let infer_cstrs_extension m (cstrs : Constraints.t) =
  let cls = clauses_of_constraints cstrs in
  infer_clauses_extension m cls

let check_constraints ((points, cstrs) : Univ.ContextSet.t) : unit =
  let clauses = time (Pp.str "Building clauses out of constraints") clauses_of_constraints cstrs in
  let m = update_model clauses Point.Map.empty in
  match time (Pp.str "Checking for a model") (check points clauses) m with
  | Loop -> Feedback.msg_info Pp.(str "found a loop")
  | Model (_w, _m) -> Feedback.msg_info Pp.(str "found a model")

    (* match check_model clauses Point.Set.empty m with
    | None -> Feedback.msg_info Pp.(str"Model is " ++ pr_levelmap m)
    | Some _ -> Feedback.msg_info Pp.(str"Not actually a model!") *)
*)
