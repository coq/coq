type constraint_type = Lt | Le | Eq

let debug_loop_checking_invariants, debug_invariants = CDebug.create_full ~name:"loop-checking-invariants" ()
let _debug_loop_checking_model, debug_model = CDebug.create_full ~name:"loop-checking-model" ()
let _debug_loop_checking_clauses, _debug_clauses = CDebug.create_full ~name:"loop-checking-clauses" ()
(* let _debug_loop_checking_bwdclauses, debug_bwdclauses = CDebug.create_full ~name:"loop-checking-bwdclauses" () *)
let _debug_loop_checking_flag, debug = CDebug.create_full ~name:"loop-checking" ()
let debug_loop_checking_timing_flag, debug_timing = CDebug.create_full ~name:"loop-checking-timing" ()
let _debug_loop_checking_loop, debug_loop = CDebug.create_full ~name:"loop-checking-loop" ()
let _debug_loop_checking_check_model, debug_check_model = CDebug.create_full ~name:"loop-checking-check-model" ()
let _debug_loop_checking_check, debug_check = CDebug.create_full ~name:"loop-checking-check" ()

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
    val hash : t -> int
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

    let hash x = x
  end

module PMap = Index.Map
module PSet = Index.Set

type univ_constraint = Point.t * constraint_type * Point.t

module NeList =
struct

  type 'a t =
    | Tip of 'a
    | Cons of 'a * 'a t

  let tip x = Tip x
  (* let cons x xs = Cons (x, xs) *)

  let map f (x : 'a t) : 'b t =
    let rec aux l =
      match l with
      | Tip x -> Tip (f x)
      | Cons (x, xs) ->
        let x' = f x in
        let xs' = aux xs in
        Cons (x', xs')
    in aux x

  let smart_map f (x : 'a t) : 'a t =
    let rec aux l =
      match l with
      | Tip x -> let x' = f x in if x' == x then l else Tip x'
      | Cons (x, xs) -> let x' = f x in
        let xs' = aux xs in
        if x' == x && xs' == xs then l
        else Cons (x', xs')
    in aux x

  let fold (f : 'a -> 'b -> 'b) (x : 'a t) (acc : 'b) : 'b =
    let rec aux acc l =
      match l with
      | Tip x -> f x acc
      | Cons (hd, tl) -> aux (f hd acc) tl
    in aux acc x

  let fold_ne (f : 'a -> 'b -> 'b) (g : 'a -> 'b) (x : 'a t) : 'b =
    let rec aux l =
      match l with
      | Tip x -> g x
      | Cons (hd, tl) -> f hd (aux tl)
    in aux x

  let fold_map (f : 'a -> 'b -> 'a * 'b) (x : 'a t) (acc : 'b) : 'a t * 'b =
    let rec aux acc l =
      match l with
      | Tip x -> let x', res = f x acc in Tip x', res
      | Cons (hd, tl) -> let hd', res = f hd acc in
        let tl', res = aux res tl in
        Cons (hd', tl'), res
    in aux acc x

  let iter f x =
    let rec aux l =
      match l with
      | Tip x -> f x
      | Cons (hd, tl) -> f hd; aux tl
    in aux x

  let for_all f x =
    let rec aux l =
      match l with
      | Tip x -> f x
      | Cons (hd, tl) -> f hd && aux tl
    in aux x

  let exists f x =
    let rec aux l =
      match l with
      | Tip x -> f x
      | Cons (hd, tl) -> f hd || aux tl
    in aux x

  let equal f x y =
    let rec aux l l' =
      match l, l' with
      | Tip x, Tip y -> f x y
      | Cons _, Tip _ -> false
      | Tip _, Cons _ -> false
      | Cons (hd, tl), Cons (hd', tl') ->
        f hd hd' && aux tl tl'
    in aux x y

  let compare f x y =
    let rec aux l l' =
      match l, l' with
      | Tip x, Tip y -> f x y
      | Cons _, Tip _ -> 1
      | Tip _, Cons _ -> -1
      | Cons (hd, tl), Cons (hd', tl') ->
        match f hd hd' with
        | 0 -> aux tl tl'
        | c -> c
    in aux x y

  let rec of_list = function
    | [] -> assert false
    | [hd] -> Tip hd
    | hd :: tl -> Cons (hd, of_list tl)

  let rec to_list = function
    | Tip hd -> [hd]
    | Cons (hd, tl) -> hd :: to_list tl

  let filter_map_same f l =
    let rec aux l =
      match l with
      | Tip hd ->
        begin match f hd with
        | None -> None
        | Some hd' -> if hd == hd' then Some l else Some (Tip hd')
        end
      | Cons (hd, tl) ->
        match f hd with
        | Some hd' ->
          let tl' = aux tl in
          begin match tl' with
            | None -> Some (Tip hd')
            | Some tl' ->
              if hd == hd' && tl == tl' then Some l
              else Some (Cons (hd', tl'))
            end
        | None -> aux tl
    in aux l

  let _mem_assq x = exists (fun y -> fst y == x)

  let _assq x l =
    let rec aux l =
      match l with
      | Tip (hd, v) -> if hd == x then v else raise_notrace Not_found
      | Cons ((hd, v), tl) ->
        if hd == x then v else aux tl
    in aux l

  let _find f l =
    let rec aux l =
      match l with
      | Tip (hd, v) -> if f hd then v else raise_notrace Not_found
      | Cons ((hd, v), tl) ->
        if f hd then v else aux tl
    in aux l

  let _head x =
    match x with
    | Tip hd -> hd
    | Cons (hd, _) -> hd

  let pr_with_sep sep prelt =
    let open Pp in
    let rec aux l =
      match l with
      | Tip x -> prelt x
      | Cons (hd, tl) -> prelt hd ++ sep () ++ aux tl
    in aux

  let filter p l =
    let rec aux l =
      match l with
      | Tip x -> if p x then Some l else None
      | Cons (hd, tl) ->
        let phd = p hd in
        match aux tl with
        | None -> if phd then Some (Tip hd) else None
        | Some tl' ->
          if phd then
            if tl == tl' then Some l
            else Some (Cons (hd, tl'))
          else Some tl'
    in aux l
end

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
  type t = Premise.t NeList.t

  let fold = NeList.fold

  let fold_ne = NeList.fold_ne

  let iter = NeList.iter
  let for_all = NeList.for_all
  let _exists = NeList.exists
  (* let _add prem (x : t) : t = CList.merge_set Premise.compare [prem] x *)
  (* let _union (x : t) (y : t) : t = CList.merge_set Premise.compare x y *)
  let compare : t -> t -> int = NeList.compare Premise.compare
  let equal : t -> t -> bool = NeList.equal Premise.equal

  (* let of_list = NeList.of_list *)

  let to_list = NeList.to_list

  let smart_map = NeList.smart_map
  let _map = NeList.map


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

    (* let of_list (k, prems) = (k, Premises.of_list prems) *)

    let pr pr_pointint concl (k, prem) =
      let open Pp in
      hov 0 (prlist_with_sep (fun () -> str ",") pr_pointint (Premises.to_list prem) ++ str " → " ++ pr_pointint (concl, k))
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

(* Comparison on this type is pointer equality *)
type canonical_node =
  { canon: Index.t;
    clauses_bwd : ClausesOf.t; (* premises -> canon + k *)
    clauses_fwd : ClausesOf.t PMap.t (* canon + k, ... ->  concl + k' *) }

(* A Point.t is either an alias for another one, or a canonical one,
    for which we know the points that are above *)

type entry =
  | Canonical of canonical_node
  | Equiv of Index.t

type model = {
  entries : entry PMap.t;
  values : int PMap.t;
  canonical : int; (* Number of canonical nodes *)
  table : Index.table }

let empty_model = {
  entries = PMap.empty;
  values = PMap.empty;
  canonical = 0;
  table = Index.empty
}

module CN = struct
  type t = canonical_node
  let equal x y = x == y
  let hash x = Index.hash x.canon
end

module Status = struct
  module Internal = Hashtbl.Make(CN)

  (** we could experiment with creation size based on the size of [g] *)
  let create (_m:model) = Internal.create 17

  let _mem = Internal.mem
  let find = Internal.find
  let replace = Internal.replace
  let fold = Internal.fold
end


let enter_equiv m u v =
  { entries = PMap.modify u (fun _ a ->
          match a with
          | Canonical _ -> Equiv v
          | _ -> assert false) m.entries;
    canonical = m.canonical - 1;
    values = PMap.remove u m.values;
    table = m.table }

let change_equiv entries u v =
  PMap.modify u (fun _ a ->
      match a with
      | Canonical _ -> assert false
      | Equiv _ -> Equiv v) entries

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

(* canonical representative with path compression : we follow the Equiv links
  and updated them as needed *)
let repr_compress_entries entries u =
  let rec aux u =
    match PMap.find u entries with
    | Equiv v ->
      let entries, can = aux v in
      if Index.equal v can.canon then entries, can
      else change_equiv entries u can.canon, can
    | Canonical can -> entries, can
  in aux u

let repr_compress m u =
  let entries, can = repr_compress_entries m.entries u in
  { m with entries }, can

let repr_node m u =
  try repr m (Index.find u m.table)
  with Not_found ->
    CErrors.anomaly ~label:"Univ.repr"
      Pp.(str"Universe " ++ Point.pr u ++ str" undefined.")

let repr_compress_node m u =
  try repr_compress m (Index.find u m.table)
  with Not_found ->
    CErrors.anomaly ~label:"Univ.repr"
      Pp.(str"Universe " ++ Point.pr u ++ str" undefined.")

let pr_index_point m idx =
  let idx = try (repr m idx).canon with Not_found -> idx in
  try Point.pr (Index.repr idx m.table)
  with Not_found -> Pp.str"<point not in table>"

let pr_pointint m = pr_with (pr_index_point m)

let _pr_clause_info m concl cl = ClausesOf.ClauseInfo.pr (pr_pointint m) concl cl

let pr_clauses_of m = ClausesOf.pr (pr_pointint m)

let repr_premise m (idx, k as x) =
  let idx' = (repr m idx).canon in
  if Index.equal idx idx' then x
  else (idx', k)

let repr_premises m (x : Premises.t) : Premises.t =
  Premises.smart_map (repr_premise m) x

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
    NeList.equal (premise_equal_upto m) prems prems'

  let premises_equal_upto m (k, prems) (k', prems') =
    k <= k' &&
    premises_equal_upto m prems prems'

  let mem_upto m (cl : ClauseInfo.t) cls =
    let eq cl' = premises_equal_upto m cl cl' in
    exists eq cls

  let subset_upto m cls cls' =
    for_all (fun cl -> mem_upto m cl cls') cls

  let filter_trivial_clause m l ((k, prems) as kprems) =
    let prems' = NeList.filter_map_same (fun (l', k' as x) ->
      let canl' = repr m l' in
      if Index.equal canl'.canon l && k' >= k then None
      else if Index.equal l' canl'.canon then Some x
      else Some (canl'.canon, k')) prems
    in
    match prems' with
    | None -> None
    | Some prems' ->
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
  let is_empty = PMap.is_empty

  let singleton cl = add cl empty

  let fold = PMap.fold


  let find idx clauses : ClausesOf.t =
    try PMap.find idx clauses
    with Not_found -> ClausesOf.empty

  let _add_upto (m : model) (l, kprem as cl : clause) (cls : t) : t =
    if ClausesOfRepr.subset_upto m kprem (find l cls) then cls
    else add cl cls

  let reindex m (clauses : t) : t =
    PMap.fold (fun idx clsof acc ->
      let idx' = (repr m idx).canon in
      if Index.equal idx' idx then acc
      else PMap.remove idx (PMap.add idx' clsof acc))
      clauses clauses

  let union_upto (m : model) (clauses : t) (clauses' : t) : t =
    let merge idx cls cls' =
      match cls, cls' with
      | None, None -> cls
      | None, Some _ -> cls'
      | Some _, None -> cls
      | Some cls, Some cls' ->
        Some (ClausesOfRepr.union_upto m idx cls cls')
    in
    PMap.merge merge (reindex m clauses) (reindex m clauses')

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

let _pr_clause_info m ((concl, kprem) : clause) =
  pr_clauses_of m concl kprem

type t = model

let check_invariants ~(required_canonical:Point.t -> bool) model =
  let required_canonical u = required_canonical (Index.repr u model.table) in
  let n_canon = ref 0 in
  PMap.iter (fun idx e ->
    match e with
    | Canonical can ->
      assert (Index.equal idx can.canon);
      assert (Index.mem (Index.repr idx model.table) model.table);
      assert (PMap.mem idx model.values);
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
            NeList.exists (fun (idx', _) -> can == repr model idx') prems) kprems) can.clauses_fwd);
      incr n_canon
    | Equiv idx' ->
      assert (PMap.mem idx' model.entries);
      assert (Index.mem (Index.repr idx' model.table) model.table);
      (* The clauses should not mention aliases *)
      assert (not (required_canonical idx)))
    model.entries

let lift_opt f x y =
  match x, y with
  | Some x', Some y' -> Some (f x' y')
  | Some _, None -> x
  | None, Some _ -> y
  | None, None -> None

let max_opt = lift_opt max
let min_opt = lift_opt min

let model_max (m : model) : int option =
  PMap.fold (fun _ v acc -> max_opt (Some v) acc) m.values None

let model_min (m : model) : int option =
  PMap.fold (fun _ v acc -> min_opt (Some v) acc) m.values None

let clauses_cardinal (m : model) : int =
  PMap.fold (fun _ k acc ->
    match k with Equiv _ -> acc | Canonical can -> acc + ClausesOf.cardinal can.clauses_bwd)
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

let length_path_from m idx =
  let rec aux = function
    | Canonical _ -> 0
    | Equiv idx -> succ (aux (PMap.find idx m))
  in aux (PMap.find idx m)

let maximal_path m =
  PMap.fold (fun _ entry acc ->
    match entry with
    | Equiv idx -> max (succ (length_path_from m idx)) acc
    | Canonical _ -> acc) m 0

let statistics model =
  let open Pp in
  str" " ++ int (PMap.cardinal model.entries) ++ str" universes" ++
  str", " ++ int (canonical_universes model) ++ str" canonical universes" ++
  str ", maximal value in the model is " ++ pr_opt int (model_max model) ++
  str ", minimal value is " ++ pr_opt int (model_min model) ++
  str", " ++ int (clauses_cardinal model) ++ str" clauses." ++ spc () ++
  int (without_bound model) ++ str" canonical universes are not bounded above " ++
  str", " ++ int (maximal_path model.entries) ++ str" maximal path length in equiv nodes"

let debug_check_invariants m =
  if CDebug.get_flag debug_loop_checking_invariants then
    (debug_invariants Pp.(fun () -> str"Checking invariants, " ++ statistics m);
      check_invariants ~required_canonical:(fun _ -> false) m)

(* PMaps are purely functional hashmaps *)

exception Undeclared of Point.t

let canonical_value m c = PMap.find_opt c.canon m.values

let set_canonical_value m c v =
  { m with values = PMap.add c.canon v m.values }

let model_value m l =
  let canon =
    try repr m l
    with Not_found -> raise (Undeclared (Index.repr l m.table))
  in canonical_value m canon

exception VacuouslyTrue

let min_premise (m : model) prem =
  let g (l, k) = (match (model_value m l) with None -> raise VacuouslyTrue | Some v -> v) - k in
  let f prem minl = min minl (g prem) in
  Premises.fold_ne f g prem

module CanSet =
struct
  type t = (ClausesOf.t * ClausesBackward.t) PMap.t * int (* cardinal of the PMap.t *)

  let fold f (m, _cm)  acc = PMap.fold f m acc

  let add k v (w, cw) = (PMap.add k v w, succ cw)

  let singleton k v = (PMap.singleton k v, 1)

  let mem x (w, _cw) = PMap.mem x w

  let empty = (PMap.empty, 0)

  let is_empty (w, _cw) = PMap.is_empty w

  let cardinal (_w, cw : t) = cw

  let update idx f (w, cw as x) =
    let cwr = ref cw in
    let w' =
      PMap.update idx (fun old ->
        let n = f old in
        match old, n with
        | None, None -> None
        | None, Some _ -> incr cwr; n
        | Some _, None -> cwr := !cwr - 1; None
        | Some _, Some _ -> n)
        w
    in
    if w == w' then x else (w', !cwr)

  let pr m (w, _) =
    let open Pp in
    prlist_with_sep spc (fun (idx, _) -> Point.pr (Index.repr idx m.table)) (PMap.bindings w)

  let pr_clauses m (w, _) =
    let open Pp in
    prlist_with_sep spc (fun (idx, (bwd, fwd)) ->
      Point.pr (Index.repr idx m.table) ++ str": " ++ spc () ++
      str" Backward clauses " ++ pr_clauses_of m idx bwd ++
      str" Forward clauses " ++ pr_clauses_bwd m fwd)
      (PMap.bindings w)


  let _domain (w, _) = PMap.domain w

  (* let _of_pset model w = PSet.fold (fun idx -> *)
    (* let can = repr model idx in *)
    (* add can.canon (can.clauses_bwd, can.clauses_fwd)) w empty *)

  (* Right-biased union *)
  let _union (w, c) (w', _) =
    let card = ref c in
    let merge _idx cls cls' =
      match cls, cls' with
      | None, None -> cls
      | _, Some _ -> incr card; cls'
      | Some _, None -> cls
    in
    let union = PMap.merge merge w w' in
    (union, !card)

end

let pr_w m w = CanSet.pr m w

exception FoundImplication

let update_value check_early_stop c m clause : model option =
  let (k, premises) = clause in
  match min_premise m premises with
  | exception VacuouslyTrue -> None
  | k0 when k0 < 0 -> None
  | k0 ->
    let newk = k + k0 in
    match canonical_value m c with
    | Some v when newk <= v -> None
    | _ ->
      check_early_stop newk;
      Some (set_canonical_value m c newk)

let pr_can m can =
  Point.pr (Index.repr can.canon m.table)

let check_model_clauses_of_aux check_early_stop m can cls =
  ClausesOf.fold (fun cls m ->
    match update_value check_early_stop can m cls with
    | None -> m
    | Some m' ->
      debug Pp.(fun () -> str"Updated value of " ++ pr_can m can ++ str " to " ++ pr_opt int (canonical_value m' can));
      debug Pp.(fun () -> str" due to clause " ++ pr_clauses_bwd m (ClausesBackward.singleton (can.canon, ClausesOf.singleton cls)));
      m')
    cls m

(** Check a set of forward clauses *)
let check_model_fwd_clauses_aux ?early_stop (cls : ClausesBackward.t) (acc : PSet.t * (CanSet.t * model)) : PSet.t * (CanSet.t * model) =
  PMap.fold (fun concl cls (* premises -> concl + k *) (modified, (w, m) as acc) ->
    let can = repr m concl in
    let check_early_stop =
      match early_stop with
      | None -> fun _ -> ()
      | Some (can', k) ->
        if can == can' then fun k' -> if k <= k' then raise FoundImplication else ()
        else fun _ -> ()
    in
    let m' = check_model_clauses_of_aux check_early_stop m can cls in
    if m == m' then (* not modifed *) acc
    else
      let upd = function
        | None -> Some (can.clauses_bwd, can.clauses_fwd)
        | Some _ -> Some (can.clauses_bwd, can.clauses_fwd)
      in
      let w' = CanSet.update can.canon upd w in
      (PSet.add can.canon modified, (w', m')))
    cls acc

let check_model_fwd_aux ?early_stop w (cls, m) : PSet.t * (CanSet.t * model) =
  CanSet.fold (fun _ (_, fwd) acc -> check_model_fwd_clauses_aux ?early_stop fwd acc) cls
    (PSet.empty, ((if PSet.is_empty w then CanSet.empty else cls), m))

let check_clauses_with_premises ?early_stop (w : PSet.t) (updates : CanSet.t) model : (PSet.t * (CanSet.t * model)) option =
  let (modified, (cls, m)) = check_model_fwd_aux ?early_stop w (updates, model) in
  if PSet.is_empty modified then (debug Pp.(fun () -> str"Found a model"); None)
  else Some (PSet.union w modified, (cls, m))

(* let _check_model_bwd = check_model *)
let cardinal_fwd w =
  CanSet.fold (fun _idx (_, fwd) acc -> ClausesBackward.cardinal fwd + acc) w 0

let check_clauses_with_premises ?early_stop w (updates : CanSet.t) model : (PSet.t * (CanSet.t * model)) option =
  let open Pp in
  debug_check_model (fun () -> str"check_model on " ++ int (CanSet.cardinal updates) ++ str" universes, " ++
  int (cardinal_fwd updates) ++ str " clauses");
  check_clauses_with_premises ?early_stop w updates model

(*let check_clauses_with_premises = time3 (Pp.str"check_clauses_with_premises") check_clauses_with_premises*)

(* let check_model = time3 (Pp.str "check_model") check_model *)

type 'a result = Loop | Model of 'a * model

let canonical_cardinal m = m.canonical

let can_all_premises_in m w prem =
  Premises.for_all (fun (l, _) -> CanSet.mem (repr m l).canon w) prem
let _ise = ClausesOf.is_empty
let _ise' = ClausesBackward.is_empty
(* Partition the clauses according to the presence of w in the premises, and only w in the conclusions *)
let partition_clauses_fwd model (w : CanSet.t) : CanSet.t * CanSet.t * CanSet.t =
  CanSet.fold (fun idx (bwd, fwd) (allw, conclw, conclnw) ->
    let bwdw, bwdnw = ClausesOf.partition (fun (_k, prems) -> can_all_premises_in model w prems) bwd in
    let fwdw, fwdnw = ClausesBackward.partition (fun concl _clsinfo -> CanSet.mem (repr model concl).canon w) fwd in
    let allw =
      if ClausesOf.is_empty bwdw && ClausesBackward.is_empty fwdw then allw
      else
        CanSet.add idx (bwdw, fwdw) allw (* Premises and conclusions in w *)
    in
    let conclw =
      if ClausesOf.is_empty bwdnw then conclw
      else
        CanSet.add idx (bwdnw, ClausesBackward.empty) conclw (* Conclusions in w, premises not in w *)
    in
    let conclnw =
      if ClausesBackward.is_empty fwdnw then conclnw
      else
         CanSet.add idx (ClausesOf.empty, fwdnw) conclnw in (* Conclusions not in w, Premises in w *)
    (allw, conclw, conclnw))
    w (CanSet.empty, CanSet.empty, CanSet.empty)

let partition_clauses_fwd = time2 (Pp.str"partition clauses fwd") partition_clauses_fwd
(* a = 0
      b -> c
      a -> b + 1
      c -> c + 1

      1st round: b = 0.
      W = {b}
      2nd round: c = 0.
      W = {b, c}
      c = 1.
      W = {b, c}
      *)

(* If early_stop is given, check raises FoundImplication as soon as
   it finds that the given atom is true *)

(* model is a model for the clauses outside cls *)
let check ?early_stop model (cls : CanSet.t) =
  let cV = canonical_cardinal model in
  debug_check_invariants model;
  let rec inner_loop cardW w premconclw conclw m =
    (* Should consider only clauses with conclusions in w *)
    (* Partition the clauses acscording to the presence of w in the premises *)
    debug_loop Pp.(fun () -> str "Inner loop on " ++ int cardW ++ str" universes: " ++
      str " Premises and conclusions in w: " ++ pr_w m premconclw ++
      str " Conclusions in w: " ++ pr_w m conclw);
    (* Warning: m is not necessarily a model for w *)
    let rec inner_loop_partition w cls m =
      debug_loop Pp.(fun () -> str "cls = " ++ pr_w m cls);
      match loop cardW w cls m with
      | Loop -> Loop
      | Model (wr, mr) ->
        debug_loop Pp.(fun () -> str "wr = " ++ pr_w mr wr);
        (match check_clauses_with_premises ?early_stop w conclw mr with
        | Some (wconcl, (clsconcl, mconcl)) ->
          debug_loop Pp.(fun () -> str "clsconcl = " ++ pr_w mconcl clsconcl);
          inner_loop_partition wconcl clsconcl mconcl
        | None ->
          debug_loop Pp.(fun () -> str"Inner loop found a model");
          Model (wr, mr))
      in inner_loop_partition w premconclw m
  and loop cV w cls m =
    Control.check_for_interrupt ();
    debug_loop Pp.(fun () -> str"loop iteration on "  ++ CanSet.pr_clauses m cls ++ str" with bound " ++ int cV);
    match check_clauses_with_premises ?early_stop w cls m with
    | None -> Model (cls, m)
    | Some (w, (cls, m)) ->
      debug_loop Pp.(fun () -> str"Updated universes: " ++ prlist_with_sep spc (pr_index_point m) (PSet.elements w) ++ str", bound is " ++ int cV);
      let cardW = (PSet.cardinal w) in
      if Int.equal cardW cV
      then (debug_loop Pp.(fun () -> str"Found a loop on " ++ int cV ++ str" universes" ); Loop)
      else
        let (premconclw, conclw, premw) = partition_clauses_fwd m cls in
        (* debug_loop Pp.(fun () -> str"partitionning clauses: " ++ spc () ++
          CanSet.pr_clauses { m with entries = PMap.empty } cls); *)
        debug_loop Pp.(fun () -> str"partitioned clauses: from and to w " ++ spc () ++
          CanSet.pr_clauses { m with entries = PMap.empty } premconclw);
        debug_loop Pp.(fun () -> str"partitioned clauses: to w, not from w: " ++ spc () ++
          CanSet.pr_clauses { m with entries = PMap.empty } conclw);
        debug_loop Pp.(fun () -> str"partitioned clauses: from w, not to w " ++ spc () ++
          CanSet.pr_clauses { m with entries = PMap.empty } premw);

        (* debug_check_invariants { model = m; updates = w; clauses = conclnW }; *)
        (match inner_loop cardW PSet.empty premconclw conclw m with
        | Loop -> Loop
        | Model (wc, mc) ->
          debug_loop Pp.(fun () -> str "wc = " ++ pr_w mc wc);
          (* wc is a subset of w *)
          (match check_clauses_with_premises w premw mc with
          | None -> Model (wc, mc)
          | Some (w, (wcls, mcls)) -> loop cV w wcls mcls))
  in loop cV PSet.empty cls model

(* let check m w = *)
  (* debug Pp.(fun () -> str"Calling loop-checking"); *)
  (* check m w *)
  (* debug Pp.(fun () -> str"Loop-checking terminated"); *)
  (* with Stack_overflow -> *)
    (* CErrors.anomaly (Pp.str "check raised a stack overflow") *)

let entry_value m e =
  match e with
  | Equiv idx -> canonical_value m (repr m idx)
  | Canonical can -> canonical_value m can

let pr_levelmap (m : model) : Pp.t =
  let open Pp in
  h (prlist_with_sep fnl (fun (u, v) ->
    let value = entry_value m v in
    let point = Index.repr u m.table in
    Point.pr point ++ str" -> " ++ pr_opt int value) (PMap.bindings m.entries))
  (* Point.Map.pr Pp.int m  *)

let pr_model model =
  Pp.(str "model: " ++ pr_levelmap model)

let debug_model m =
  debug_model Pp.(fun () -> str"Model is " ++ pr_levelmap m)

let _repr_clause m (concl, prem as cl : clause) =
  let concl' = (repr m concl).canon in
  let prem' = repr_clauses_of m prem in
  if concl' == concl && prem' == prem then cl
  else (concl', prem')

let modify_can canidx (f : Index.t -> canonical_node -> canonical_node) =
  PMap.modify canidx
    (fun idx entry ->
    match entry with
    | Equiv _ -> assert false
    | Canonical can -> let can' = f idx can in
      if can' == can then entry else Canonical can')

type can_clause = ((canonical_node * int) NeList.t * (canonical_node * int))

let pr_can_clause m (prems, conclk) =
  let open Pp in
  pr_with (pr_can m) conclk ++ str" ≤ " ++ NeList.pr_with_sep spc (pr_with (pr_can m)) prems

let add_can_clause_model m ((prems, (canl, k)) : can_clause) : can_clause * model =
  let clof = (k, NeList.map (fun (can, k) -> (can.canon, k)) prems) in
  (* Add clause to the backwards clauses of l *)
  let canl' =
    let bwd =
      (* if ClausesOfRepr.mem_upto m clof clauses_bwd then clauses_bwd else  *)
        ClausesOf.add clof canl.clauses_bwd in
    if bwd == canl.clauses_bwd then canl
    else { canl with clauses_bwd = bwd }
  in
  let m' = if canl == canl' then m else change_node m canl' in
  let prems', m' = (* Add clause to the forward clauses from the premises *)
    NeList.fold_map (fun ((idx0, k) as prem) entries ->
      let idx = if idx0 == canl then canl' else idx0 in
      let idx' =
        let fwd = ClausesBackward.add (canl'.canon, ClausesOf.singleton clof) idx.clauses_fwd in
        if fwd == idx.clauses_fwd then idx
        else { idx with clauses_fwd = fwd }
      in
      if idx0 != idx' then ((idx', k), change_node entries idx')
      else (prem, entries))
      prems m'
  in (prems', (repr m' canl'.canon, k)), m'

let add_can_clause_model m cl =
  let can, model' = add_can_clause_model m cl in
  if model' == m then can, m else can, model'

let add_clause_model m (prems, (l, k)) : model =
  let m, canl = repr_compress m l in
  let canl = canl.canon in
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
  (* Add clause to the forward clauses from the premises *)
  let entries = Premises.fold (fun (idx, _) entries ->
    let entries, canidx = repr_compress_entries entries idx in
    let canidx = canidx.canon in
    modify_can canidx (fun _idx ({ clauses_fwd; _ } as can) ->
      (* let fwd = ClausesBackward.add_upto m (canl, ClausesOf.singleton clof) clauses_fwd in  *)
      let fwd = ClausesBackward.add (canl, ClausesOf.singleton clof) clauses_fwd in
      if fwd == clauses_fwd then can
      else { can with clauses_fwd = fwd })
      entries)
    prems entries
  in { m with entries }

(** Assumes premise and conclusion already in canonical form *)
let add_clauses_of_model m (l, kprems) =
  ClausesOf.fold (fun (k, prems) m ->
    let cl = (prems, (l, k)) in
    add_clause_model m cl) kprems m

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

let _canonical_model m = repr_model m

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
  (* match check_model clauses (clauses_levels model clauses) model with
  | None -> Some m
  | Some (w, m') ->
    let inw = clauses_forward m' m.clauses w in
    debug Pp.(fun () -> str"After one check model: " ++ int (Clauses.cardinal inw) ++ str" having premises in w");*)
  (* let levels = PSet.union w (clauses_levels clauses.Clauses.clauses_fwd) in *)
  match check m w with
  | Loop ->
    debug Pp.(fun () -> str"loop-checking found a loop");
    None
  | Model (_updates, model) ->
    debug_check_invariants model;
    debug_model model;
    debug Pp.(fun () -> str"loop-checking found a model");
    Some model

let infer_clauses_extension = time2 Pp.(str"infer_clauses_extension") infer_clauses_extension
let empty = empty_model

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


type pclause_info = (int * (Point.t * int) NeList.t)

let _to_clause_info m (k, prems : pclause_info) : clause_info =
  let trans_prem (p, k) =
    let can = repr_node m p in
    (can.canon, k)
  in
  (k, NeList.map trans_prem prems)

(* let _check_leq (m : t) u v = *)
  (* let cls = clauses_of_le_constraint model u v Clauses.empty in *)
  (* check_clauses model cls *)

(* let _is_bound (m : t) can cano : bool =
  PMap.exists (fun concl clsc ->
    if Index.equal concl can.canon then false
    else ClausesOf.has_bound model cano clsc) m.clauses *)

(* let inspect_bwd m (cls : ClausesBackward.t) : unit =
  ClausesBackward.fold (fun idx prems _ ->
    let triv = filter_trivial_clause m (idx, prems) in
    debug Pp.(fun () -> str "Clause " ++ pr_clause m triv ++ str" is trivial? " ++ bool (is_empty_clause triv)))
    cls () *)

(* Precondition: canu.value = canv.value, so no new model needs to be computed *)
let enforce_eq_can model canu canv : canonical_node * t =
  assert (canonical_value model canu = canonical_value model canv);
  assert (canu != canv);
  (* v := u or u := v, depending on Point.keep_canonical (e.g. for Set) *)
  debug_check_invariants model;
  let model0 = model in
  let can, other, model =
    if Point.keep_canonical (Index.repr canu.canon model.table) then
      canu, canv, enter_equiv model canv.canon canu.canon
    else
      canv, canu, enter_equiv model canu.canon canv.canon
  in
  let can, model =
    let bwd = ClausesOfRepr.union_upto model can.canon can.clauses_bwd other.clauses_bwd in
    let fwd = ClausesBackward.union_upto model can.clauses_fwd other.clauses_fwd in
    let modeln = { model with entries = PMap.empty } in
      debug Pp.(fun () -> str"Backward clauses for " ++
      pr_can model can ++ str": " ++ spc () ++
      pr_clauses_of modeln can.canon can.clauses_bwd);
      debug Pp.(fun () -> str"Backward clauses for " ++
      pr_can model0 other ++ str": " ++ spc () ++
      pr_clauses_of modeln other.canon other.clauses_bwd);
      debug Pp.(fun () -> str"New backward clauses for " ++
        pr_can model can ++ str": " ++ spc () ++
        pr_clauses_of modeln can.canon bwd);
      debug Pp.(fun () -> str"Add forward clauses for " ++
        pr_can model can ++ str": " ++ spc () ++
        pr_clauses_bwd modeln fwd);
      debug Pp.(fun () -> str"Previous forward clauses for " ++
        pr_can model can ++ str": " ++ spc () ++
        pr_clauses_bwd modeln can.clauses_fwd);
      debug Pp.(fun () -> str"Other forward clauses for " ++
        pr_can model0 other ++ str": " ++ spc () ++
        pr_clauses_bwd modeln other.clauses_fwd);
    let can = { can with clauses_bwd = bwd; clauses_fwd = fwd } in
    can, change_node model can
  in
  debug_check_invariants model;
  can, model

let enforce_eq_can = time3 (Pp.str"enforce_eq_can") enforce_eq_can

 let pr_can_constraints m can =
  let open Pp in
  pr_clauses_of m can.canon can.clauses_bwd ++ spc () ++
  str"Forward clauses: " ++ pr_clauses_bwd m can.clauses_fwd

let make_equiv m equiv =
  debug Pp.(fun () -> str"Unifying universes: " ++
    prlist_with_sep spc (fun can -> pr_can m can) equiv);
  match equiv with
  | can :: can' :: tl ->
    (* We are about to merge all these universes as they should be equal in the model,
      they should hence have the same values *)
    if CDebug.(get_flag debug_loop_checking_invariants) then
      assert (List.for_all (fun x -> canonical_value m x = canonical_value m can) (can' :: tl));
    let can, m =
      List.fold_left (fun (can, m) can' -> enforce_eq_can m can can')
        (enforce_eq_can m can can') tl
    in
    debug Pp.(fun () -> str"Chosen canonical universe: " ++ pr_can m can ++
          str"Constraints:" ++ pr_can_constraints m can);
    m
  | [_] -> m
  | _ -> assert false

let make_equiv = time2 (Pp.str"make_equiv") make_equiv

let clauses_bwd_univs m cls =
  PMap.fold (fun concl _ acc -> PSet.add (repr m concl).canon acc) cls PSet.empty

let find_to_merge model status canv canu =
  let rec forward can : bool =
    debug Pp.(fun () -> str"visiting " ++ pr_can model can);
    match Status.find status can with
    | merge -> merge
    | exception Not_found ->
      let merge = can == canv || can == canu in
      let () = Status.replace status can merge in
      let cls = can.clauses_fwd in
      debug Pp.(fun () -> str"Forward universes: " ++ int (ClausesBackward.cardinal cls) ++
        str " Canonical: " ++ int (PSet.cardinal (clauses_bwd_univs model cls)));
      let merge =
        ClausesBackward.fold (fun concl _cls merge ->
          let conclcan = repr model concl in
          if conclcan != can && canonical_value model conclcan = canonical_value model can then (* We stay in the same equivalence class *)
            let merge' = forward conclcan in
            merge' || merge
          else merge) cls merge
      in
      Status.replace status can merge;
      merge
  in
  let merge = forward canu in
  if merge then
    let merge_fn can mark acc = if mark then can :: acc else acc in
    let equiv = Status.fold merge_fn status [] in
    merge, equiv
  else merge, []

let find_to_merge =
  time4 (Pp.str "find_to_merge") find_to_merge

let simplify_clauses_between model canv canu =
  if canv == canu then model
  else if not (Option.equal Int.equal (canonical_value model canu) (canonical_value model canv)) then
      (* We know v -> u and check for u -> v, this can only be true if both levels
        already have the same value *)
    (debug Pp.(fun () -> pr_can model canu ++ str"'s value =  " ++
        pr_opt int (canonical_value model canu) ++ str" and " ++ pr_can model canv ++ str "'s value = "
      ++ pr_opt int (canonical_value model canv) ++ str", no simplification possible");
      model)
  else
    let status = Status.create model in
    let merge, equiv = find_to_merge model status canv canu in
    if merge then make_equiv model equiv else model

(* let simplify_clauses_between = *)
  (* time3 (Pp.str "simplify_clauses_between") simplify_clauses_between *)
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

let can_clause_of_can_constraint (cstr : can_constraint) : can_clause =
  let (l, k, r) = cstr in (* l + k <= r *)
  (NeList.tip (r, 0), (l, k))

let _can_clause_of_point_constraint (m : t) l k r : can_clause =
  (* l + k <= r *)
  let canl = repr_node m l in
  let canr = repr_node m r in
  (NeList.tip (canr, 0), (canl, k))

let _filter_trivial_clause m (l, kprems as x) =
  let prems' =
    ClausesOf.filter_map (fun kprems -> ClausesOfRepr.filter_trivial_clause m l kprems) kprems
  in
  if ClausesOf.is_empty prems' then None
  else if prems' == kprems then Some x
  else Some (l, prems')

let mem_clause m ((l, kprem) : clause) : bool =
  ClausesOfRepr.subset_upto m kprem (repr m l).clauses_bwd

(* let enforce_Clauses.of_bwd_can_constraint = *)
  (* time2 (Pp.str "Enforcing clauses") enforce_Clauses.of_bwd_can_constraint *)

type 'a check_function = t -> 'a -> 'a -> bool

(* @raises VacuouslyTrue if there is an undefined level in the premises *)
let min_can_premise model prem =
  let g (l, k) = (match canonical_value model l with Some v -> v | None -> raise VacuouslyTrue) - k in
  let f prem minl = min minl (g prem) in
  Premises.fold_ne f g prem

(* let _check_clause m prems concl k =
  (* premises -> can + k ? *)
  let test_idx y kpath =
    match prems with
    | NeList.Tip (prem, k') -> Index.equal y prem.canon && kpath <= k'
    | _ ->
        try let ky = NeList.find (fun prem -> Index.equal y prem.canon) prems in
          kpath <= ky
        with Not_found -> false
  in
  let test_repr y kpath =
    match prems with
    | NeList.Tip (prem, k') -> y == prem && kpath <= k'
    | _ ->
        if NeList.mem_assq y prems then
          kpath <= NeList.assq y prems
        else false
  in
  (* If the clause holds then prems -> concl + k, so k0 + k <= concl.value *)
  let rec aux visited todo next_todo =
    match todo, next_todo with
    | [], [] -> visited
    | [], todo -> aux visited todo []
    | (canv, kpath) :: todo, next_todo ->
      match canv.mark with
      | Visited kpath' when kpath' <= kpath -> aux visited todo next_todo
      | _ ->
        let bwd = canv.clauses_bwd in
        if ClausesOf.exists
          (fun (kp, premises) ->
            NeList.for_all (fun (idx, k') -> test_idx idx (kpath - kp + k')) premises) bwd then
          raise_notrace (Found visited)
        else
        (* canv + k' -> canv + kpath *)
          let visited = canv :: visited in
          canv.mark <- Visited kpath;
          let next_todo =
            ClausesOf.fold
              (fun (kp, premises) acc ->
                NeList.fold (fun (idx, k') acc ->
                  (* idx + k' -> canv + kp *)
                  let canidx = repr m idx in
                  let kidx = kpath - kp + k' in
                  if not (Index.equal canidx.canon idx) &&
                    test_repr canidx kidx then raise_notrace (Found visited)
                  else (canidx, kidx) :: acc)
                  premises acc)
                bwd next_todo
          in
          aux visited todo next_todo
  in
  try
    let res, visited =
      try false, aux [] [(concl, k)] []
      with Found visited -> true, visited
    in
    List.iter (fun u -> u.mark <- NoMark) visited;
    res
  with e ->
    (* Unlikely event: fatal error or signal *)
    let () = unset_marks m in
    raise e *)

type check_clause_mark = VisitedAt of int

exception Found

let _check_clause_singleton m prem concl k =
  (* premise -> concl + k ? *)
  let premidx = prem.canon in
  let test_idx y kpath = Index.equal y premidx && kpath <= 0 in
  let test_repr y kpath = y == prem && kpath <= 0 in
  let fold_prem kpath (kp, premises) acc =
    match premises with
    | NeList.Tip (idx, k') ->
      let canidx = repr m idx in
      let kidx = kpath - kp + k' in
      if canidx == prem && kidx <= 0 then raise_notrace Found
      (* else if prem.value > canidx.value then
        (* If this holds then it is impossible for a clause prem -> canidx + k to hold,
           as this would imply that canidx.value >= prem.value + k
        *)
        acc *)
      else (canidx, kidx) :: acc
    | _ ->
    NeList.fold (fun (idx, k') acc ->
      (* idx + k' -> canv + kp *)
      let canidx = repr m idx in
      let kidx = kpath - kp + k' in
      if not (Index.equal canidx.canon idx) &&
        test_repr canidx kidx then raise_notrace Found
      else (canidx, kidx) :: acc)
      premises acc
  in
  let status = Status.create m in
  let rec aux todo next_todo =
    match todo, next_todo with
    | [], [] -> ()
    | [], todo -> aux todo []
    | (canv, kpath) :: todo, next_todo ->
      match Status.find status canv with
      | VisitedAt kpath' when kpath' <= kpath -> aux todo next_todo
      | exception Not_found | _ ->
        let existsfn kprem =
          kpath - fst kprem <= 0 &&
          match snd kprem with
          | NeList.Tip (idx, _) -> Index.equal idx premidx
          | _ -> NeList.for_all (fun (idx, k') -> test_idx idx (kpath - fst kprem + k')) (snd kprem)
        in
        let bwd = canv.clauses_bwd in
        if ClausesOf.exists existsfn bwd then raise_notrace Found
        else
        (* canv + k' -> canv + kpath *)
          let fold_fn kprem acc = fold_prem kpath kprem acc in
          let next_todo = ClausesOf.fold fold_fn bwd next_todo in
          Status.replace status canv (VisitedAt kpath);
          aux todo next_todo
  in
  try let () = aux [(concl, k)] [] in false
  with Found -> true



(* A clause premises -> concl + k might hold in the current minimal model without being valid in all
   its extensions.

   We generate the minimal model starting from the premises. I.e. we make the premises true.
   Then we check that the conclusion holds in this minimal model.  *)

let check_clause_singleton_alt model prem concl k =
  (* premise -> concl + k ? *)
  debug Pp.(fun () -> str"Checking entailment: " ++ pr_index_point model prem.canon ++
    str " -> " ++ pr_index_point model concl.canon ++ str"+" ++ int k);
  let values = PMap.singleton prem.canon 0 in
  let model = { model with values } in
  let cls = CanSet.singleton prem.canon (prem.clauses_bwd, prem.clauses_fwd) in
  (* let modified, (w, model) = check_model_fwd_clauses_aux prem.clauses_fwd (PSet.empty, (mo.empty, model)) in
  if PSet.is_empty modified then false else begin *)
  (* We have a model where only the premise is true, check if the conclusion follows *)
  debug Pp.(fun () -> str"Launching loop-checking to check for entailment");
  match check ~early_stop:(concl, k) model cls with
  | exception FoundImplication ->
    debug Pp.(fun () -> str"loop-checking found the implication early");
    true
  | Loop ->
    debug Pp.(fun () -> str"loop-checking found a loop");
    false
  | Model (_updates, model') ->
    debug Pp.(fun () -> str"loop-checking found a model");
    debug_check_invariants model';
    debug_model model';
    match canonical_value model' concl with
    | None ->
      debug Pp.(fun () -> str"Conclusion has no value in the minimal model, not implied");
      false
    | Some value ->
      debug Pp.(fun () -> str"Conclusion has value " ++ int value ++
        str" in the minimal model, expecting conclusion + " ++ int k ++ str " to hold");
      k <= value

let check_clause_singleton model prem concl k =
  check_clause_singleton_alt model prem concl k

  (*
  let res' = check_clause_singleton_alt model prem concl k in
  if res == res' then res
  else
    (CErrors.anomaly Pp.(str"check_clause_singleton discrepancy: original gave " ++ bool res ++
      str " while alternative gave " ++ bool res'))
*)

(* a -> b
   b -> c

   add x



*)
(*
let check_holds m concl clause =
  let (k, premises) = clause in
  let m =
  let chk = NeList.fold (fun (idx, idxk) m ->
    let can = repr_model m idx in
    update_value (can, m) idxk)
    premises m
  in
  chk*)

(* let check_clauses m (cls : ClausesBackward.t) =
  PMap.for_all (fun concl cls ->
    let can = repr model concl in
    ClausesOf.for_all (fun cl ->
        let bwdc = check_clause_holds model can cl in bwdc)
      cls)
    cls *)

      (* check_inv_clause_of m concl cl) *)
      (* if check_clause_of m can.value cl then *)
        (* let fwdc = check_clause_holds_fwd m can cl in *)
        (* if fwdc == bwdc then fwdc *)
        (* else CErrors.anomaly Pp.(str "check_clause_holds differ in fwd and backward mode: forward" ++ bool fwdc ++ str" backward: " ++ bool bwdc) *)
      (* else false)  *)

(* let check_clauses m cls =
  if check_clauses m cls then
    (debug Pp.(fun () -> str"check_clauses succeeded on: " ++ pr_clauses_bwd model cls ++
    str" and model " ++ pr_levelmap model); true)
  else (debug Pp.(fun () -> str"check_clauses failed on: " ++ pr_clauses_bwd model cls ++
    str" and model " ++ pr_levelmap model); false) *)


(* let check_clause = time4 (Pp.str"check_clause") check_clause *)

let check_lt (m : t) u v =
  let canu = repr_node m u in
  let canv = repr_node m v in
  check_clause_singleton m canv canu 1
  (* let (prems, (concl, k)) = can_clause_of_point_constraint m u 1 v in *)
  (* check_clause m prems concl k *)

let check_leq (m : t) u vp =
  debug_check Pp.(fun () -> str"checking : " ++ Point.pr u ++ str " ≤ " ++ Point.pr vp);
  let canu = repr_node m u in
  let canv = repr_node m vp in
  canu == canv ||
  check_clause_singleton m canv canu 0

let check_eq m u v =
  let canu = repr_node m u in
  let canv = repr_node m v in
  canu == canv

(*let check_clause_holds_fwd m can clause =
  (* premises -> can + k *)
  let (kcan, premises) = clause in
  (* 1, UnivBinders.14, 0 *)
  let canp = Premises.map (fun (idx, k) -> repr m idx, k) premises in
  debug_check Pp.(fun () -> str"Checking " ++ pr_clause_info m can.canon clause);
  if NeList.mem_assq can canp then
    (debug_check Pp.(fun () -> str " ? " ++ bool true); true)
  else begin
    let rec aux (canv, kpath) =
      (* canv + kpath -> can + k ? *)
      let fwd = canv.clauses_fwd in (* Constraints canv -> ? *)
      try let cls = PMap.find can.canon fwd in
        (* Constraints canv -> can *)
        debug_check Pp.(fun () -> str"Found " ++ pr_can m can ++ str" in forward clauses of " ++ pr_can m canv ++ spc () ++
          str "forward clauses: " ++ pr_clauses_of m can.canon cls);
        ClausesOf.exists (fun (kp, premises) ->
          (* premises -> can.canon + kp *)
          let (_, kcanv) = NeList.head premises in
          (* kcanv is always 0 *)
          (* canv + kcanv -> can.canon + kp implies canv + kpath -> can.canon + k *)
          kcan <= kp + kpath - kcanv) cls
      with Not_found ->
        debug_check Pp.(fun () -> str"Didn't find " ++ pr_can m can ++ str" in forward clauses of " ++ pr_can m canv ++ spc () ++
          str "forward clauses: " ++ pr_clauses_bwd m fwd);
        PMap.exists (fun idx cls ->
          let canidx = repr m idx in
          (* Trivial canv + k -> canv clause *)
          if canidx == canv then
            (debug_check Pp.(fun () -> str"Skipping trivial clauses: " ++ pr_clauses_of m idx cls); false)
          else if canidx == can then (* Missed clauses due to forward clauses not being a canonical map *)
            ClausesOf.exists (fun (kp, premises) ->
              (* premises -> can.canon + kp *)
              let (_, kcanv) = NeList.head premises in
              (* kcanv is always 0 *)
              (* canv + kcanv -> can.canon + kp implies canv + kpath -> can.canon + k *)
              kcan <= kp + kpath - kcanv) cls
          else
          ClausesOf.exists (fun (kp, premises) ->
          (* premises = [canv] -> canidx.canon + kp *)
            Premises.exists (fun (_, kcanv) -> aux (canidx, kpath + kp - kcanv)) premises)
          cls) fwd
    in
    let res = NeList.exists aux canp in
    debug_check Pp.(fun () -> str " ? " ++ bool res); res
  end

let _check_clause_holds_fwd_use = check_clause_holds_fwd*)

(* Checks that a clause currently holds in the model *)
let check_clause_of m conclv clause =
  let (k, premises) = clause in
  let k0 = min_premise m premises in
  if k0 < 0 then false (* We do not allow vacuously true constraints *)
  else
    (debug Pp.(fun () -> str"check_clause_of: k = " ++ int k ++ str" k0 = " ++ int k0 ++ str" conclv = " ++ int conclv);
    k + k0 <= conclv)

let _check_clause_info m (concl, clause) =
  let v = canonical_value m (repr m concl) in
  match v with
  | Some v -> ClausesOf.for_all (check_clause_of m v) clause
  | None -> true (* concl is undefined *)

(* let pr_clauses m cls = Clauses.pr pr_clause m cls.Clauses.clauses_bwd *)

let _mem_clause = time2 (Pp.str"mem_clause") mem_clause
let _add_clauses_of_model = time2 (Pp.str "add_clauses_of_model") add_clauses_of_model

let update_model_value (m : model) can k' : model =
  let v = canonical_value m can in
  let k' = max_opt v k' in
  if Option.equal Int.equal k' v then m
  else
    (debug Pp.(fun () -> str"Updated value of " ++ pr_can m can ++ str " to " ++ pr_opt int k');
    set_canonical_value m can (Option.get k'))

let update_model ((prems, (can, k)) : can_clause) (m : model) : CanSet.t * model =
  match min_can_premise m prems with
  | exception VacuouslyTrue -> (CanSet.empty, m)
  | k0 ->
    let m' = update_model_value m can (Some (k + k0)) in
    if m' != m then
      let canset = CanSet.add can.canon (can.clauses_bwd, can.clauses_fwd) CanSet.empty in
      let pset = PSet.singleton can.canon in
      match check_clauses_with_premises pset canset m' with
      | Some (_modified, wm) -> wm
      | None -> (CanSet.empty, m')
    else (CanSet.empty, m)

let filter_trivial_can_clause ((prems, (concl, k as conclk) as x) : can_clause) : can_clause option =
  match NeList.filter (fun (prem, k') -> not (prem == concl && k' >= k)) prems with
  | Some prems' -> if prems' == prems then Some x else Some (prems', conclk)
  | None -> None

let infer_clause_extension cl m =
  (* debug Pp.(fun () -> str "current model is: " ++ pr_levelmap model); *)
  debug_check_invariants m;
  debug Pp.(fun () -> str"Enforcing clause " ++ pr_can_clause m cl);
  match filter_trivial_can_clause cl with
  | None -> Some m
  | Some cl ->
    debug Pp.(fun () -> str"After filtering, clause is: " ++ pr_can_clause m cl);
    (* if mem_clause m cl then Some m else *)
    let cl, m = add_can_clause_model m cl in
    let w, m = update_model cl m in
    if CanSet.is_empty w then begin
      (* The clause is already true in the current model,
        but might not be in an extension, so we keep it *)
      debug Pp.(fun () -> str"Clause is valid in the current model");
      (* debug_clauses Pp.(fun () -> str"Clauses: " ++ pr_clauses model m.clauses); *)
      Some m
    end else begin
      (* The clauses are not valid in the current model, we have to find a new one *)
      debug Pp.(fun () -> str"Enforcing clauses requires a new inference");
      match infer_clauses_extension w m with
      | None ->
        debug Pp.(fun () -> str"Enforcing clauses " ++ pr_can_clause m cl ++ str" resulted in a loop");
        None
      | Some _ as x ->
        (* let (_, (conclcan, _)) = cl in *)
        (* debug Pp.(fun () -> str"Backward clauses of concl " ++ pr_clauses_of model conclcan.canon conclcan.clauses_bwd); *)
        (* assert (check_clause model cl); *)
        x
    end

let infer_extension x k y m =
  let cl = can_clause_of_can_constraint (x, k, y) in
  infer_clause_extension cl m

let infer_extension =
  time4 Pp.(str "infer_extension") infer_extension

(* Enforce u <= v and check if v <= u already held, in that case, enforce u = v *)
let enforce_leq_can u v m =
  match infer_extension u 0 v m with
  | None -> None
  | Some m' ->
    if m' != m then
      let v = repr m' v.canon in
      let u = repr m' u.canon in
      Some (simplify_clauses_between m' v u)
    else Some m

let enforce_leq u v m =
  let m, canu = repr_compress_node m u in
  let m, canv = repr_compress_node m v in
  enforce_leq_can canu canv m

let enforce_lt u v m =
  let m, canu = repr_compress_node m u in
  let m, canv = repr_compress_node m v in
  infer_extension canu 1 canv m

let get_proper_value m can =
  match canonical_value m can with
  | Some v -> v
  | None -> raise (Undeclared (Index.repr can.canon m.table))

let enforce_eq u v m =
  let canu = repr_node m u in
  let canv = repr_node m v in
  if canu == canv then Some m
  else begin
    debug Pp.(fun () -> str"enforce_eq: " ++ pr_can m canu ++ str" = " ++ pr_can m canv);
    match Int.compare (get_proper_value m canu) (get_proper_value m canv) with
    (* | 0 -> Some (snd (enforce_eq_can m canu canv)) *)
    | x when x <= 0 ->
      (* canu.value <= canv.value, so v <= u is trivial and we cannot have u < v,
         only u <= v in the clauses.
         The first enforce will be fast, the second can involve an inference *)
      (* let cls = clauses_forward model m.clauses (PSet.singleton canu.canon) in *)
      (* debug Pp.(fun () -> str"enforce_eq: clauses to move " ++ pr_clauses model cls); *)
      Option.bind (enforce_leq_can canv canu m)
        (fun m' ->
          let canu' = repr m' canu.canon in
          let canv' =  repr m' canv.canon in
          enforce_leq_can canu' canv' m')
    | _ ->
      (* canv.value < canu.value, so u <= v is trivial.
          The first enforce will be fast, the second can involve an inference *)
      (* let cls = clauses_forward model m.clauses (PSet.singleton canv.canon) in *)
      (* debug Pp.(fun () -> str"enforce_eq: clauses to move " ++ pr_clauses model cls); *)
      Option.bind (enforce_leq_can canu canv m)
        (fun m' ->
          let canu' = repr m' canu.canon in
          let canv' =  repr m' canv.canon in
          enforce_leq_can canv' canu' m')
  end


type lub = (Point.t * int) list
type ilub = (canonical_node * int) NeList.t

(* max u_i <= v <-> ∧_i u_i <= v *)
let clauses_of_le_constraint (u : ilub) (v : ilub) cls =
  NeList.fold (fun (u, k) cls ->
    (v, (u, k) : can_clause) :: cls) u cls

let clauses_of_constraint m (u : lub) k (v : lub) cls =
  let u = List.map (fun (p, k) -> repr_node m p, k) u in
  let v = List.map (fun (p, k) -> repr_node m p, k) v in
  let u = NeList.of_list u in
  let v = NeList.of_list v in
  match k with
  | Le -> clauses_of_le_constraint u v cls
  | Lt -> clauses_of_le_constraint (NeList.map (fun (l, k) -> (l, k + 1)) u) v cls
  | Eq -> clauses_of_le_constraint u v (clauses_of_le_constraint v u cls)

let enforce_constraint u k v (m : t) =
  let cls = clauses_of_constraint m u k v [] in
  List.fold_left (fun m cl ->
    match m with
    | None -> None
    | Some m -> infer_clause_extension cl m) (Some m) cls

exception AlreadyDeclared

let add_model u { entries; table; values; canonical } =
  if Index.mem u table then
   (debug Pp.(fun () -> str"Already declared level: " ++ Point.pr u);
    raise AlreadyDeclared)
  else
    let idx, table = Index.fresh u table in
    let can = Canonical { canon = idx;
      clauses_fwd = PMap.empty; clauses_bwd = ClausesOf.empty } in
    let entries = PMap.add idx can entries in
    let values = PMap.add idx 0 values in
    idx, { entries; table; values; canonical = canonical + 1 }

let add ?(rank:int option) u model =
  let _r = rank in
  debug Pp.(fun () -> str"Declaring level " ++ Point.pr u);
  let _idx, model = add_model u model in
  model

let check_declared model us =
  let check l = if not (Index.mem l model.table) then raise (Undeclared l) in
  Point.Set.iter check us

type explanation = Point.t * (constraint_type * Point.t) list

let get_explanation (cstr : Point.t * constraint_type * Point.t) _ : explanation =
  let (l, _, _) = cstr in
  (* TODO *)
  (l, [])

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
      | NeList.Tip (v, 0) ->
        let vcan = repr m v in
        let vp = Index.repr vcan.canon m.table in
        if k = 0 then Constraints.add (conclp, Le, vp) cstrs
        else if k = 1 then Constraints.add (conclp, Lt, vp) cstrs
        else assert false
      | _ -> assert false) cls cstrs)
    clauses Constraints.empty

let constraints_of model fold acc =
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

let constraints_for ~(kept:Point.Set.t) model (fold : 'a constraint_fold) (accu : 'a) =
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
      let v = match prems with NeList.Tip (v, 0) -> v | _ -> assert false in
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

let domain model = Index.dom model.table

let choose p model p' =
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
let repr model =
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
          | NeList.Tip (v, 0) ->
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
  let max = Option.default 0 (model_max m) in
  let valm = PMap.map (fun e -> max - Option.get (entry_value m e)) m.entries in
    pmap_to_point_map m.table valm

let valuation model = valuation_of_model model

end
