open Univ

let _, debug_updates = CDebug.create_full ~name:"loop-checking-updates" ()

(* let debug_check_fwd, _ = CDebug.create_full ~name:"loop-checking-fix-check" () *)

let _debug_loop_checking_partition, debug_loop_partition = CDebug.create_full ~name:"loop-checking-partition" ()
let debug_loop_checking_invariants, _debug_invariants = CDebug.create_full ~name:"loop-checking-invariants" ()
let _debug_loop_checking_invariants_all, debug_invariants_all = CDebug.create_full ~name:"loop-checking-invariants-all" ()
let _debug_loop_checking_model, debug_model = CDebug.create_full ~name:"loop-checking-model" ()
let _debug_loop_checking_clauses, _debug_clauses = CDebug.create_full ~name:"loop-checking-clauses" ()
(* let _debug_loop_checking_bwdclauses, debug_bwdclauses = CDebug.create_full ~name:"loop-checking-bwdclauses" () *)
let _debug_loop_checking_flag, debug = CDebug.create_full ~name:"loop-checking" ()
let debug_loop_checking_timing_flag, debug_timing = CDebug.create_full ~name:"loop-checking-timing" ()
let _debug_loop_checking_loop, debug_loop = CDebug.create_full ~name:"loop-checking-loop" ()
let _debug_loop_checking_check_model, debug_check_model = CDebug.create_full ~name:"loop-checking-check-model" ()
let _debug_loop_checking_check, _debug_check = CDebug.create_full ~name:"loop-checking-check" ()
let _debug_loop_checking_set, _debug_set = CDebug.create_full ~name:"loop-checking-set" ()

let _debug_loop_checking_global_flag, debug_global = CDebug.create_full ~name:"loop-checking-global" ()
let _debug_loop_checking_constraints_for_flag, debug_constraints_for =
  CDebug.create_full ~name:"loop-checking-constraints-for" ()

let _debug_loop_checking_minim, _debug_minim =
  CDebug.create_full ~name:"loop-checking-minim" ()

(* let _debug_loop_checking_remove, debug_remove = CDebug.create_full ~name:"loop-checking-remove" () *)

let _debug_enforce_eq, debug_enforce_eq = CDebug.create_full ~name:"loop-checking-enforce-eq" ()
let _debug_find_to_merge_global_flag, debug_find_to_merge_global = CDebug.create_full ~name:"loop-checking-find-to-merge-global" ()

let _debug_find_to_merge_flag, debug_find_to_merge = CDebug.create_full ~name:"loop-checking-find-to-merge" ()
let debug_switch_union_upto, _debug_switch_union_upto = CDebug.create_full ~name:"loop-checking-switch-union-upto" ()

(* let _ = CDebug.set_flag debug_loop_checking_check true *)

let debug_pr_level_ref = ref Level.raw_pr
let set_debug_pr_level fn =
  debug_global Pp.(fun _ -> str"resetting pr_level function");
  debug_pr_level_ref := fn

let debug_pr_level l = !debug_pr_level_ref l

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

let _time4 prefix f =
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


module Index :
sig
  type t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  module Set : CSig.SetS with type elt = t
  module Map : CMap.ExtS with type key = t and module Set := Set
  type table
  val empty : table
  val fresh : Level.t -> table -> t * table
  val mem : Level.t -> table -> bool
  val find : Level.t -> table -> t
  val repr : t -> table -> Level.t
  val dom : table -> Level.Set.t
  (* val hash : t -> int *)
end =
struct
  type t = int
  let equal = Int.equal
  let compare = Int.compare
  module Set = Int.Set
  module Map = Int.Map

  type table = {
    tab_len : int;
    tab_fwd : Level.t Int.Map.t;
    tab_bwd : int Level.Map.t
  }

  let empty = {
    tab_len = 0;
    tab_fwd = Int.Map.empty;
    tab_bwd = Level.Map.empty;
  }
  let mem x t = Level.Map.mem x t.tab_bwd
  let find x t = Level.Map.find x t.tab_bwd
  let repr n t = Int.Map.find n t.tab_fwd

  let fresh x t =
    let () = assert (not @@ mem x t) in
    let n = t.tab_len in
    n, {
      tab_len = n + 1;
      tab_fwd = Int.Map.add n x t.tab_fwd;
      tab_bwd = Level.Map.add x n t.tab_bwd;
    }

  let dom t = Level.Map.domain t.tab_bwd

  (* let hash x = x *)
end

module PMap = Index.Map

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

  let _filter_map_same f l =
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

  let rec append xs ys =
    match xs with
    | Tip x -> Cons (x, ys)
    | Cons (x, xs) -> Cons (x, append xs ys)

  let map_splice (f : 'a -> 'a t option) (l : 'a t) : 'a t =
    let rec aux l =
      match l with
      | Tip x -> (match f x with Some l -> l | None -> l)
      | Cons (x, xs) ->
        match f x with
        | Some l -> append l (aux xs)
        | None -> Cons (x, aux xs)
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

  let _uniq eq l =
    let rec aux l =
      match l with
      | Tip _ -> l
      | Cons (hd, tl) ->
        if exists (fun y -> eq hd y) tl then aux tl
        else Cons (hd, aux tl)
    in aux l

  type cmp =
    | Merge of bool (* false = use the left argument, true = use the right argument *)
    | Diff of int

  let add cmp x l =
    let rec aux l =
      match l with
      | Tip y ->
        (match cmp x y with
        | Merge false -> Tip x
        | Merge true -> l
        | Diff c ->
          if c <= 0 then Cons (x, l)
          else Cons (y, Tip x))
      | Cons (y, l') ->
        (match cmp x y with
         | Merge false -> Cons (x, l')
         | Merge true -> l
         | Diff c ->
            if c <= 0 then Cons (x, l)
            else let l'' = aux l' in
              if l'' == l' then l
              else Cons (y, l''))
    in aux l

  let sort cmp l =
    match l with
    | Tip _ -> l
    | Cons (a, l') -> fold (fun a acc -> add cmp a acc) l' (Tip a)

end

module SetWithCardinal (O:OrderedType.S) (S : CSig.SetS with type elt = O.t) =
struct

  type t = { set : S.t; cardinal : int }

  let empty = { set = S.empty; cardinal = 0 }

  let is_empty s = S.is_empty s.set
  let cardinal s = s.cardinal

  let add x ({set; cardinal} as s) =
    let set' = S.add x set in
    if set' == set then s
    else { set = set'; cardinal = cardinal + 1}

  let singleton x = add x empty

  let mem x s = S.mem x s.set
  let remove x ({set; cardinal} as s) =
    let set' = S.remove x set in
    if set' == set then s
    else { set = set'; cardinal = cardinal - 1}

  let union s {set; _} = S.fold add set s

  let fold f s = S.fold f s.set

  let elements s = S.elements s.set

  let smap f s = S.fold (fun x acc -> S.add (f x) acc) s S.empty
  let map f {set; _} =
    let s' = smap f set in
    { set = s'; cardinal = S.cardinal s'}

  let for_all p s = S.for_all p s.set
  let exists p s = S.exists p s.set

  let iter f s = S.iter f s.set

  let partition f (s : t) =
    let left = ref 0 and right = ref 0 in
    let f x =
      let res = f x in
      if res then (incr left; res)
      else (incr right; res)
    in
    let l, r = S.partition f s.set in
    { set = l; cardinal = !left }, { set = r; cardinal = !right }

  let choose s = S.choose s.set

  let of_set s = { set = s; cardinal = S.cardinal s }
end

module type TypeWithCardinal =
sig
  type t
  val cardinal : t -> int
end

module MapWithCardinal (O : OrderedType.S) (T : TypeWithCardinal) =
struct
  module M = Map.Make(O)
  type t = { map : T.t M.t; cardinal : int }

  let empty = { map = M.empty; cardinal = 0 }
  let is_empty m = M.is_empty m.map
  let add x k m =
    let m' = M.add x k m.map in
    if m' == m.map then m
    else { map = m'; cardinal = m.cardinal + 1}

  let singleton x k = add x k empty

  let remove x m =
    let m' = M.remove x m.map in
    if m' == m.map then m
    else { map = m'; cardinal = m.cardinal - 1}

  let fold f m = M.fold f m.map
  let cardinal m = m.cardinal

  let union f m m' =
    let cardinal = ref m.cardinal in
    let merge_fn k x x' =
      match x, x' with
      | None, None -> None
      | Some x, None -> cardinal := !cardinal + T.cardinal x; Some x
      | None, Some x -> cardinal := !cardinal + T.cardinal x; Some x
      | Some x, Some y ->
        let xy = f k x y in
        cardinal := !cardinal + T.cardinal xy;
        Some xy
    in
    let u = M.merge merge_fn m.map m'.map in
    { map = u; cardinal = !cardinal }

  let update x f {map;cardinal} =
    let cardinal = ref cardinal in
    let fn x =
      let x' = f x in
      match x, x' with
      | None, Some m' -> cardinal := !cardinal + T.cardinal m'; x'
      | None, None -> x'
      | Some x, None -> cardinal := !cardinal - T.cardinal x; x'
      | Some x, Some y ->
        cardinal := !cardinal - T.cardinal x + T.cardinal y; x'
    in
    let m' = M.update x fn map in
    { map = m'; cardinal = !cardinal}

  let compute_cardinal m' =
    M.fold (fun _ v acc -> acc + T.cardinal v) m' 0

  let map f m =
    let m' = M.map f m.map in
    if m' == m.map then m
    else { map = m'; cardinal = compute_cardinal m' }

  let exists f m = M.exists f m.map
  let _for_all f m = M.for_all f m.map
  let iter f m = M.iter f m.map

  let filter f m =
    let m' = M.filter f m.map in
    { map = m'; cardinal = compute_cardinal m' }

  let filter_map f m =
    let m' = M.filter_map f m.map in
    { map = m'; cardinal = compute_cardinal m' }

  let _find x m = M.find x m.map
  let find_opt x m = M.find_opt x m.map
  let _partition f (m : t) =
    let left = ref 0 and right = ref 0 in
    let f k x =
      let res = f k x in
      if res then (left := !left + T.cardinal x; res)
      else (right := !right + T.cardinal x; res)
    in
    let l, r = M.partition f m.map in
    { map = l; cardinal = !left}, { map = r; cardinal = !right}

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

    let incl x y : NeList.cmp =
      let (idx, k) = x in
      let (idx', k') = y in
      match Index.compare idx idx' with
      | 0 -> NeList.Merge (k <= k')
      | x -> NeList.Diff x
  end

  open NeList

  type t = Premise.t NeList.t

  let _fold = NeList.fold

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

  let pr pr_index_point prem =
    let open Pp in
    prlist_with_sep (fun () -> str ",") pr_index_point (to_list prem)

  let add : Premise.t -> t -> t = NeList.add Premise.incl

  let add_opt p o =
    match o with
    | None -> NeList.tip p
    | Some l -> add p l
  let sort : t -> t = NeList.sort Premise.incl

  let filter f l =
    NeList.filter f l

  let union (prems : t) (prems' : t) : t =
    fold add prems prems'

  let shift n p =
    if Int.equal n 0 then p
    else NeList.map (fun (x,k) -> (x, k + n)) p

  let subst idx u prems =
    let rec aux l =
      match l with
      | Tip (idx', k) ->
        if Index.equal idx idx' then shift k u
        else l
      | Cons ((idx', k) as prem, prems) ->
        if Index.equal idx idx' then union (shift k u) prems
        else let prems' = aux prems in
          if prems' == prems then l
          else add prem prems'
    in aux prems

end

let pr_with f (l, n) =
  if Int.equal n 0 then f l
  else Pp.(f l ++ Pp.str"+" ++ int n)

let pr_clause pr_index_point (prems, concl) =
  let open Pp in
  hov 0 (Premises.pr pr_index_point prems ++ str " → " ++ pr_index_point concl)

type locality =
| Global
| Local

let pr_local local = let open Pp in
  match local with
  | Local -> spc () ++ str"(local)"
  | Global -> spc () ++ str"(global)"

let compare_locality local local' =
  match local, local' with
  | Local, Local -> 0
  | Local, Global -> -1
  | Global, Local -> 1
  | Global, Global -> 0

let subsumes_locality local local' =
  match local, local' with
  | Local, Local -> true
  | Local, Global -> false (* A local constraint cannot replace a global one *)
  | Global, Local -> true (* A global constraint is a fortiori valid locally *)
  | Global, Global -> true


module ClausesOf = struct
  module ClauseInfo = struct
    type t = int * locality * Premises.t

    let _equal x y : bool =
      let (k, local, prems) = x in
      let (k', local', prems') = y in
      if Int.equal k k' then
        if local == local' then
          Premises.equal prems prems'
        else false
      else false

    let compare x y : int =
      let (k, local, prems) = x in
      let (k', local', prems') = y in
      match Int.compare k k' with
      | 0 ->
        (match compare_locality local local' with
        | 0 -> Premises.compare prems prems'
        | x -> x)
      | x -> x

    (** [subsumes cl cl'] is true if [cl] subsumes [cl'], i.e. [cl'] is implied by [cl] *)
    let subsumes (i, local, prems) (i', local', prems') =
      if Int.equal i i' && subsumes_locality local local' then
        let find (l, k) =
           match NeList._assq l prems' with
           | exception Not_found -> false
           | k' -> k' <= k
        in
        NeList.for_all find prems
      else false

    (* let of_list (k, prems) = (k, Premises.of_list prems) *)

    let pr pr_index_point concl (k, local, prem) =
      let open Pp in
      hov 0 (Premises.pr pr_index_point prem ++ str " → " ++ pr_index_point (concl, k) ++ pr_local local)
  end

  module ClauseSet = Set.Make(ClauseInfo)
  module SWC = SetWithCardinal(ClauseInfo)(ClauseSet)
  include SWC

  let pr pr_index_point concl cls =
    let open Pp in
    v 0 (prlist_with_sep spc (ClauseInfo.pr pr_index_point concl) (elements cls))

  (* Ocaml >= 4.11 has a more efficient version. *)
  let filter_map p l =
    fold (fun x acc ->
      match p x with
      | None -> remove x acc
      | Some x' -> if x' == x then acc else add x' (remove x acc)) l l

  let shift n cls = if Int.equal n 0 then cls else map (fun (k, local, prems) -> (k + n, local, prems)) cls

  let add cl cls =
    if exists (fun cl' -> ClauseInfo.subsumes cl' cl) cls then cls
    else SWC.add cl cls

  let choose cls = SWC.choose cls

end

type clause = Index.t * ClausesOf.t

module PartialClausesOf = struct
  module ClauseInfo = struct
    type t = int * Premises.t option

    let _equal (x : t) (y : t) : bool =
      let (k, prems) = x in
      let (k', prems') = y in
      if Int.equal k k' then
        Option.equal Premises.equal prems prems'
      else false

    let compare (x : t) (y : t) : int =
      let (k, prems) = x in
      let (k', prems') = y in
      match Int.compare k k' with
      | 0 -> Option.compare Premises.compare prems prems'
      | x -> x

    (* let of_list (k, prems) = (k, Premises.of_list prems) *)

    let pr pr_index_point prem concl (k, prems) =
      let open Pp in
      hov 0 (prlist_with_sep (fun () -> str ",") pr_index_point (prem :: Option.cata Premises.to_list [] prems)
        ++ str " → " ++ pr_index_point (concl, k))
  end

  module ClauseInfos = Set.Make (ClauseInfo)
  module SWC = SetWithCardinal(ClauseInfo)(ClauseInfos)
  include SWC

  let pr pr_index_point prem concl cls =
    let open Pp in
    v 0 (prlist_with_sep spc (ClauseInfo.pr pr_index_point prem concl) (elements cls))

  (* Ocaml >= 4.11 has a more efficient version. *)
  let filter_map p l =
    fold (fun x acc ->
      match p x with
      | None -> remove x acc
      | Some x' -> if x' == x then acc else add x' (remove x acc)) l l

  let shift n cls = if Int.equal n 0 then cls else map (fun (k, prems) -> (k + n, prems)) cls

end

type fwd_clause =
  { prems : PartialClausesOf.t;
    kprem : int;
    concl : Index.t }

module ForwardClauses =
struct
  module PMap = MapWithCardinal (Index) (PartialClausesOf)
  (** This type represents a map from conclusions to increments + premises,
     e.g [other -> concl + n] *)
  type fwd_clauses = PMap.t

  module IntMap = MapWithCardinal (Int) (PMap)
  (** [t] This type represents forward clauses [(_ + k, other -> concl + n)].
    The premises are necessarily non-empty, and the [(_ + k)] one is singled out.
    They are indexed by [k], then by the conlusion universe [concl] and finally
    by [n], in PartialClausesOf.t, which contains the potentially empty [other] premises.
    The cardinal is maintained for fast computations. *)
  type t = IntMap.t

  let add (cl : fwd_clause) (clauses : t) : t =
    IntMap.update cl.kprem
      (fun cls ->
        match cls with
        | None -> Some (PMap.singleton cl.concl cl.prems)
        | Some cls ->
          Some (PMap.update cl.concl
            (fun cls ->
              match cls with
              | None -> Some cl.prems
              | Some cls -> Some (PartialClausesOf.union cl.prems cls))
          cls))
      clauses

    let replace (cl : fwd_clause) (clauses : t) : t =
      IntMap.update cl.kprem
        (fun cls ->
          match cls with
          | None -> Some (PMap.singleton cl.concl cl.prems)
          | Some cls ->
            Some (PMap.add cl.concl cl.prems cls))
        clauses


  (* let union (clauses : t) (clauses' : t) : t = *)
    (* PMap.fold (fun idx cls acc -> add (idx, cls) acc) clauses clauses' *)

  let _union (clauses : t) (clauses' : t) : t =
    let merge_pclauses clauses clauses' =
      let merge _idx cls cls' = PartialClausesOf.union cls cls' in
      PMap.union merge clauses clauses'
    in
    let merge_by_kprem _kprem cls cls' = merge_pclauses cls cls' in
    IntMap.union merge_by_kprem clauses clauses'

  (** [shift n clauses] Shift by n the clauses.
      The resulting clauses represents (_ + k + n, ... -> concl) *)
  let shift n clauses =
    if Int.equal n 0 then clauses else
    IntMap.fold (fun k fwd acc ->
      IntMap.add (k + n) fwd acc)
      clauses IntMap.empty

  let filter (f : int -> Index.t -> PartialClausesOf.t -> bool) clauses =
    IntMap.fold (fun k fwd acc ->
      let fwd = PMap.filter (f k) fwd in
      IntMap.add k fwd acc)
      clauses IntMap.empty

  let filter_map (f : int -> Index.t -> PartialClausesOf.t -> PartialClausesOf.t option) clauses =
    IntMap.fold (fun k fwd acc ->
      let fwd = PMap.filter_map (f k) fwd in
      if PMap.is_empty fwd then acc else IntMap.add k fwd acc)
      clauses IntMap.empty

  let cardinal (cls : t) : int = IntMap.cardinal cls
  let empty = IntMap.empty
  (* let is_empty x = IntMap.is_empty x *)

  let singleton cl = add cl empty

  let fold (f : kprem:int -> concl:Index.t -> prems:PartialClausesOf.t -> 'a -> 'a) (cls : t) : 'a -> 'a =
    IntMap.fold (fun kprem cls acc ->
      PMap.fold (fun concl prems acc ->
        f ~kprem ~concl ~prems acc) cls acc)
      cls

  (* let union clauses clauses' =
    let merge _idx cls cls' =
      match cls, cls' with
      | None, None -> cls
      | None, Some _ -> cls'
      | Some _, None -> cls
      | Some cls, Some cls' ->
        Some (ClausesOf.union cls cls')
    in
    PMap.merge merge clauses clauses' *)

  (* let _partition (p : Index.t -> ClausesOf.t -> bool) (cls : t) : t * t = PMap.partition p cls *)
  (* let _filter (p : Index.t -> ClausesOf.t -> bool) (cls : t) : t = PMap.filter p cls *)

  let pr_clauses pr prem (cls : PMap.t) =
    let open Pp in
    PMap.fold (fun concl cls acc -> PartialClausesOf.pr pr prem concl cls ++ spc () ++ acc) cls (mt())

  let pr pr_prem prem (cls : t) =
    let open Pp in
    IntMap.fold
      (fun kprem cls acc -> pr_clauses pr_prem (prem, kprem) cls ++ acc)
      cls (mt ())

end

module PSet = SetWithCardinal(Index)(Index.Set)

(* Comparison on this type is pointer equality *)
type canonical_node =
  { canon: Index.t;
    local: locality;
    value : int;
    clauses_bwd : ClausesOf.t; (* premises -> canon + k *)
    clauses_fwd : ForwardClauses.t (* canon + k, ... ->  concl + k' *) }

(* A Level.t is either an alias for another one, or a canonical one,
    for which we know the points that are above *)

type entry =
  | Canonical of canonical_node
  | Equiv of locality * Index.t * int

type model = {
  locality : locality;
  entries : entry PMap.t;
  canentries : PSet.t; (* subset of entries that are Canonical *)
  values : int PMap.t option; (* values, superseding the ones attached to canonical nodes if present *)
  canonical : int; (* Number of canonical nodes *)
  table : Index.table }

let set_local m = { m with locality = Local }

let empty_model = {
  locality = Global;
  entries = PMap.empty;
  canentries = PSet.empty;
  values = None;
  canonical = 0;
  table = Index.empty
}

let empty = empty_model

let clear_constraints m =
  let entries =
    let map l entry =
      match entry with
      | Equiv (local, _, _) ->
        Canonical { canon = l; value = 0; local; clauses_bwd = ClausesOf.empty; clauses_fwd = ForwardClauses.empty }
      | Canonical can ->
        Canonical { can with value = 0; clauses_bwd = ClausesOf.empty; clauses_fwd = ForwardClauses.empty }
    in
    PMap.mapi map m.entries
  in
  { m with canentries = (PSet.of_set (PMap.domain entries)); entries; values = None; canonical = 0 }

module CN = struct
  type t = canonical_node
  (* let equal x y = x == y *)
  (* let hash x = Index.hash x.canon *)
  let compare x y = Index.compare x.canon y.canon
end
(* module CSet = CSet.Make(CN) *)

let enter_equiv m u v i =
  { locality = m.locality;
    entries = PMap.modify u (fun _ a ->
          match a with
          | Canonical _ -> Equiv (m.locality, v, i)
          | _ -> assert false) m.entries;
    canentries = PSet.remove u m.canentries;
    canonical = m.canonical - 1;
    values = Option.map (PMap.remove u) m.values;
    table = m.table }

let change_equiv entries u (local, v, i) =
  PMap.modify u (fun _ a ->
      match a with
      | Canonical _ -> assert false
      | Equiv _ -> Equiv (local, v, i)) entries

let change_node m n =
  { m with entries =
    PMap.modify n.canon
      (fun _ a ->
        match a with
        | Canonical _ -> Canonical n
        | _ -> assert false)
      m.entries }

exception Undeclared of Level.t

(* let _ = CErrors.register_handler *)
  (* (function Undeclared l -> Some Pp.(str"Undeclared universe level: " ++ Level.raw_pr l) | _ -> None) *)

(* canonical representative : we follow the Equiv links *)
let rec repr m u =
  match PMap.find u m.entries with
  | Equiv (_, v, k) -> let (can, k') = repr m v in (can, k' + k)
  | Canonical arc -> (arc, 0)
  (* | exception Not_found -> raise (Undeclared (Index.repr u m.table)) *)

let rec repr_expr m (u, k as x) =
  match PMap.find u m.entries with
  | Equiv (_, v, k') -> repr_expr m (v, k' + k)
  | Canonical _ -> x

let rec repr_expr_can m (u, k) =
  match PMap.find u m.entries with
  (* | exception Not_found -> raise (Undeclared (Index.repr u m.table)) *)
  | Equiv (_, v, k') -> repr_expr_can m (v, k' + k)
  | Canonical can -> (can, k)

let repr_can_expr m (u, k) =
  match PMap.find u.canon m.entries with
  | Equiv (_, v, k') -> repr_expr_can m (v, k' + k)
  | Canonical can -> (can, k)

(* canonical representative with path compression : we follow the Equiv links
  and updated them as needed *)
let repr_compress_entries entries u =
  let rec aux u =
    match PMap.find u entries with
    | Equiv (local, v, k) ->
      let entries, (can, k') = aux v in
      if Index.equal v can.canon then entries, (can, k + k')
      else change_equiv entries u (local, can.canon, k + k'), (can, k + k')
    | Canonical can -> entries, (can, 0)
  in aux u

let repr_compress m u =
  let entries, can = repr_compress_entries m.entries u in
  { m with entries }, can

let repr_node m u =
  try repr m (Index.find u m.table)
  with Not_found ->
    CErrors.anomaly ~label:"Univ.repr"
      Pp.(str"Universe " ++ debug_pr_level u ++ str" undefined" ++
      (if Index.mem u m.table then str" (index found)" else str " (index not found in " ++ Level.Set.pr debug_pr_level (Index.dom m.table) ++ str")") ++ str".")

(* let repr m idx =
  try repr m idx
  with Not_found ->
    CErrors.anomaly ~label:"Univ.repr"
      Pp.(str"Universe " ++ debug_pr_level (Index.repr idx m.table) ++ str" undefined.") *)

let remove_node m n =
  let entries =
    PMap.fold (fun idx a entries ->
      match a with
      | Canonical _ -> entries
      | Equiv (_, idx', k) ->
        let idx', _k = repr_expr m (idx', k) in
        if Index.equal idx' n.canon then
          PMap.remove idx entries
        else entries) m.entries m.entries in
  let entries = PMap.remove n.canon entries in
  { m with entries }

let repr_node_expr m (u, k) =
  let (can, k') = repr_node m u in (can, k + k')

let repr_compress_node m u =
  try repr_compress m (Index.find u m.table)
  with Not_found ->
    CErrors.anomaly ~label:"Univ.repr"
      Pp.(str"Universe " ++ debug_pr_level u ++ str" undefined.")

let pr_expr = LevelExpr.pr debug_pr_level

let pr_raw_index_point m idx =
  try pr_expr (Index.repr idx m.table, 0)
  with Not_found -> Pp.str"<point not in table>"

let pr_raw_index_point_expr m (idx, n) =
  try pr_expr (Index.repr idx m.table, n)
  with Not_found -> Pp.str"<point not in table>"

let pr_index_point m (idx, n) =
  let (idx, k) = try let can, k = repr m idx in (can.canon, k) with Not_found -> (idx, 0) in
  try pr_expr (Index.repr idx m.table, k + n)
  with Not_found -> Pp.str"<point not in table>"


let _pr_clause_info m concl cl = ClausesOf.ClauseInfo.pr (pr_index_point m) concl cl

let pr_clauses_of m = ClausesOf.pr (pr_index_point m)

let eq_expr (idxu, ku as u) (idxv, kv as v) =
  u == v || (Index.equal idxu idxv && Int.equal ku kv)

let eq_can_expr (canu, ku as u) (canv, kv as v) =
  u == v || (canu == canv && Int.equal ku kv)

module PremisesRepr =
struct

  let repr m (x : Premises.t) : Premises.t =
    let x' = Premises.smart_map (repr_expr m) x in
    if x' == x then x
    else (* There was a change in the model *)
      Premises.sort x'

  let premise_equal_upto m u v =
    eq_expr (repr_expr m u) (repr_expr m v)

  let equal_upto m prems prems' =
    NeList.equal (premise_equal_upto m) prems prems'

end

module ClausesOfRepr =
struct
  open ClausesOf

  let repr_clause_info m ((k, local, prems as x) : ClausesOf.ClauseInfo.t) : ClausesOf.ClauseInfo.t =
    let prems' = PremisesRepr.repr m prems in
    if prems' == prems then x
    else (k, local, prems')

  let repr m x =
    ClausesOf.map (repr_clause_info m) x

  let clauseinfo_equal_upto m ((k, local, prems) : ClausesOf.ClauseInfo.t) (k', local', prems') =
    Int.equal k k' && local == local' &&
    PremisesRepr.equal_upto m prems prems'

  let mem_upto m (cl : ClauseInfo.t) cls =
    let eq cl' = clauseinfo_equal_upto m cl cl' in
    exists eq cls

  let _subset_upto m cls cls' =
    for_all (fun cl -> mem_upto m cl cls') cls

  let filter_trivial_clause m l (k, local, prems as cl) =
    (* Canonicalize the premises *)
    let prems' = Premises.smart_map (repr_expr m) prems in
     (* Filter out ..., u + k, ... -> u trivial clause *)
    if NeList.exists (fun (can, k') -> Index.equal can l && k' >= k) prems' then None
    else
      if prems' == prems then Some cl
      else
      (* Simplify (u + k, ... u + k -> v + k') clauses to have a single premise by universe *)
      (* let prems' = NeList.uniq eq_expr prems' in *)
      Some (k, local, prems')

  let filter_trivial (m : model) l kprem =
    filter_map (filter_trivial_clause m l) kprem

  let _union_upto m idx x y =
    union (filter_trivial m idx x) (filter_trivial m idx y)

end

module PartialClausesOfRepr =
struct
  open PartialClausesOf

  let repr_clause_info m ((k, prems as x) : ClauseInfo.t) : ClauseInfo.t =
    let prems' = Option.Smart.map (PremisesRepr.repr m) prems in
    if prems' == prems then x
    else (k, prems')

  let repr m x =
    PartialClausesOf.map (repr_clause_info m) x

  let clauseinfo_equal_upto m ((k, prems) : ClauseInfo.t) (k', prems') =
    Int.equal k k' &&
    Option.equal (PremisesRepr.equal_upto m) prems prems'

  let mem_upto m (cl : ClauseInfo.t) cls =
    let eq cl' = clauseinfo_equal_upto m cl cl' in
    exists eq cls

  let _subset_upto m cls cls' =
    for_all (fun cl -> mem_upto m cl cls') cls

  let filter_trivial_clause m (prem:Index.t) (kprem : int) (concl : Index.t) ((k, prems as x) : ClauseInfo.t) : ClauseInfo.t option =
     (* Filter out ..., u + kprem, ... -> u + k trivial clause *)
    if Index.equal prem concl && kprem >= k then
      (* if kprem >= k then the clause is trivial, otherwise
         necessarily other premises can make the clause non-trivial *)
      None
    else
      match prems with
      | None -> (* prem -> concl + k *) Some x
      | Some prems ->
        (* Canonicalize the premises *)
        let prems' = Premises.smart_map (repr_expr m) prems in
        if NeList.exists (fun (can, k') -> Index.equal can concl && k' >= k) prems' then None
        else
          if prems' == prems then Some x
          else
           (* Simplify (u + k, ... u + k -> v + k') clauses to have a single premise by universe *)
           (* let prems' = NeList.uniq eq_expr prems' in *)
           Some (k, Some prems')

  let filter_trivial (m : model) prem kprem concl (cls : t) =
    filter_map (filter_trivial_clause m prem kprem concl) cls

  let _union_upto m prem kprem concl x y =
    union (filter_trivial m prem kprem concl x) (filter_trivial m prem kprem concl y)

  (* let union x y = union x y *)
end

module ForwardClausesRepr =
struct
  open ForwardClauses

  (* let _add_upto (m : model) (cl : fwd_clause) (cls : t) : t = *)
    (* if ClausesOfRepr.subset_upto m kprem (find cl.concl cls) then cls *)
    (* else add cl cls *)

  let reindex_clauses m (clauses : PMap.t) : PMap.t =
    PMap.fold (fun idx clsof acc ->
      let idx', k = repr m idx in
      if Index.equal idx'.canon idx then acc
      else
        let clsof = PartialClausesOf.shift k clsof in
        let acc = PMap.update idx'.canon
          (function None -> Some clsof | Some clsof' -> Some (PartialClausesOf.union clsof clsof')) acc in
        PMap.remove idx acc)
      clauses clauses

  (* let _reindex m (fwd : t) : t = *)
    (* Int.Map.map (fun cls -> reindex_clauses m cls) fwd *)

  let _union_upto (m : model) prem (clauses : t) (clauses' : t) : t =
    let merge_by_kprem kprem cls cls' =
      let merge concl cls cls' = PartialClausesOfRepr._union_upto m prem kprem concl cls cls' in
      let iclauses = reindex_clauses m cls
      and iclauses' = reindex_clauses m cls' in
      PMap.union merge iclauses iclauses'
    in
    let merge kprem cls cls' = merge_by_kprem kprem cls cls' in
    IntMap.union merge clauses clauses'

  let repr_clauses m (clauses : fwd_clauses) : fwd_clauses =
    PMap.fold (fun idx clsof acc ->
      let idx', k = repr m idx in
      let clsof' = PartialClausesOfRepr.repr m clsof in
      if Index.equal idx'.canon idx && clsof' == clsof then acc
      else
        let clsof' = PartialClausesOf.shift k clsof' in
        let acc = PMap.update idx'.canon (function None -> Some clsof' | Some clsofo -> Some (PartialClausesOf.union clsofo clsof')) acc in
        if Index.equal idx'.canon idx then acc else PMap.remove idx acc)
      clauses clauses

  let repr m (cls : t) : t =
    IntMap.map (repr_clauses m) cls

end

let cons_opt_nelist tip rest =
  match rest with
  | None -> NeList.tip tip
  | Some l -> NeList.Cons (tip, l)

let _app_opt_nelist u rest =
  match rest with
  | None -> u
  | Some l -> NeList.append u l

let pr_fwd_clause m prem (cls : ForwardClauses.t) =
  ForwardClauses.pr (pr_index_point m) prem cls

let _pr_clause_info m ((concl, kprem) : clause) =
  pr_clauses_of m concl kprem

type t = model

let eq_pointint m x x' =
  let (can, idx) = repr_expr m x
  and (can', idx') = repr_expr m x' in
  can == can' && Int.equal idx idx'


let canonical_can_premises p =
  Premises.sort (NeList.map (fun (can, k) -> (can.canon, k)) p)

let _canonical_clause (prems, (concl, k)) =
  (canonical_can_premises prems, (concl.canon, k))

let canonical_premises m = NeList.map (repr_expr_can m)

let _pr_clause_idx m cl = pr_clause (pr_index_point m) cl

let check_invariants ~(required_canonical:Level.t -> bool) model =
  let required_canonical u = required_canonical (Index.repr u model.table) in
  let n_canon = ref 0 in
  PMap.iter (fun idx e ->
    match e with
    | Canonical can ->
      assert (Index.equal idx can.canon);
      assert (Index.mem (Index.repr idx model.table) model.table);
      (* assert (PMap.mem idx model.values); *)
      let cls = can.clauses_bwd in
      ClausesOf.iter
        (fun (k, _local, prems) ->
          (* prems -> can + k *)
          if not (k >= 0) then CErrors.user_err Pp.(str "A conclusion has negative weight") else ();
          let prems = canonical_can_premises (canonical_premises model prems) in
          let check_prem (l, lk) =
            if not (lk >= 0) then CErrors.user_err Pp.(str "A premise has negative weight") else ();
            assert (PMap.mem l model.entries);
            let lcan, lk = repr_expr_can model (l, lk) in
            (* Ensure this backward clause of shape [max(... l + lk ... ) -> can + k] is registered as a forward clause for the premise l *)
            match ForwardClauses.IntMap.find_opt lk lcan.clauses_fwd with
            | Some fwd ->
              ForwardClauses.PMap.exists (fun idx kprem ->
              (* kprem = { (kconcl, max ( ... l' + lk' ... )) } -> idx *)
              let (can', shift) = repr model idx in
              let kprem = PartialClausesOf.shift shift kprem in
              can' == can &&
              PartialClausesOf.exists (fun (k', prems') ->
                let prems' = canonical_can_premises (cons_opt_nelist (lcan, lk) (Option.map (canonical_premises model) prems')) in
                Int.equal k k' && NeList.equal (eq_pointint model) prems prems') kprem)
                fwd
            | None -> false
          in
          Premises.iter (fun kprem -> if (check_prem kprem) then () else
            CErrors.user_err Pp.(str"Clause " ++
              pr_fwd_clause model (fst kprem)
              (ForwardClauses.singleton { concl = can.canon; kprem = (snd kprem);
                prems = PartialClausesOf.singleton (k, NeList.filter (fun x -> not (eq_expr kprem x)) prems) }) ++ str" is not registered as a forward clauses for "
              ++ pr_index_point model kprem ++ fnl () ++ str" prems = " ++ _pr_clause_idx model (prems, (can.canon, k)))) prems) cls;
      incr n_canon
    | Equiv (_local, idx', k) ->
      assert (k >= 0);
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
  match m.values with
  | None ->
    Some (PMap.fold (fun _ e acc -> match e with Equiv _ -> acc | Canonical can -> max can.value acc) m.entries 0)
  | Some values ->
    PMap.fold (fun _ v acc -> max_opt (Some v) acc) values None

let model_min (m : model) : int option =
  match m.values with
  | None ->
    Some (PMap.fold (fun _ e acc -> match e with Equiv _ -> acc | Canonical can -> min can.value acc) m.entries 0)
  | Some values ->
    PMap.fold (fun _ v acc -> min_opt (Some v) acc) values None

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
  prlist_with_sep spc (fun idx -> debug_pr_level (Index.repr idx m.table)) (PSet.elements s)

let length_path_from m idx =
  let rec aux = function
    | Canonical _ -> 0
    | Equiv (_local, idx, _) -> succ (aux (PMap.find idx m))
  in aux (PMap.find idx m)

let maximal_path m =
  PMap.fold (fun _ entry acc ->
    match entry with
    | Equiv (_local, idx, _) -> max (succ (length_path_from m idx)) acc
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

let pr_can m can =
  debug_pr_level (Index.repr can.canon m.table)

let pr_can_clauses m ?(local=false) can =
  if not local || (local && can.local == Local) then
    Pp.(str"For " ++ pr_can m can ++ fnl () ++ pr_clauses_of m can.canon can.clauses_bwd ++ fnl () ++
        str"Forward" ++ spc () ++ pr_fwd_clause m can.canon can.clauses_fwd ++ fnl ())
  else Pp.mt ()

let pr_clauses_all ?(local=false) m =
  let open Pp in
  PMap.fold (fun p e acc ->
    match e with
    | Equiv (is_local, p', k) ->
      if not local || (local && is_local == Local) then
        pr_raw_index_point m p ++ str " = " ++ pr_raw_index_point_expr m (p',k) ++ pr_local is_local ++ spc () ++ acc
      else acc
    | Canonical can -> pr_can_clauses ~local m can ++ acc)
    m.entries (Pp.mt ())

let debug_check_invariants m =
  if CDebug.get_flag debug_loop_checking_invariants then
    (debug_invariants_all Pp.(fun () -> str"Checking invariants, " ++ statistics m);
     debug_invariants_all (fun () -> pr_clauses_all m);
     try check_invariants ~required_canonical:(fun _ -> false) m
     with e ->
      debug_invariants_all Pp.(fun () -> str "Broken invariants on: " ++ pr_clauses_all m ++ CErrors.print e);
      raise e)

(* PMaps are purely functional hashmaps *)

let get_canonical_value m c =
  match m.values with
  | None -> c.value
  | Some values -> PMap.find c.canon values

let canonical_value m c =
  match m.values with
  | None -> Some c.value
  | Some values -> PMap.find_opt c.canon values

let set_canonical_value m can v =
  match m.values with
  | None -> change_node m { can with value = v }
  | Some values -> { m with values = Some (PMap.add can.canon v values) }

(* let _repr_canon m can =
  let bwd = repr_clauses_of m can.clauses_bwd in
  let fwd = ForwardClauses.repr m can.clauses_fwd in
  let can = { can with clauses_bwd = bwd; clauses_fwd = fwd } in
  change_node m can, can *)

let add_opt o k =
  if Int.equal k 0 then o else Option.map ((+) k) o

let model_value m l =
  let canon, k =
    try repr m l
    with Not_found -> raise (Undeclared (Index.repr l m.table))
  in add_opt (canonical_value m canon) k

exception VacuouslyTrue

module CanSet =
struct
  type t = ForwardClauses.t PMap.t * int (* cardinal of the PMap.t *)

  let fold f (m, _cm)  acc = PMap.fold f m acc

  let add k v (w, cw) =
    let card = ref cw in
    let upd = function
      | None -> incr card; Some v
      | Some _ -> Some v
    in
    let pm = PMap.update k upd w in
    (pm, !card)

  let _singleton k v = (PMap.singleton k v, 1)

  let mem x (w, _cw) = PMap.mem x w

  let empty = (PMap.empty, 0)

  let _is_empty (w, _cw) = PMap.is_empty w

  let cardinal (_w, cw : t) = cw

  (* let update idx f (w, cw as x) =
    let cwr = ref cw in
    let w' =
      PMap.update idx (fun old ->
        let n = f old in
        match old, n with
        | None, None -> n
        | None, Some _ -> incr cwr; n
        | Some _, None -> cwr := !cwr - 1; n
        | Some _, Some _ -> n)
        w
    in
    if w == w' then x else (w', !cwr) *)

  let _pr m (w, _) =
    let open Pp in
    prlist_with_sep spc (fun (idx, _) -> debug_pr_level (Index.repr idx m.table)) (PMap.bindings w)

  let pr_clauses m (w, _) =
    let open Pp in
    prlist_with_sep spc (fun (idx, fwd) ->
      debug_pr_level (Index.repr idx m.table) ++ str": " ++ spc () ++
      str" Forward clauses " ++ pr_fwd_clause m idx fwd)
      (PMap.bindings w)


  let domain (w, _) = PMap.domain w

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

exception FoundImplication

let get_model_value m l k =
  (match (model_value m l) with None -> raise VacuouslyTrue | Some v -> v) - k

let min_premise (m : model) (premv : int) (prem : Premises.t option) : int =
  let g (l, k) = get_model_value m l k in
  let f prem minl = min minl (g prem) in
  match prem with
  | None -> premv
  | Some prems -> min premv (Premises.fold_ne f g prems)

let update_value prem premk premv concl m (clause : PartialClausesOf.ClauseInfo.t) : int option =
  let (conclk, premises) = clause in
  match min_premise m premv premises with
  | exception VacuouslyTrue -> None
  | k0 when k0 < 0 -> None
  | k0 ->
    let newk = conclk + k0 in
    match canonical_value m concl with
    | Some v when newk <= v -> None
    | _ ->
      debug_updates Pp.(fun () -> str"Updated value of " ++ pr_can m concl ++ str " to " ++ int newk);
      debug_updates Pp.(fun () -> str" due to clause " ++
        pr_clause (pr_index_point m) (cons_opt_nelist (prem, premk) premises, (concl.canon, conclk)));
      Some newk

let check_model_clauses_of_aux m prem premk premv concl cls =
  PartialClausesOf.fold (fun cls m ->
    match update_value prem premk premv concl m cls with
    | None -> m
    | Some newk -> set_canonical_value m concl newk)
    cls m

let find_bwd m idx cls =
  let open ForwardClauses in
  match PMap.find_opt idx cls with
  | Some cls -> cls
  | None ->
    PMap.fold (fun concl cls acc ->
      let can', _k = repr m concl in
      if can'.canon == idx then PartialClausesOf.union cls acc else acc) cls PartialClausesOf.empty

(** Check a set of forward clauses *)
let check_model_fwd_clause_aux ?early_stop prem (fwd : ForwardClauses.t) (acc : PSet.t * model) : PSet.t * model =
  let open ForwardClauses in
  let check () =
    IntMap.fold (fun premk fwd acc ->
      let premv = get_model_value (snd acc) prem premk in
      PMap.fold (fun concl fwd (* (prem + premk), premises -> concl + k *) (wcls, m as acc) ->
        let can, k = repr m concl in
        let fwd = PartialClausesOf.shift k fwd in
        let m' = check_model_clauses_of_aux m prem premk premv can fwd in
        if m == m' then (* not modifed *) acc
        else (PSet.add can.canon wcls, m')) fwd acc)
      fwd acc
  in
  match early_stop with
  | None -> check ()
  | Some (can, k) ->
      let (_, m) = acc in
      IntMap.iter (fun premk fwd ->
        let cls = find_bwd m can.canon fwd in
        let premv = get_model_value (snd acc) prem premk in
        PartialClausesOf.iter (fun cls ->
          match update_value prem premk premv can m cls with
          | None -> ()
          | Some newk -> if k <= newk then raise FoundImplication)
          cls) fwd;
        check ()

let check_model_fwd_aux ?early_stop (cls, m) : PSet.t * model =
  CanSet.fold (fun can fwd m -> check_model_fwd_clause_aux ?early_stop can fwd m) cls (PSet.empty, m)

(* let check_model_fwd_aux ?early_stop (cls, m) =
  (* if CDebug.get_flag debug_check_fwd then
    CanSet.fold (fun _ fwd acc -> check_model_fwd_clause_aux ?early_stop fwd acc) cls
    (PSet.empty, m)
  else  *)
    check_model_fwd_aux ?early_stop (cls, m) *)

let check_clauses_with_premises ?early_stop (cls : CanSet.t) model : (PSet.t * model) option =
  let (updates, model') = check_model_fwd_aux ?early_stop (cls, model) in
  if model == model' then (debug Pp.(fun () -> str"Found a model"); None)
  else Some (updates, model')

(* let _check_model_bwd = check_model *)
let cardinal_fwd w =
  CanSet.fold (fun _idx fwd acc -> ForwardClauses.cardinal fwd + acc) w 0

let check_clauses_with_premises ?early_stop (updates : CanSet.t) model : (PSet.t * model) option =
  let open Pp in
  debug_check_model (fun () -> str"check_model on " ++ int (CanSet.cardinal updates) ++ str" universes, " ++
  int (cardinal_fwd updates) ++ str " clauses");
  check_clauses_with_premises ?early_stop updates model

(*let check_clauses_with_premises = time3 (Pp.str"check_clauses_with_premises") check_clauses_with_premises*)

(* let check_model = time3 (Pp.str "check_model") check_model *)

type 'a result = Loop | Model of 'a * model

let canonical_cardinal m = m.canonical

let can_all_premises_in m w prem =
  Premises.for_all (fun (l, _) -> PSet.mem (fst (repr m l)).canon w) prem

let partition_clauses_of model w cls =
  PartialClausesOf.partition (fun (_k, prems) ->
    Option.cata (can_all_premises_in model w) true prems) cls

let add_bwd prems kprem concl clsof =
  if PartialClausesOf.is_empty prems then clsof
  else ForwardClauses.add { prems; kprem; concl } clsof

let replace_bwd prems kprem concl clsof =
  ForwardClauses.replace { prems; kprem; concl } clsof

let add_canset idx (clauses : ForwardClauses.t) canset =
  if ForwardClauses.IntMap.is_empty clauses then canset
  else CanSet.add idx clauses canset

(* Partition the clauses according to the presence of w in the premises, and only w in the conclusions *)
let partition_clauses_fwd model (w : PSet.t) (cls : CanSet.t) : CanSet.t * CanSet.t * CanSet.t =
  CanSet.fold (fun prem fwd (allw, conclw, conclnw) ->
    let fwdw, fwdpremw, fwdnw =
      ForwardClauses.fold (fun ~kprem ~concl ~prems (fwdallw, fwdnallw, fwdnw) ->
        let concl, conclk = repr model concl in
        let concl = concl.canon in
        let cprems = PartialClausesOf.shift conclk prems in
        if PSet.mem concl w then
          let allw, nallw = partition_clauses_of model w cprems in
          (add_bwd allw kprem concl fwdallw,
           add_bwd nallw kprem concl fwdnallw,
           fwdnw)
        else (fwdallw, fwdnallw, add_bwd cprems kprem concl fwdnw))
        fwd (ForwardClauses.empty, ForwardClauses.empty, ForwardClauses.empty)
    in
    (* We do not keep bindings for all indexes *)
    let allw = add_canset prem fwdw allw (* Premises and conclusions in w *) in
    let conclw = add_canset prem fwdpremw conclw (* Conclusions in w, premises not all in w *) in
    let conclnw = add_canset prem fwdnw conclnw in (* Conclusions not in w, Premises not all in w *)
    (allw, conclw, conclnw))
    cls (CanSet.empty, CanSet.empty, CanSet.empty)

let add_fwd_clause m w cls =
  PSet.fold (fun idx cls ->
    if CanSet.mem idx cls then cls
    else
      let can, _ = repr m idx in
      debug_loop_partition Pp.(fun () -> str"Adding forward clauses of " ++ pr_can m can ++
        pr_fwd_clause m can.canon can.clauses_fwd);
      CanSet.add idx can.clauses_fwd cls)
 w cls

let partition_clauses_fwd = time2 (Pp.str"partition clauses fwd") partition_clauses_fwd

(* If early_stop is given, check raises FoundImplication as soon as
   it finds that the given atom is true *)

let model_points model = model.canentries

let _pr_w m w =
  let open Pp in
  PSet.fold (fun idx pp ->
    pr_index_point m (idx,0) ++ spc () ++ pp) w (mt())

let w_of_canset (c : CanSet.t) = CanSet.domain c

(* let _target_of_canset (c : CanSet.t) =
  CanSet.fold (fun _idx fwd acc ->
    PSet.union (PMap.domain fwd) acc) c PSet.empty *)

let pr_w m w = let open Pp in prlist_with_sep spc (fun x -> pr_index_point m (x,0)) (PSet.elements w)

let _pr_canset m (cls : CanSet.t) : Pp.t =
  let open Pp in
  CanSet.fold (fun idx fwd acc ->
    hov 1 (str "For " ++ pr_index_point m (idx,0) ++ str": " ++
      pr_fwd_clause m idx fwd) ++ fnl () ++ acc) cls (Pp.mt())

let pr_clauses m =
  PMap.fold (fun p e acc ->
    match e with
    | Equiv (local, p', k) ->
      Pp.(pr_raw_index_point m p ++ str " = " ++ pr_index_point m (p', k) ++ pr_local local ++ fnl () ++ acc)
    | Canonical can ->
      let bwd = can.clauses_bwd in
      Pp.(pr_clauses_of m can.canon bwd ++ fnl () ++ acc)) m.entries (Pp.mt ())

(* model is a model for the clauses outside cls *)
let check_canset ?early_stop model ?(w=PSet.empty) (cls : CanSet.t) =
  let v = model_points model in
  let cV = canonical_cardinal model in
  debug_loop Pp.(fun () -> str"All model clauses: " ++ pr_clauses model);
(*   assert (cV = PSet.cardinal v); *)
  debug_check_invariants model;
  let rec inner_loop w cardW premconclw conclw m =
    (* Should consider only clauses with conclusions in w *)
    (* Partition the clauses acscording to the presence of w in the premises *)
    debug_loop Pp.(fun () -> str "Inner loop on " ++ int cardW ++ str" universes: " ++ spc () ++
      hov 2 (str " Premises and conclusions in w: " ++ int (Index.Set.cardinal (w_of_canset premconclw))) ++ fnl () ++
      hov 2 (str " Conclusions in w: " ++ int (Index.Set.cardinal (w_of_canset conclw))));
    (* Warning: m is not necessarily a model for w *)
    let rec inner_loop_partition w cardW premconclw conclw m =
      debug_loop Pp.(fun () -> str "inner_loop_partition on #|premconclw| = " ++ int (CanSet.cardinal premconclw) ++ str" cardW = " ++ int cardW);
      (* debug_loop Pp.(fun () -> str "cls = " ++ pr_w m cls); *)
      match loop w cardW PSet.empty premconclw m with
      | Loop -> Loop
      | Model (wr, mr) ->
        debug_loop Pp.(fun () -> str "inner_loop_partition call to loop results in a model with wr of size " ++ int (CanSet.cardinal wr) );
        (* debug_loop Pp.(fun () -> str "wr = " ++ pr_w mr wr); *)
        (* This is only necessary when clauses do have multiple premises,
           otherwise each clause is either in premconclw and already considered
           or in conclw but then the premise cannot be updated and this is useless work *)
        (match check_clauses_with_premises ?early_stop conclw mr with
        | Some (_wconcl, mconcl) ->
          (* debug_loop Pp.(fun () -> str "clsconcl = " ++ pr_w mconcl clsconcl); *)
          debug_loop Pp.(fun () -> str"Found an update in conclw after finding a model of premconclw in inner loop");
          inner_loop_partition w cardW premconclw conclw mconcl
        | None ->
          debug_loop Pp.(fun () -> str"Inner loop found a model");
          Model (wr, mr))
      in
      (* assert (PSet.cardinal (w_of_canset premconclw) <= cardW); *)
      (* assert (PSet.cardinal (target_of_canset conclw) <= cardW); *)
      inner_loop_partition w cardW premconclw conclw m
  and loop v cV winit (cls : CanSet.t) m =
    debug_loop Pp.(fun () -> str "loop on winit = " ++ pr_w m winit ++ str", #|cls| = " ++ int (cardinal_fwd cls) ++ str" bound is " ++ int cV);
    (* debug_loop Pp.(fun () -> str" cls = : " ++ pr_w m u); *)
    debug_loop_partition Pp.(fun () -> str"initial clauses: " ++ CanSet.pr_clauses m cls);
    (* debug_loop Pp.(fun () -> str"loop iteration on " ++ CanSet.pr_clauses m cls ++ str" with bound " ++ int cV); *)
    match check_clauses_with_premises ?early_stop cls m with
    | None -> debug_loop Pp.(fun () -> str "loop on #|w| = " ++ int (CanSet.cardinal cls) ++ str" found a model, bound is " ++ int cV);
      Model (cls, m)
    | Some (wupd, m) ->
      let w = PSet.union winit wupd in
      debug_loop Pp.(fun () -> str"check_clauses_with_premises updated " ++ int (PSet.cardinal w) ++ str" universes, bound is " ++ int cV);
      (* debug_loop Pp.(fun () -> str"diff between w and cls: " ++ pr_w m (PSet.diff w u)); *)
      (* debug_loop Pp.(fun () -> str"diff between w and cls domain: " ++ pr_w m (PSet.diff w (CanSet.domain cls))); *)
      (* debug_loop Pp.(fun () -> str"diff between cls domain and w: " ++ pr_w m (PSet.diff (CanSet.domain cls) w)); *)
      (* debug_loop Pp.(fun () -> str"cls domain is: " ++ pr_w m (CanSet.domain cls))); *)
      (* debug_loop Pp.(fun () -> str"Updated universes: " ++ pr_w m w ++ str", bound is " ++ int cV); *)
      let cardW = (PSet.cardinal w) in
      if Int.equal cardW cV
      then (debug_loop Pp.(fun () -> str"Found a loop on " ++ int cV ++ str" universes" ); Loop)
      else begin
        (* (if cardW > cV then
          let diff = (PSet.diff w v) in
          if PSet.is_empty diff then assert false;
          Feedback.msg_warning Pp.(str"Cardinal of w > V: " ++ pr_w m diff)); *)

        let cls = add_fwd_clause m wupd cls in
        let (premconclw, conclw, premw) = partition_clauses_fwd m w cls in
        debug_loop_partition Pp.(fun () -> str"partitioning clauses: " ++ CanSet.pr_clauses m cls);
        debug_loop_partition Pp.(fun () -> str"partitioned clauses: from and to w " ++ spc () ++
          CanSet.pr_clauses { m with entries = PMap.empty } premconclw);
        debug_loop_partition Pp.(fun () -> str"partitioned clauses: to w, not from w: " ++ spc () ++
          CanSet.pr_clauses { m with entries = PMap.empty } conclw);
        debug_loop_partition Pp.(fun () -> str"partitioned clauses: from w, not to w " ++ spc () ++
          CanSet.pr_clauses { m with entries = PMap.empty } premw);

        (match inner_loop w cardW premconclw conclw m with
        | Loop -> Loop
        | Model (wc, mc) ->
          (* debug_loop Pp.(fun () -> str "wc = " ++ pr_w mc wc); *)
          debug_loop Pp.(fun () -> str"Checking clauses with premises in w, concl not in w, bound is " ++ int cV);
          (* wc is a subset of w *)
          (* TODO check weird Loop behavior in cumulativity.v without early stop *)
          (match check_clauses_with_premises ?early_stop premw mc with
          | None -> Model (wc, mc)
          | Some (w', mcls) ->
            (* if Int.equal (PSet.cardinal w') cV then Loop else *)
            (debug_loop Pp.(fun () -> str"Resulted in an update of #|w| = " ++ int (PSet.cardinal w') ++
              str" universes, launching back loop. w = " ++ pr_w mcls w ++ spc () ++ str" w' = " ++ pr_w mcls w');
            let cls = add_fwd_clause mcls w' cls in
            loop v cV (PSet.union w w') cls mcls)))
      end
  in
  loop v cV w cls model

let check ?early_stop model w =
  let cls = add_fwd_clause model w CanSet.empty in
  check_canset ?early_stop model ~w cls

let expr_value m (can, k) = add_opt (canonical_value m can) (- k)

let defined_expr_value m (can, k) = get_canonical_value m can - k


let entry_value m e =
  match e with
  | Equiv (_local, idx, k) -> expr_value m (repr_expr_can m (idx, k))
  | Canonical can -> canonical_value m can

let pr_levelmap (m : model) : Pp.t =
  let open Pp in
  h (prlist_with_sep fnl (fun (u, v) ->
    let value = entry_value m v in
    let point = Index.repr u m.table in
    debug_pr_level point ++ str" -> " ++ pr_opt int value) (PMap.bindings m.entries))
  (* Level.Map.pr Pp.int m  *)

let pr_model ?(local=false) model =
  (* Pp.(str "model: " ++ pr_levelmap model) *)
  Pp.(str"clauses: " ++ pr_local model.locality ++ fnl () ++ pr_clauses_all ~local model)

let debug_model m =
  debug_model Pp.(fun () -> str"Model is " ++ pr_levelmap m)

let _repr_clause m (concl, prem as cl : clause) =
  let concl' = (fst (repr m concl)).canon in
  let prem' = ClausesOfRepr.repr m prem in
  if concl' == concl && prem' == prem then cl
  else (concl', prem')

let _modify_can canidx (f : Index.t -> canonical_node -> canonical_node) =
  PMap.modify canidx
    (fun idx entry ->
    match entry with
    | Equiv _ -> assert false
    | Canonical can -> let can' = f idx can in
      if can' == can then entry else Canonical can')

type can_clause = ((canonical_node * int) NeList.t * (canonical_node * int))

let pr_can_clause m (prems, conclk) =
  let open Pp in
  pr_with (pr_can m) conclk ++ str" ≤ " ++ NeList.pr_with_sep (fun () -> str", ") (pr_with (pr_can m)) prems

let remove_premise idx prems =
  let rec aux = function
    | NeList.Tip (idx', _) as l -> if Index.equal idx idx' then None else Some l
    | NeList.Cons ((idx', _) as prem, l') ->
      if Index.equal idx idx' then aux l'
      else match aux l' with
        | None -> Some (NeList.Tip prem)
        | Some l' -> Some (NeList.Cons (prem, l'))
  in aux prems

let add_can_clause_model m ((prems, (canl, conclk)) : can_clause) : (can_clause * model) option =
  let canprems = NeList.map (fun (can, k) -> (can.canon, k)) prems in
  let clof = (conclk, m.locality, canprems) in
  (* Add clause to the backwards clauses of l *)
  let canl' =
    let bwd = ClausesOf.add clof canl.clauses_bwd in
    if bwd == canl.clauses_bwd then canl
    else { canl with clauses_bwd = bwd }
  in
  if canl == canl' then None else
  let m' = change_node m canl' in
  let prems', m' = (* Add clause to the forward clauses from the premises *)
    NeList.fold_map (fun ((idx0, kprem) as prem) entries ->
      let idx = if idx0 == canl then canl' else idx0 in
      let idx' =
        let fwd = ForwardClauses.add { kprem; concl = canl'.canon;
          prems = PartialClausesOf.singleton (conclk, remove_premise idx0.canon canprems) } idx.clauses_fwd in
        if fwd == idx.clauses_fwd then idx
        else { idx with clauses_fwd = fwd }
      in
      if idx0 != idx' then ((idx', kprem), change_node entries idx')
      else (prem, entries))
      prems m'
  in Some ((prems', repr_expr_can m' (canl'.canon, conclk)), m')

let repr_model m =
  let entries' =
    PMap.Smart.map (function
    | Equiv _ as entry -> entry
    | Canonical can as entry ->
      let bwd = ClausesOfRepr.repr m can.clauses_bwd in
      let fwd = ForwardClausesRepr.repr m can.clauses_fwd in
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

let infer_clauses_extension cans m =
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
  match check m cans with
  | Loop ->
    debug Pp.(fun () -> str"loop-checking found a loop");
    None
  | Model (_updates, model) ->
    debug_check_invariants model;
    debug_model model;
    debug Pp.(fun () -> str"loop-checking found a model");
    Some model

(* let infer_clauses_extension ?w = time2 Pp.(str"infer_clauses_extension") (infer_clauses_extension ?w) *)

let pr_incr pr (x, k) =
  Pp.(pr x ++ if k == 0 then mt() else str"+" ++ int k)

(* Precondition: canu.value = canv.value, so no new model needs to be computed.
  Returns the chosen (can + k') universe, the new [other = level + k] binding
  and the new model
*)
let enforce_eq_can model (canu, ku as _u) (canv, kv as _v) : (canonical_node * int) * (Index.t * (Index.t * int)) * t =
  (* assert (expr_value model u = expr_value model v); *)
  (* assert (canu != canv); *)
  (* v := u or u := v, depending on Level.is_source (for Set) *)
  debug_check_invariants model;
  (* let model0 = model in *)
  let can, k, other, diff, model =
    if Level.is_set (Index.repr canu.canon model.table) then
      (* Set + k = l + k' -> k' < k
        -> l = Set + (k - k') *)
      (assert (kv <= ku);
       (canu, ku, canv, ku - kv, enter_equiv model canv.canon canu.canon (ku - kv)))
    else if Level.is_set (Index.repr canv.canon model.table) then
      (assert (ku <= kv);
       (canv, kv, canu, kv - ku, enter_equiv model canu.canon canv.canon (kv - ku)))
    else if Int.equal ku kv then
      (* This heuristic choice has real performance impact in e.g. math_classes/dyadics.v *)
      if ForwardClauses.cardinal canu.clauses_fwd <= ForwardClauses.cardinal canv.clauses_fwd then
        (canv, kv, canu, 0, enter_equiv model canu.canon canv.canon 0)
      else (canu, ku, canv, 0, enter_equiv model canv.canon canu.canon 0)
    else if ku <= kv then
      (canv, kv, canu, kv - ku, enter_equiv model canu.canon canv.canon (kv - ku))
    else
      (* canu + ku = canv + kv /\ kv < ku ->
        canv = canu + (ku - kv)
        *)
      (canu, ku, canv, ku - kv, enter_equiv model canv.canon canu.canon (ku - kv))
  in
  (* other = can + diff *)
  let can, model =
    (* let bwd = ClausesOf.union can.clauses_bwd (ClausesOf.shift diff other.clauses_bwd) in *)
    (* let fwd = ForwardClauses.union can.clauses_fwd other.clauses_fwd in *)
    (* let modeln = { model with entries = PMap.empty; canentries = PSet.empty; } in *)
      (* debug_enforce_eq Pp.(fun () ->
        str"enforcing " ++ pr_raw_index_point modeln can.canon ++ str" = " ++
        pr_incr (pr_raw_index_point model) (other.canon, diff));
      debug_enforce_eq Pp.(fun () -> str"Backward clauses for " ++
      pr_can model can ++ str": " ++ spc () ++
      pr_clauses_of modeln can.canon can.clauses_bwd);
      debug_enforce_eq Pp.(fun () -> str"Backward clauses for " ++
      pr_can model0 other ++ str": " ++ spc () ++
      pr_clauses_of modeln other.canon other.clauses_bwd);
      debug_enforce_eq Pp.(fun () -> str"Previous forward clauses for " ++
        pr_can model can ++ str": " ++ spc () ++
        pr_fwd_clause modeln can.canon can.clauses_fwd);
      debug_enforce_eq Pp.(fun () -> str"Other forward clauses for " ++
        pr_can model0 other ++ str": " ++ spc () ++
        pr_fwd_clause modeln can.canon other.clauses_fwd); *)
    let bwd =
      if CDebug.get_flag debug_switch_union_upto then
        ClausesOf.union can.clauses_bwd (ClausesOf.shift diff other.clauses_bwd)
      else
        ClausesOfRepr._union_upto model can.canon can.clauses_bwd (ClausesOf.shift diff other.clauses_bwd)
    in
    let fwd =
      if CDebug.get_flag debug_switch_union_upto then
        ForwardClauses._union can.clauses_fwd (ForwardClauses.shift diff other.clauses_fwd)
      else
        ForwardClausesRepr._union_upto model can.canon can.clauses_fwd (ForwardClauses.shift diff other.clauses_fwd)
    in
    (* debug_enforce_eq Pp.(fun () -> str"New backward clauses for " ++
    pr_can model can ++ str": " ++ spc () ++
    pr_clauses_of modeln can.canon bwd);
    debug_enforce_eq Pp.(fun () -> str"Add forward clauses for " ++
    pr_can model can ++ str": " ++ spc () ++
    pr_fwd_clause modeln can.canon fwd); *)

    let can = { can with clauses_bwd = bwd; clauses_fwd = fwd } in
    can, change_node model can
  in
  debug_check_invariants model;
  (can, k), (other.canon, (can.canon, diff)), model

let enforce_eq_can = time3 (Pp.str"enforce_eq_can") enforce_eq_can

let _pr_can_constraints m can =
  let open Pp in
  pr_clauses_of m can.canon can.clauses_bwd ++ spc () ++
  str"Forward clauses: " ++ pr_fwd_clause m can.canon can.clauses_fwd

let enforce_eq_can m can can' equivs =
  let can = repr_can_expr m can in
  let can' = repr_can_expr m can' in
  if fst can == fst can' then (can, equivs, m)
  else let can, other, m = enforce_eq_can m can can' in
    (can, other :: equivs, m)

let make_equiv m equiv =
  match equiv with
  | can :: can' :: tl ->
    debug_enforce_eq Pp.(fun () -> str"Unifying universes: " ++
      prlist_with_sep spc (fun can -> pr_incr (pr_can m) can) equiv);
    (* We are about to merge all these universes as they should be equal in the model,
      they should hence have the same values *)
    if CDebug.(get_flag debug_loop_checking_invariants) then
      assert (List.for_all (fun x -> expr_value m x = expr_value m can) (can' :: tl));
    let can, equivs, m =
      List.fold_left (fun (can, equivs, m) can' -> enforce_eq_can m can can' equivs)
        (enforce_eq_can m can can' []) tl
    in
    debug_enforce_eq Pp.(fun () -> str"Chosen canonical universe: " ++ pr_incr (pr_can m) can);
    m, equivs
  | _ -> m, []


let make_equiv = time2 (Pp.str"make_equiv") make_equiv

let _clauses_bwd_univs m cls =
  let open ForwardClauses in
  IntMap.fold (fun _premk cls acc ->
    PMap.fold (fun concl _ acc -> PSet.add (fst (repr m concl)).canon acc) cls acc)
    cls PSet.empty


  type path = (canonical_node * int) list

let compare_can_expr (can, k) (can', k') =
  if can == can' then Int.compare k k'
  else Index.compare can.canon can'.canon

module Path =
struct
  type t = path
  let compare x y =
    CList.compare compare_can_expr x y
end

module PathSet =
struct
  include Set.Make(Path)

  let filter_map p l =
    fold (fun x acc ->
      match p x with
      | None -> remove x acc
      | Some x' -> if x' == x then acc else add x' (remove x acc)) l l

end

module Status = struct
  (* module Internal = Hashtbl.Make(CN) *)
  module M = Map.Make(CN)

  type status =
    | Processing
    | Merged of PathSet.t
    | NonMerged

  type t = status M.t

  (** we could experiment with creation size based on the size of [g] *)
  let empty = M.empty

  let replace m can s = M.add can s m
  let find m c = M.find c m

  let add c s m = M.add c s m
  let remove c m = M.remove c m

  (* let intersection (x : t) (y : t) : t =
    let filter can (merge, k) =
      match find y can with
      | exception Not_found -> Some (false, k)
      | (merge', _k') -> Some (merge && merge', k)
    in
    Internal.filter_map_inplace filter x;
    x
  let merge (x : t) (y : t) : t =
    Internal.iter (fun can (merge, k) ->
      if merge then
        match find x can with
        | exception Not_found ->
          Internal.add x can (merge, k)
        | (merge', _) ->
          if not merge' then
            Internal.add x can (merge, k))
      y;
    x *)
end

(*
module Status = struct
  module Merged = Map.Make(CN)
  module NonMerged = Set.Make(CN)

  type merge_info = int Merged.t
  type merged = merge_info Merged.t
  type t = {
    merged : merged;
    (* can -> (k, m) records (can, k) as being merged, as well as all expressions in m *)
    nonmerged : NonMerged.t
  }


  let inter_merged m m' =
    let merge _ mi mi' =
      match mi, mi' with
      | Some _, Some _ -> mi
      | _, _ -> None
    in
    Merged.merge merge m m'


  (** we could experiment with creation size based on the size of [g] *)
  let create (_m:model) =
    { merged = Merged.empty; nonmerged = NonMerged.empty }

  let find s c =
    try Merged.find c s.merged
    with Not_found ->
      if NonMerged.mem c s.nonmerged then Merged.empty
      else raise Not_found
  let replace s can merge =
    if not (Merged.is_empty merge) then
      { merged = Merged.add can merge s.merged; nonmerged = NonMerged.remove can s.nonmerged }
    else { s with nonmerged = NonMerged.add can s.nonmerged }

end*)

(** [shrink_premises prems] Simplifies the clause [prems -> concl + conclk]
  by removing redundant hypotheses [l + k] when [l + k'] with [k' > k] is also present in [prems],
  potentially returning [None] if the clause is trivial, that is, has a premise [concl + k]
  with [k >= conclk].
*)
let shrink_premises prems concl conclk =
  (* This assumes a single Index.t * nat binding by index and preserves it *)
  let update ((prem, k) as x) prems =
    match prems with
    | None -> Some (NeList.Tip x)
    | Some prems ->
      let rec aux prems =
      match prems with
      | NeList.Tip ((prem', k') as p) ->
        if Index.equal prem prem' then
          if k <= k' then prems
          else NeList.Tip x
        else NeList.Cons (x, NeList.Tip p)
      | NeList.Cons ((prem', k') as p, prems') ->
        if Index.equal prem prem' then
          if k <= k' then prems
          else NeList.Cons ((prem, k), prems')
        else
          let prems''= aux prems' in
          if prems' == prems'' then prems else NeList.Cons (p, prems'')
      in Some (aux prems)
  in
  let rec aux acc = function
    | NeList.Tip ((prem, k) as x) ->
      if Index.equal prem concl && k >= conclk then acc else update x acc
    | NeList.Cons ((prem, k) as x, xs) ->
      if Index.equal prem concl && k >= conclk then aux acc xs
      else aux (update x acc) xs
  in aux None prems

let _simplify_premises m prems concl conclk : Premises.t option =
  let prems' = Premises.smart_map (repr_expr m) prems in
  shrink_premises prems' concl conclk

let repr_premises model (prems : Premises.t) =
  Premises._map (repr_expr_can model) prems

let repr_can_premises model prems =
  Premises._map (repr_can_expr model) prems

let pr_can_expr m (c, n) = pr_index_point m (c.canon, n)

let pr_can_prems m = Premises.pr (pr_can_expr m)

let pr_path model path =
  let open Pp in
  prlist_with_sep spc (pr_can_expr model) path

let pr_paths model paths =
  let open Pp in
  if PathSet.is_empty paths then str"∅"
  else str"{ " ++ Pp.prlist_with_sep (fun () -> Pp.str ", ") (pr_path model) (PathSet.elements paths) ++ str" }"

let pr_status model s =
  let open Pp in
  match s with
  | Status.Processing -> str "being processed"
  | Status.Merged ps -> str "merged with paths: " ++ pr_paths model ps
  | Status.NonMerged -> str "not merged"

let find_loop can path =
  let rec aux path =
    match path with
    | [] -> None
    | (x, _) as hd :: xs ->
      if x == can then Some [hd]
      else match aux xs with
        | None -> None
        | Some p -> Some (hd :: p)
  in aux path

let _find_first prems path =
  let rec aux = function
    | [] -> []
    | hd :: tl -> if NeList.exists (fun cank -> eq_can_expr cank hd) prems then [hd] else hd :: aux tl
  in aux path

let intersect_psets p p' =
  let fold path acc =
    let fold' path' acc =
      match CList.intersect eq_can_expr path path' with
      | [] | [_] -> acc
      | l -> PathSet.add l acc
    in
    PathSet.fold fold' p' acc
  in
  PathSet.fold fold p PathSet.empty

let chop_at can path =
  let rec aux = function
    | [] -> None
    | hd :: tl ->
      if eq_can_expr can hd then Some ([hd], tl)
      else match aux tl with
      | Some (pref, suff) -> Some (hd :: pref, suff)
      | None -> None
  in aux path

let replace_path_prefix can newp oldp =
  match chop_at can oldp with
  | None -> None
  | Some (pref, suff) ->
    let newsuff = CList.intersect eq_can_expr newp suff in
    Some (pref @ newsuff)

let replace_prefix_if_included can path ps =
  let filter path' = replace_path_prefix can path path' in
  PathSet.filter_map filter ps

(** [find_to_merge_bwd model status u v] Search for an equivalence class of universes backward from u to v.
  @assumes u -> v is consistent *)
let find_to_merge_bwd model (status : Status.t) prems (canv, kv) =
  (* let nb_univs = ref 0 and nb_cstrs = ref 0 in *)
  debug_find_to_merge_global Pp.(fun () -> str"Searching from " ++ Premises.pr (pr_can_expr model) prems ++ str" to " ++
    pr_can_expr model (canv, kv));
  let canvalue = defined_expr_value model (canv, kv) in
  let rec backward status path (can, k) : Status.t * PathSet.t =
    debug_find_to_merge Pp.(fun () -> str"visiting " ++ pr_can_expr model (can, k) ++ str" from path " ++ pr_path model path);
    match Status.find status can with
    | cstatus ->
      debug_find_to_merge Pp.(fun () -> str"Found " ++ pr_can_expr model (can, k) ++ str" to be " ++
        pr_status model cstatus);
      (match cstatus with
      | Status.Processing ->
        (match find_loop can path with
        | Some path -> status, PathSet.singleton path
        | None -> status, PathSet.empty)
      | Status.Merged ps ->
        (** This level was previously merged coming from a potentially different path, e.g.
            With constraints (canv <= ) x <= prefix <= u <= ... <= canv  /\ y <= prefix' <= u
            Searching from max(x,y) to canv
            When we find u from y :: prefix' we can reuse the paths merged through u that are
            included in prefix'
            *)
        let merged = replace_prefix_if_included (can,k) path ps in
        let status = Status.(replace status can (Merged merged)) in
        status, merged
      | Status.NonMerged -> status, PathSet.empty)
    | exception Not_found ->
      let isv = can == canv && Int.equal k kv in
      let domerge = isv || Premises._exists (fun (canu, ku) -> (can == canu && Int.equal k ku)) prems in
      let path = ((can, k) :: path) in
      let merge = if domerge then PathSet.singleton path else PathSet.empty in
      if isv then status, merge else
      let status = Status.replace status can Status.Processing in
      (* let () = incr nb_univs in *)
      let cls = can.clauses_bwd in
      debug_find_to_merge Pp.(fun () -> if domerge then pr_can_expr model (can,k) ++ str " is marked as merged already" else str" is not merged yet");
      if ClausesOf.is_empty cls then status, merge else begin
        debug_find_to_merge Pp.(fun () -> str"Searching through " ++ int (ClausesOf.cardinal cls) ++ str" backward clauses of " ++ pr_can model can);
          (* str " Canonical: " ++ int (PSet.cardinal (clauses_bwd_univs model cls))); *)
        let merge_fn (clk, _local, prems) (status, merge as acc) =
          (* Ensure there is indeed a backward clause of shape canv -> can *)
          (* prems -> can + clk *)
          if clk > k then acc (* Looking at prems -> can + k + S k' clause, not applicable to find a loop with canv *)
          else (* k >= clk *)
            let status, mergeprem = backward_premises k clk (repr_premises model prems) (status, path) in
            status, PathSet.union merge mergeprem
        in
        let status, merge = ClausesOf.fold merge_fn cls (status, merge) in
        if PathSet.is_empty merge then
          Status.add can Status.NonMerged status, merge
        else
          let status = Status.add can (Status.Merged merge) status in
          status, merge
      end
  and backward_premises k clk prems (status, path) =
    let merge_prem status (prem, kprem) =
      let p = repr_can_expr model (prem, kprem + (k - clk)) in
      (* Stay in the same equivalence class *)
      let premvalue = defined_expr_value model p in
      if Int.equal premvalue canvalue then
        (* prem + kprem -> can + clk      , with k >= clk implies
            prem + kprem + (k - clk) -> can + k by upwards closure with shifting *)
          backward status path p
      else status, PathSet.empty
    in
    let merge_prem status p =
      let status, merge = merge_prem status p in
      debug_find_to_merge Pp.(fun () -> str"Paths to premise " ++ pr_can_expr model p ++ str" = " ++
        pr_paths model merge);
      status, merge
    in
    debug_find_to_merge Pp.(fun () -> str"Searching through the premises " ++ Premises.pr (pr_can_expr model) prems);
    match prems with
    | NeList.Tip p ->
      let status, mergep = merge_prem status p in
      debug_find_to_merge Pp.(fun () -> str"Paths to premises " ++ Premises.pr (pr_can_expr model) prems ++ str" are " ++
        pr_paths model mergep);
      status, mergep
    | NeList.Cons (p, ps) ->
      (* Multiple premises: we will merge the intersection of merged universes in each possible path,
         if all premises are mergeable. *)
      let fold prem (status, merge) =
        if not (PathSet.is_empty merge) then
          let status, mergeprem = merge_prem status prem in
          if not (PathSet.is_empty mergeprem) then
            status, intersect_psets mergeprem merge
          else (* At least one premise is not bounded by v, we keep the non-mergeable
            universes found during the search *)
            status, mergeprem
        else status, merge
      in
      let status', mergemax = NeList.fold fold ps (merge_prem status p) in
      debug_find_to_merge Pp.(fun () -> str"Paths from premises " ++ Premises.pr (pr_can_expr model) prems ++ str" are " ++
        pr_paths model mergemax);
      status', mergemax
  in
  let _status, merge = backward_premises 0 0 prems (status, []) in
  debug_find_to_merge_global Pp.(fun () -> str"Backward search terminated with paths " ++ pr_paths model merge);
  if PathSet.is_empty merge then [] else
    let merge_fn p acc = if List.length p > 1 then p :: acc else acc in
    PathSet.fold merge_fn merge []

(** [find_to_merge_bwd model status u v] Search for an equivalence class of universes backward from u to v *)
(* let find_to_merge_bwd = *)
  (* time4 (Pp.str "find_to_merge_bwd") find_to_merge_bwd *)

(** [get_explanation model prems concl] computes the path [concl -> prems] backward from prems, that make [prems -> concl] inconsistent
    @requires prems -> concl is inconsistent
*)
let get_explanation model prems (canv, kv) =
  debug_find_to_merge Pp.(fun () -> str"Searching from " ++ Premises.pr (pr_can_expr model) prems ++ str" to " ++
    pr_can_expr model (canv, kv));
  let rec backward status path (can, k) : Status.t * PathSet.t =
    debug_find_to_merge Pp.(fun () -> str"visiting " ++ pr_can model can ++ str" from path " ++ pr_path model path);
    match Status.find status can with
    | cstatus ->
      debug_find_to_merge Pp.(fun () -> str"Found " ++ pr_can model can ++ str" to be " ++
        pr_status model cstatus);
      (match cstatus with
      | Status.Processing ->
        (match find_loop can path with
        | Some path -> status, PathSet.singleton path
        | None -> status, PathSet.empty)
      | Status.Merged _ -> assert false (* No merging in get_explanation *)
      | Status.NonMerged -> status, PathSet.empty)
    | exception Not_found ->
      let isv = can == canv && k <= kv in
      let domerge = isv || Premises._exists (fun (canu, ku) -> (can == canu && Int.equal k ku)) prems in
      let path = ((can, k) :: path) in
      let path = if (k < kv) then (can, kv) :: path else path in
      let merge = if domerge then PathSet.singleton path else PathSet.empty in
      if isv then status, merge else
      let status = Status.replace status can Status.Processing in
      (* let () = incr nb_univs in *)
      let cls = can.clauses_bwd in
      debug_find_to_merge Pp.(fun () -> if domerge then pr_can model can ++ str " is marked as merged already" else str" is not merged yet");
      if ClausesOf.is_empty cls then status, merge else begin
        debug_find_to_merge Pp.(fun () -> str"Searching through " ++ int (ClausesOf.cardinal cls) ++ str" backward clauses of " ++ pr_can model can);
          (* str " Canonical: " ++ int (PSet.cardinal (clauses_bwd_univs model cls))); *)
        let merge_fn (clk, _local, prems) (status, merge) =
          (* prems -> can + clk *)
          let status, mergeprem = backward_premises k clk (repr_premises model prems) (status, path) in
          status, PathSet.union merge mergeprem
        in
        let status, merge = ClausesOf.fold merge_fn cls (status, merge) in
        if PathSet.is_empty merge then
          Status.add can Status.NonMerged status, merge
        else
          let status = Status.remove can status in
          status, merge
      end
  and backward_premises k clk prems (status, path) =
    let merge_prem status (prem, kprem) =
      let p = repr_can_expr model (prem, kprem + (k - clk)) in
      (* Stay in the same equivalence class *)
      (* prem + kprem -> can + clk      , with k >= clk implies
         prem + kprem + (k - clk) -> can + k by upwards closure with shifting *)
      backward status path p
    in
    debug_find_to_merge Pp.(fun () -> str"Searching through the premises " ++ Premises.pr (pr_can_expr model) prems);
    match prems with
    | NeList.Tip p ->
      let status, mergep = merge_prem status p in
      debug_find_to_merge Pp.(fun () -> str"Paths from premises " ++ Premises.pr (pr_can_expr model) prems ++ str" are " ++
        pr_paths model mergep);
      status, mergep
    | NeList.Cons (p, ps) ->
      (* Multiple premises: we will merge the intersection of merged universes in each possible path,
         if all premises are mergeable. *)
      let fold prem (status, merge) =
        if not (PathSet.is_empty merge) then
          let status, mergeprem = merge_prem status prem in
          if not (PathSet.is_empty mergeprem) then
            status, intersect_psets mergeprem merge
          else (* At least one premise is not bounded by v, we keep the non-mergeable
            universes found during the search *)
            status, mergeprem
        else status, merge
      in
      let status', mergemax = NeList.fold fold ps (merge_prem status p) in
      debug_find_to_merge Pp.(fun () -> str"Paths from premises " ++ Premises.pr (pr_can_expr model) prems ++ str" are " ++
        pr_paths model mergemax);
      status', mergemax
  in
  let _status, merge = backward_premises 0 0 prems (Status.empty, []) in
  debug_find_to_merge Pp.(fun () -> str"Backward search terminated with paths " ++ pr_paths model merge);
  if PathSet.is_empty merge then [] else
    let merge_fn p acc = p :: acc in
    PathSet.fold merge_fn merge []

type equivalences = (Index.t * (Index.t * int)) list

(** [simplify_clauses_between model u v] Checks if [v <= u] holds, in which case it
  merges the equivalence classes of universes between [u] and [v]. If [v] is the lub
  of [v1..vn], they might not be merged while other universes between [u] and [v] are merged.
    @param model Assumes [u <= v] holds already
    @return a potentially modified model, without changing any values *)
let simplify_clauses_between model (canu, _ as u) prems : t * equivalences =
  let premsmax = (Premises._fold (fun u m -> max_opt (expr_value model u) m) prems None) in
  if not (Option.equal Int.equal premsmax (expr_value model u)) then
      (* We know v -> u and check for u -> v, this can only be true if both levels
        already have the same value *)
    (debug_enforce_eq Pp.(fun () -> pr_can_prems model prems ++ str"'s value =  " ++
        pr_opt int premsmax ++ str" and " ++ pr_can model canu ++ str "'s value = "
      ++ pr_opt int (canonical_value model canu) ++ str", no simplification possible");
    model, [])
  else
    let status = Status.empty in
    let () = debug_enforce_eq Pp.(fun () -> str"simplify_clauses_between calling find_to_merge") in
    let equiv =
      (* if CDebug.get_flag debug_switch_find_to_merge then *)
        (* find_to_merge_fwd model status u v *)
      (* else  *)
        find_to_merge_bwd model status prems u
    in
    let make_equiv (model, equivs) path =
      let m, equivs' = make_equiv model path in
      m, equivs' @ equivs
    in
    List.fold_left make_equiv (model,[]) equiv

type nat = int
type can_constraint = (canonical_node * nat) * (canonical_node * nat)

let can_clause_of_can_constraint (cstr : can_constraint) : can_clause =
  let (l, r) = cstr in (* l + k <= r *)
  (NeList.tip r, l)

type 'a check_function = t -> 'a -> 'a -> bool

let update_model_value (m : model) can k' : model =
  let v = canonical_value m can in
  let k' = max_opt v k' in
  if Option.equal Int.equal k' v then m
  else
    (debug Pp.(fun () -> str"Updated value of " ++ pr_can m can ++ str " to " ++ pr_opt int k');
    set_canonical_value m can (Option.get k'))

(** [min_can_premise model prem]
    @raises VacuouslyTrue if there is an undefined level in the premises *)
let min_can_premise model prem =
  let g (l, k) = (match canonical_value model l with Some v -> v | None -> raise VacuouslyTrue) - k in
  let f prem minl = min minl (g prem) in
  Premises.fold_ne f g prem

let update_model ((prems, (can, k)) : can_clause) (m : model) : PSet.t * model =
  match min_can_premise m prems with
  | exception VacuouslyTrue -> (PSet.empty, m)
  | k0 ->
    let m' = update_model_value m can (Some (k + k0)) in
    if m' != m then
      let canset = CanSet.add can.canon can.clauses_fwd CanSet.empty in
      match check_clauses_with_premises canset m' with
      | Some (modified, wm) -> (modified, wm)
      | None -> (PSet.empty, m')
    else (PSet.empty, m)

let infer_clause_extension cl minit =
  (* debug Pp.(fun () -> str "current model is: " ++ pr_levelmap model); *)
  (* debug_check_invariants minit; *)
  match add_can_clause_model minit cl with
  | None ->
    (* The clause was already present in the model *)
     Some minit
  | Some (cl, m) ->
    let cans, m = update_model cl m in
    if PSet.is_empty cans then begin
      (* The clause is already true in the current model,
        but might not be in an extension, so we keep it *)
      (* debug Pp.(fun () -> str"Clause is valid in the current model"); *)
      (* debug_clauses Pp.(fun () -> str"Clauses: " ++ pr_clauses model m.clauses); *)
      Some m
    end else
      (* The clauses are not valid in the current model, we have to find a new one *)
      (* debug Pp.(fun () -> str"Enforcing clauses requires a new inference"); *)
      infer_clauses_extension cans m

let infer_clause_extension cl m =
  debug_global Pp.(fun () -> str"Enforcing clause " ++ pr_can_clause m cl);
  let res = infer_clause_extension cl m in
  match res with
  | None -> debug_global Pp.(fun () -> str"Resulted in a loop"); res
  | Some m ->
    debug_check_invariants m;
    debug_global Pp.(fun () -> str" is consistent"); res


(* A clause premises -> concl + k might hold in the current minimal model without being valid in all
   its extensions.

   We generate the minimal model starting from the premises. I.e. we make the premises true.
   Then we check that the conclusion holds in this minimal model.  *)

let check_one_clause model prems concl k =
  (* premise -> concl + k ? *)
  (* debug Pp.(fun () -> str"Checking entailment: " ++ prlist_with_sep (fun () -> str",") (pr_can_expr model) (NeList.to_list prems) ++ *)
    (* str " -> " ++ pr_can_expr model (concl, k)); *)
  (* if (Level.is_set (Index.repr concl.canon model.table)) && k == 0 then true else *)
  let model = NeList.fold (fun prem values ->
    let x, k = repr_can_expr model prem in
    update_model_value values x (Some k)) prems
    { model with values = Some PMap.empty }
  in
  let w, cls = NeList.fold (fun (prem, _k) (w, cls) -> (PSet.add prem.canon w, CanSet.add prem.canon prem.clauses_fwd cls)) prems (PSet.empty, CanSet.empty) in
  (* We have a model where only the premise is true, check if the conclusion follows *)
  (* debug Pp.(fun () -> str"Launching loop-checking to check for entailment"); *)
  match check_canset ~early_stop:(concl, k) model ~w cls with
  | exception FoundImplication ->
    (* debug Pp.(fun () -> str"loop-checking found the implication early"); *)
    true
  | Loop ->
    (* debug Pp.(fun () -> str"loop-checking found a loop"); *)
    false
  | Model (_updates, model') ->
    (* debug Pp.(fun () -> str"loop-checking found a model"); *)
    (* debug_check_invariants model'; *)
    (* debug_model model'; *)
    match canonical_value model' concl with
    | None ->
      (* debug Pp.(fun () -> str"Conclusion has no value in the minimal model, not implied"); *)
      false
    | Some value ->
      (* debug Pp.(fun () -> str"Conclusion has value " ++ int value ++ *)
        (* str" in the minimal model, expecting conclusion + " ++ int k ++ str " to hold"); *)
      k <= value

let _check_one_clause = check_one_clause

let check_one_clause_loop model prems concl conclk =
  (* premises -> concl + k ?.

    Add concl + k -> p + 1 for all p ∈ premises and check for consistency.
    If there is a loop the clause holds, otherwise the clause doesn't

  *)
  debug Pp.(fun () -> str"Checking entailment: " ++ prlist_with_sep (fun () -> str",") (pr_can_expr model) (NeList.to_list prems) ++
    str " -> " ++ pr_can_expr model (concl, conclk));
  (* if (Level.is_set (Index.repr concl.canon model.table)) && k == 0 then true else *)
  debug Pp.(fun () -> str"Checking consistency of adding negation of the clause");
  let _, holds =
    NeList.fold (fun (prem, k) (m, result) ->
      if result then (m, result)
      else
        let cl = can_clause_of_can_constraint (repr_expr_can m (prem.canon, k + 1), repr_expr_can m (concl.canon, conclk)) in
        let res = infer_clause_extension cl m in
        match res with
        | None -> (m, true)
        | Some m -> (m, false))
      prems (model, false) in
  if holds then
    (debug Pp.(fun () -> str"The clause does hold"); holds)
  else
    (debug Pp.(fun () -> str"The clause does not hold, its negation is consistent"); holds)

let _check_one_clause_loop = check_one_clause_loop

(* (* [infer_extension u v m] enforces [u <= v] in [m] *)
let infer_extension x y m =
  let cl = can_clause_of_can_constraint (x, y) in (* x <= y *)
  infer_clause_extension cl m

(** [infer_extension u v m] enforces [u <= v] in [m] *)
let infer_extension =
  time3 Pp.(str "infer_extension") infer_extension *)

(** Enforce u <= v and check if v <= u already held, in that case, enforce u = v *)
let enforce_leq_can u v m =
  let cl = (v, u) in
  (* let vcan = v in *)
  (* debug_global Pp.(fun () -> str"enforce_leq " ++ pr_can_clause m cl); *)
  debug_enforce_eq Pp.(fun () -> str"enforce_leq " ++ pr_can_clause m cl);
   (* ++ spc () ++
    pr_can_clauses m (fst vcan) ++ pr_can_clauses m (fst u)); *)
  if (match v with NeList.Tip v -> eq_can_expr u v | _ -> false) then
    (debug_enforce_eq Pp.(fun () -> str"already equal"); Some (m, []))
  else
  match infer_clause_extension (v, u) m with
  | None -> None
  | Some m' ->
    if m' != m then
      (debug_enforce_eq Pp.(fun () -> str"enforce_leq did modify the model, looking for inverse clause");
      let u = repr_can_expr m' u in
      let v = repr_can_premises m' v in
      Some (simplify_clauses_between m' u v))
    else Some (m, [])

let enforce_leq_level u v m =
  let m, canu = repr_compress_node m u in
  let m, canv = repr_compress_node m v in
  enforce_leq_can canu (NeList.Tip canv) m

let _get_proper_value m can =
  match canonical_value m can with
  | Some v -> v
  | None -> raise (Undeclared (Index.repr can.canon m.table))

let enforce_eq_level u v m =
  let (canu, ku as u) = repr_node m u in
  let (canv, kv as v) = repr_node m v in
  debug_enforce_eq Pp.(fun () -> str"enforce_eq: " ++ pr_can_expr m u ++ str" = " ++ pr_can_expr m (canv, kv));
  match enforce_leq_can v (NeList.Tip u) m with
  | None -> None
  | Some (m', equivs) ->
    let canu' = repr_expr_can m' (canu.canon, ku) in
    let canv' = repr_expr_can m' (canv.canon, kv) in
    match enforce_leq_can canu' (NeList.Tip canv') m' with
    | None -> None
    | Some (m', equivs') -> Some (m', equivs @ equivs')

let enforce_eq_level = time3 (Pp.str "enforce_eq_level") enforce_eq_level

let check_eq_level_expr u v m =
  let vl = v in debug_global Pp.(fun () -> str"Checking equality of representatives " ++ LevelExpr.pr debug_pr_level u ++ str " and " ++ LevelExpr.pr debug_pr_level vl);
  let canu, ku = repr_node_expr m u in
  let canv, kv = repr_node_expr m v in
  canu == canv && Int.equal ku kv

(* max u_i <= v <-> ∧_i u_i <= v *)
let clauses_of_le_constraint u v cls =
  List.fold_right (fun (u, k) cls -> (Universe.repr v, (u, k)) :: cls) (Universe.repr u) cls

let clauses_of_constraint (u : Universe.t) k (v : Universe.t) cls =
  match k with
  | Le -> clauses_of_le_constraint u v cls
  | Eq -> clauses_of_le_constraint u v (clauses_of_le_constraint v u cls)

let can_clause_of_clause m (prems, concl) =
  let prems = NeList.of_list (List.map (fun prem -> repr_node_expr m prem) prems) in
  let concl = repr_node_expr m concl in
  (prems, concl)

let infer_extension (prems, (concl, k)) m = enforce_leq_can (concl, k) prems m

(* let debug_filter, _ = CDebug.create_full ~name:"loop-checking-filter" () *)

(** Simplify u <= max (Set, v) clauses to u <= v and filter away u <= ... u + n , ... clauses, always valid *)
let filter_trivial_can_clause m ((prems, (concl, k as conclk)) : can_clause) : can_clause option =
  (* Trivial ... u + k + n ... -> u + k clause *)
  if NeList.exists (fun (prem, k') -> prem == concl && k' >= k) prems then
    None
  else
    (* Filter out `Set` from max(Set, u) -> v constraints *)
    let canset = Index.find Level.set m.table in
    let prems =
      match NeList.filter (fun (prem, k) -> not (Index.equal prem.canon canset && Int.equal k 0)) prems with
      | Some prems -> prems (* There were at least two premises in the rule *)
      | None -> prems
    in
    Some (prems, conclk)

let infer_extension_filter cl (m, equivs as x) =
  match filter_trivial_can_clause m cl with
  | None -> Some x
  | Some cl ->
    match infer_extension cl m with
    | None -> None
    | Some (m, equivs') -> Some (m, equivs @ equivs')

let _repr_can_clause m (prems, conclk) =
  let concl = repr_can_expr m conclk in
  let prems = repr_can_premises m prems in
  (prems, concl)

let unrepr_equivalences model (idxs : equivalences) =
  List.map (fun (idx, (idx', k)) -> (Index.repr idx model.table, (Index.repr idx' model.table, k))) idxs

let enforce_constraint u k v (m : t) =
  let cls = clauses_of_constraint u k v [] in
  List.fold_left (fun m cl ->
    match m with
    | None -> None
    | Some (m, equivs) -> infer_extension_filter (can_clause_of_clause m cl) (m, equivs)) (Some (m, [])) cls

let enforce u k v m =
  match Universe.repr u, k, Universe.repr v with
  | [(u, 0)], Eq, [(v, 0)] -> enforce_eq_level u v m
  | [(u, 0)], Le, [(v, 0)] -> enforce_leq_level u v m
  | _, _, _ -> enforce_constraint u k v m

let enforce u k v m =
  let res = enforce u k v m in
  Option.map (fun (m, equivs) -> m, unrepr_equivalences m equivs) res

let enforce_eq u v m =
  debug_enforce_eq (let vc = v in Pp.(fun () -> Universe.pr debug_pr_level u ++ str" = " ++ Universe.pr debug_pr_level vc ++ pr_local m.locality));
  enforce u Eq v m
let enforce_leq u v m =
  debug_enforce_eq (let vc = v in Pp.(fun () -> Universe.pr debug_pr_level u ++ str" ≤ " ++ Universe.pr debug_pr_level vc ++ pr_local m.locality));
  enforce u Le v m
let enforce_lt u v m = enforce_leq (Universe.addn u 1) v m

let check_clause model cl =
  match filter_trivial_can_clause model cl with
  | None -> true
  | Some (prems, (concl, k)) ->
    check_one_clause model prems concl k

let check_clause = time2 (Pp.str "check_clause") check_clause

let check_constraint (m : t) u k u' =
  debug_global Pp.(fun () -> str"Checking " ++ Constraints.pr debug_pr_level (Constraints.singleton (u,k,u')));
  let cls = clauses_of_constraint u k u' [] in
  let res = List.fold_left (fun check cl -> check && check_clause m (can_clause_of_clause m cl)) true cls in
  if res then (debug_global Pp.(fun () -> str" Clause holds"); res)
  else (debug_global Pp.(fun () -> str" Clause does not hold"); res)

let check_leq m u v = check_constraint m u Le v
let check_eq m u v =
  match Universe.repr u, Universe.repr v with
  | [ur], [vr] -> check_eq_level_expr ur vr m
   (* || check_constraint m u Eq v *)
  | _, _ -> check_constraint m u Eq v

let enforce_constraint (u, k, v) (m : t) = enforce u k v m

exception AlreadyDeclared

let add_model u { locality; entries; table; values; canonical; canentries } =
  if Index.mem u table then
   (debug_global Pp.(fun () -> str"Already declared level: " ++ debug_pr_level u);
    raise AlreadyDeclared)
  else
    let idx, table = Index.fresh u table in
    let can = Canonical { canon = idx; value = 0; local = locality;
      clauses_fwd = ForwardClauses.empty; clauses_bwd = ClausesOf.empty } in
    let entries = PMap.add idx can entries in
    idx, { locality; entries; table; values; canonical = canonical + 1; canentries = PSet.add idx canentries }

let add ?(rank:int option) u model =
  let _r = rank in
  debug_global Pp.(fun () -> str"Declaring level " ++ debug_pr_level u ++ pr_local model.locality);
  let _idx, model = add_model u model in
  model

let check_declared model us =
  let check l = not (Index.mem l model.table) in
  let undeclared = Level.Set.filter check us in
  if Level.Set.is_empty undeclared then Ok ()
  else Error undeclared

type extended_constraint_type =
  | ULe | ULt | UEq

type explanation = Universe.t * (extended_constraint_type * Universe.t) list

let to_expr model (can, k) = (Index.repr can.canon model.table, k)

let to_exprs model (hd, p) =
  (Universe.of_expr (to_expr model hd), List.map (fun (d, e) -> (d, Universe.of_expr (to_expr model e))) p)

let normalize_path p =
  let min = List.fold_left (fun k (_, k') -> min k k') 0 p in
  let hd, tl =
    if min < 0 then
      match p with
      | [] -> assert false
      | (x, k as hd) :: tl ->
        (hd, (ULt, (x, k - min)) :: List.map (fun (x, k) -> (ULe, (x, k - min))) tl)
    else
      match p with
      | [] -> assert false
      | hd :: tl -> (hd, List.map (fun x -> (ULe, x)) tl)
  in
  let rec strictify (x, k) l =
    match l with
    | [] -> []
    | (ULe, (x', k' as e)) as hd :: tl ->
      if x == x' && k < k' then (ULt, (x', k')) :: strictify e tl
      else hd :: strictify e tl
    | (_, e) as hd :: tl -> hd :: strictify e tl
  in (hd, strictify hd tl)

let repr_node_expr_eq m (u, k) =
  let (can, k' as e) = repr_node_expr m (u, k) in
  let canl = Index.repr can.canon m.table in
  if not (Level.equal canl u) then
    (debug_find_to_merge Pp.(fun () -> str "repr_node_expr " ++  LevelExpr.pr debug_pr_level (u,k) ++ str " = "
      ++ LevelExpr.pr debug_pr_level (canl, k'));
    Some (u, k), e)
  else None, e

let can_clause_of_clause_eqs m (prems, concl) =
  let prems = (List.map (fun prem -> repr_node_expr_eq m prem) prems) in
  let premeqs =
    if List.exists (fun (premeq, _) -> Option.has_some premeq) prems then
      let gete (premeq, (can, k)) =
        match premeq with
        | Some e -> e
        | None -> (Index.repr can.canon m.table, k)
      in
      Some (List.map gete prems)
    else None
  in
  let prems = List.map snd prems in
  let concleq, concl = repr_node_expr_eq m concl in
  (premeqs, concleq), (NeList.of_list prems, concl)

let get_explanation ((l, k, r) : univ_constraint) model : explanation =
  let get_explanation cl =
    let (eqprems, eqconcl), (prems, concl) = can_clause_of_clause_eqs model cl in
    debug_find_to_merge Pp.(fun () -> str "get_explanation for " ++ pr_can_clause model (prems, concl));
    let expl = get_explanation model prems concl in
    match expl with
    | [] -> None
    | p :: _ps ->
      match (to_exprs model (normalize_path (List.rev p))) with
      | (preme, []) -> (* Self loop *)
        let concleqs = match eqconcl with
          | Some e -> [ULe, Universe.of_expr (to_expr model concl); UEq, Universe.of_expr e]
          | None -> [ULe, Universe.of_expr (to_expr model concl)]
        in
        let prem, premeqs = match eqprems with
          | Some e -> (Universe.of_list e, [ULe, preme])
          | None -> (preme, [])
        in
        Some (prem, premeqs @ concleqs)
      | (r, rs) ->
        let eqconcl = match eqconcl with
          | Some e -> [(UEq, Universe.of_expr e)]
          | None -> []
        in
        let rs = rs @ eqconcl in
        let expl =
          match eqprems with
          | Some l -> (Universe.of_list l, (UEq, r) :: rs)
          | None -> (r, rs)
        in
        Some expl
  in
  let get_explanation_le u v =
    let res = List.fold_left (fun acc l ->
      match acc with
      | None -> get_explanation (Universe.repr v, l)
      | Some _ -> acc) None (Universe.repr u)
    in
    match res with
    | Some expl -> expl
    | None -> (u, [])
  in
  match k with
  | Le -> get_explanation_le l r
  | Eq -> if check_leq model l r then get_explanation_le r l else get_explanation_le l r

(* Precondition: all mentionned universes are canonical *)
let merge_clauses premsfwd can cank premsbwd concl conclk =
  (* New constraint: premsbwd[can + k := premsfwd + k'] -> concl + conclk']  *)
  let bk = NeList._find (fun c -> Index.equal c can) premsbwd in
  let premsfwd, premsbwd, conclk =
    (* Align the clauses on the same universe by the admissible shift transform *)
    if bk <= cank then
      (* Shift the backwards clause *)
      let diff = cank - bk in
      premsfwd, Premises.shift diff premsbwd, conclk + diff
    else
      Premises.shift (bk - cank) premsfwd, premsbwd, conclk
  in
  let prems' = NeList.map_splice (fun (c, _) ->
    if Index.equal c can then Some premsfwd else None) premsbwd in
  (prems', (concl, conclk))

let repr_clause model (prems, concl) =
  (NeList.map (repr_expr_can model) prems, repr_expr_can model concl)

let remove_fwd_clauses_to model prems target =
  Premises._fold (fun prem model ->
    let can, _k = repr_expr_can model prem in
    let fwd' = ForwardClauses.filter (fun _k concl _ ->
      let conclcan, _ = repr model concl in
      not (Index.equal conclcan.canon target)) can.clauses_fwd in
    change_node model { can with clauses_fwd = fwd' })
    prems model

(* This filters out forward clauses of prems mentioning target, which are
  duplicates of an existing constraint. *)
let remove_fwd_clauses_from model prems target =
  match prems with
  | None -> model
  | Some prems ->
    Premises._fold (fun prem model ->
      let can, _k = repr_expr_can model prem in
      let fwd' = ForwardClauses.filter_map (fun _k _concl clauses ->
        let clauses = PartialClausesOf.filter_map
          (fun ((_, prems) as cl) ->
            match prems with
            | None -> Some cl
            | Some prems ->
              if Premises._exists (fun (idx, _) ->
                let can, _ = repr model idx in
                  Index.equal can.canon target) prems then None
                else Some cl) clauses
          in
          if PartialClausesOf.is_empty clauses then None else Some clauses)
          can.clauses_fwd in
      change_node model { can with clauses_fwd = fwd' })
      prems model

let remove_all_bwd_clauses_from model concl prem =
  let can, _k = repr model concl in
  let bwd' = ClausesOf.filter_map (fun (_, _local, prems as cli) ->
    if Premises._exists (fun (prem', _) -> let canprem, _ = repr model prem' in Index.equal canprem.canon prem) prems then
      None
    else Some cli) can.clauses_bwd
  in
  change_node model { can with clauses_bwd = bwd' }

let remove_bwd_clauses_from model prem target =
  let can, _k = repr model prem in
  let bwd' = ClausesOf.filter_map (fun (kconcl, _local, prems as cli) ->
    if Int.equal kconcl 0 && Premises._exists (fun (prem, _) -> let canprem, _ = repr model prem in Index.equal canprem.canon target) prems then
      None
    else Some cli) can.clauses_bwd
  in
  change_node model { can with clauses_bwd = bwd' }

let clauses_of_univ_constraint u v cls =
  NeList.fold (fun e cls -> (u, e) :: cls) v cls
let unrepr_univ model u = Universe.unrepr (List.map (to_expr model) u)
let repr_univ model u = List.map (repr_node_expr model) (Universe.repr u)

(** Simplify u <= max (Set, v) clauses to u <= v and filter away u <= ... u + n , ... clauses, always valid *)
let filter_trivial_clause m (prems, (concl, k as conclk)) =
  (* Trivial ... u + k + n ... -> u + k clause *)
  if NeList.exists (fun (prem, k') -> Index.equal prem concl && k' >= k) prems then None
  else
    let canset = Index.find Level.set m.table in
    let filter (prem, _k') = not (Index.equal prem concl (* k' < k *)) in
    match Premises.filter filter prems with
    | None -> (* We removed the only trivial premise (concl, k') -> concl, k *) None
    | Some prems ->
      (* Filter out `Set` from max(Set, u) -> v constraints *)
      let prems =
        match NeList.filter (fun (prem, k) -> not (Index.equal prem canset && Int.equal k 0)) prems with
        | Some prems -> prems (* There were at least two premises in the rule *)
        | None -> prems
      in
      Some (prems, conclk)

let can_clause_of_idx_clause m (prems, concl) =
  let prems = NeList.map (repr_expr_can m) prems in
  let concl = repr_expr_can m concl in
  (prems, concl)

let enforce_clause cl model =
  let (prems, concl) = can_clause_of_idx_clause model cl in
  enforce_leq_can concl prems model

let pr_clause model cl =
  pr_clause (pr_index_point model) cl

exception InconsistentEquality

(** [set idx u model] substitutes universe [u] for all occurrences of [idx] in model, resulting
  in a set of constraints that no longer mentions [idx]. This is a stronger than [enforce_eq idx u],
  as the [idx] universe is dropped from the constraints altogether.

  @raises InconsistentEquality if one of the constraints involving [idx] cannot be satisfied when substituting [idx] with [u]. *)

let set_can (can,k) u model =
  let u =
    if Int.equal k 0 then u
    else
      if NeList.for_all (fun (_, k') -> k' >= k) u then
        NeList.map (fun (x, k') -> (x, k' - k)) u
      else raise InconsistentEquality
  in
  let fwd = can.clauses_fwd in
  let bwd = can.clauses_bwd in
  let uprems = NeList.map (fun (can, k) -> can.canon, k) u in
  _debug_set Pp.(fun () ->
    str"Looking at forward clauses " ++ pr_fwd_clause model can.canon fwd);
  let model, newclauses =
     ForwardClauses.fold (fun ~kprem ~concl ~prems (model, newclauses) ->
      let concl, k = repr_expr model (concl, 0) in
      let fwd = PartialClausesOf.shift k prems in
      PartialClausesOf.fold (fun (conclk, premsfwd) (model, newclauses) ->
        (* premsfwd, can + kprem -> concl + conclk *)
        (* Remove duplicate records of this constraint in premsfwd *)
        let premsrepr = Option.map (PremisesRepr.repr model) premsfwd in
        let model = remove_fwd_clauses_from model premsfwd can.canon in
        let model = remove_all_bwd_clauses_from model concl can.canon in
        let conclk = (concl, k + conclk) in
        (* Ensure the clause is not already trivial (self-loops) *)
        let precl = (Premises.add_opt (can.canon, kprem) premsrepr, conclk) in
        match filter_trivial_clause model precl with
        | None -> model, newclauses
        | Some (prems', conclk) ->
          _debug_set Pp.(fun () ->
              str"filter_trivial_clause " ++ pr_clause model precl ++ str " = " ++ pr_clause model (prems', conclk));
          let cl = (Premises.subst can.canon uprems prems', conclk) in
          _debug_set Pp.(fun () ->
            str"After substitution of " ++ pr_raw_index_point model can.canon ++ str" with " ++ pr_can_prems model u ++str " : " ++ pr_clause model cl);
          model, cl :: newclauses)
        fwd (model, newclauses))
      fwd (model, [])
  in
  _debug_set Pp.(fun () ->
    str"New clauses from forward: " ++ prlist_with_sep spc (pr_clause model) newclauses ++ fnl () ++
    str"Looking at backward clauses " ++ pr_clauses_of model can.canon bwd);
  let model, newclauses =
    ClausesOf.fold (fun (cank, _local, premsbwd) (model, newclauses) ->
      (* premsbwd -> can + cank *)
      let premsbwd = PremisesRepr.repr model premsbwd in
      let model = remove_fwd_clauses_to model premsbwd can.canon in
      match filter_trivial_clause model (premsbwd, (can.canon, cank)) with
      | None -> model, newclauses
      | Some (prems', _conclk) ->
        let u' = Premises.shift cank uprems in
        let cls = clauses_of_univ_constraint prems' u' [] in
        model, cls @ newclauses)
    bwd (model, newclauses)
  in
  let model = remove_node model can in
  _debug_set Pp.(fun () ->
    str"After removals, model is " ++ pr_clauses_all ~local:true model ++
    str"Adding constraints" ++ prlist_with_sep spc (pr_clause model) newclauses);
  let enforce_clause (model, equivs) cl =
    match enforce_clause cl model with
    | Some (model, equivs') -> (model, equivs' @ equivs)
    | None -> raise InconsistentEquality
  in List.fold_left enforce_clause (model, []) newclauses

exception OccurCheck

let set lvl u model =
  _debug_set Pp.(fun () -> str"Setting " ++ debug_pr_level lvl ++ str" := " ++ Universe.pr debug_pr_level u);
  let cank = repr_node model lvl in
  let u = NeList.of_list (repr_univ model u) in
  _debug_set Pp.(fun () -> str"Canonical representatives: " ++ pr_can_expr model cank ++ str" = " ++ pr_can_prems model u);
  if NeList.exists (fun (can', _k') -> fst cank == can') u then raise OccurCheck
  else
    let setidx = Index.find Level.set model.table in
    if Index.equal (fst cank).canon setidx then raise InconsistentEquality
    else
      let model, equivs = set_can cank u model in
      let equivs = unrepr_equivalences model equivs in
      model, equivs

type level_equivalences = (Level.t * (Level.t * int)) list

type 'a simplification_result =
  | HasSubst of 'a * level_equivalences * Universe.t
  | NoBound
  | CannotSimplify

(** [minimize idx model] returns a new model where the universe level idx has been removed and
  the new constraints are enough to derive the previous ones on all other universes.
  It returns a lower bound on idx in the original constraints, or None if it cannot be expressed.
  E.g. minimizing k when the only constraint is l + 1 <= k + 2 would result in k = l - 1 which is not a valid universe.  *)
let minimize_can can k model =
  let fwd = can.clauses_fwd in
  let bwd = can.clauses_bwd in
  _debug_minim Pp.(fun () -> str"Minimizing " ++ pr_can model can ++ str" in graph: " ++ pr_clauses_all model);
  let model, glb =
    ForwardClauses.fold (fun ~kprem ~concl ~prems (model, glb) ->
      let concl, k = repr model concl in
      let fwd = PartialClausesOf.shift k prems in
      let (model, glb) =
        PartialClausesOf.fold (fun (conclk, premsfwd) (model, glb) ->
          (* premsfwd, can + kprem -> concl + conclk *)
          (* Remove duplicate records of this constraint in premsfwd *)
          let model = remove_fwd_clauses_from model premsfwd can.canon in
          let model =
            ClausesOf.fold (fun (cank, _local, premsbwd) model ->
              (* premsbwd -> can + cank *)
              let premsfwd = (cons_opt_nelist (can.canon, kprem) premsfwd) in
              let cl = merge_clauses premsbwd can.canon cank premsfwd concl.canon conclk in
              let cl = repr_clause model cl in
              let model =
                match filter_trivial_can_clause model cl with
                | None -> model
                | Some cl ->
                  match add_can_clause_model model cl with
                  | Some (_, m) -> m
                  | None -> model
              in
              let model = remove_fwd_clauses_to model premsbwd can.canon in
              model) bwd model
          in
          let glb = (concl.canon, (conclk - kprem)) :: glb in
          (model, glb))
        fwd (model, glb)
      in
      let model = remove_all_bwd_clauses_from model concl.canon can.canon in
      (model, glb))
    fwd (model, [])
  in
  let sort (idx, k) (idx', k') =
    match Index.compare idx idx' with
    | 0 -> Int.compare k k'
    | n -> n
  in
  let glb = List.map (repr_expr_can model) (List.sort_uniq sort glb) in
  if CList.is_empty glb then NoBound
  else
    let glb = Universe.addn (unrepr_univ model glb) k in
    if Universe.for_all (fun (_, k) -> k >= 0) glb
    then
      (_debug_minim Pp.(fun () -> str"Removing: " ++ pr_can model can ++ str " in " ++ pr_clauses_all model);
      let model = remove_node model can in
      debug_check_invariants model;
      _debug_minim Pp.(fun () -> str"Removed " ++ pr_can model can ++ str ", new model: " ++ pr_clauses_all model);
      HasSubst (model, [], glb))
    else CannotSimplify


let minimize level model =
  match repr model (Index.find level model.table) with
  | exception Not_found -> CannotSimplify (* should rather raise the exception here *)
  | (can, k) -> minimize_can can k model

let maximize_can (can, k) model =
  let bwd = can.clauses_bwd in
  _debug_minim Pp.(fun () -> str"Maximizing " ++ pr_can model can ++ str" in graph: " ++ pr_clauses_all model);
  let card = ClausesOf.cardinal bwd in
  match card with
  | 0 -> NoBound
  | n when n <> 1 -> CannotSimplify
  | _ ->
    let cank, _local, premsbwd = ClausesOf.choose bwd in
    let ubound = NeList.map (repr_expr_can model) premsbwd in
    if NeList.for_all (fun (_, k) -> cank <= k) ubound then
      let ubound = NeList.map (fun (can, k) -> (can, k - cank)) ubound in
      let model, equivs = set_can (can, k) ubound model in
      try HasSubst (model, unrepr_equivalences model equivs, unrepr_univ model (NeList.to_list ubound))
      with InconsistentEquality -> CannotSimplify
    else CannotSimplify

let maximize level model =
  match repr model (Index.find level model.table) with
  | exception Not_found -> CannotSimplify
  | can -> maximize_can can model

let remove_set_clauses_can can model =
  let setidx = Index.find Level.set model.table in
  let fwd = can.clauses_fwd in
  match ForwardClauses.IntMap._find 0 fwd with
  | exception Not_found -> model
  | fwd_clauses ->
    match ForwardClauses.PMap._find setidx fwd_clauses with
    | exception Not_found -> model
    | prems ->
      let prems = PartialClausesOf.filter_map
      (fun (k', prem as x) ->
        if Int.equal k' 0 && Option.is_empty prem then None else Some x)
        prems
      in
      let fwd = replace_bwd prems 0 setidx fwd in
      let model = change_node model { can with clauses_fwd = fwd } in
      (* Filter out u -> Set + 0 constraints *)
      remove_bwd_clauses_from model setidx can.canon

let remove_set_clauses l model =
  match repr model (Index.find l model.table) with
  | exception Not_found -> model
  | (can, _k) -> remove_set_clauses_can can model

let pr_constraint_type k =
  let open Pp in
  match k with
  | Eq -> str " = "
  | Le -> str " ≤ "

let constraint_type_ord c1 c2 = match c1, c2 with
| Le, Le -> 0
| Le, Eq -> -1
| Eq, Eq -> 0
| Eq, Le -> 1

type univ_constraint = Universe.t * constraint_type * Universe.t

module UConstraintOrd =
struct
type t = univ_constraint
let compare (u,c,v) (u',c',v') =
  let i = constraint_type_ord c c' in
  if not (Int.equal i 0) then i
  else
    let i' = Universe.compare u u' in
    if not (Int.equal i' 0) then i'
    else Universe.compare v v'
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

let constraints_of_clauses ?(only_local = false) m clauses =
  PMap.fold (fun concl bwd cstrs ->
    ClausesOf.fold (fun (k, local, prems) cstrs ->
      if only_local && local == Global then cstrs
      else
      let prems = NeList.to_list prems in
      let prems =
        List.map (fun (v, k) ->
          let vcan, vk = repr m v in
          let vp = Index.repr vcan.canon m.table in
          (vp, vk + k)) prems
      in
      let prem = Universe.unrepr prems in
      Constraints.add (Universe.of_list [(Index.repr concl m.table, k)], Le, prem) cstrs)
      bwd cstrs)
    clauses Constraints.empty

let constraints_of model ?(only_local = false) fold acc =
  let module UF = Unionfind.Make (LevelExpr.Set) (LevelExpr.Map) in
  let equiv = UF.create () in
  let bwd = ref PMap.empty in
  let locals = ref Level.Set.empty in
  let constraints_of u v =
    match v with
    | Canonical can ->
      if only_local && can.local == Local then locals := Level.Set.add (Index.repr can.canon model.table) !locals;
      bwd := PMap.add can.canon can.clauses_bwd !bwd
    | Equiv (local, v, vk) ->
      if only_local && local == Global then () else
      let u = Index.repr u model.table in
      let v = Index.repr v model.table in
      UF.union (u, 0) (v, vk) equiv
  in
  let () = PMap.iter constraints_of model.entries in
  let cstrs = constraints_of_clauses model !bwd in
  !locals, Constraints.fold fold cstrs acc, UF.partition equiv

type 'a constraint_fold = univ_constraint -> 'a -> 'a

let interp_univ model l =
  Universe.of_list (NeList.to_list (NeList.map (fun (idx, k) -> (Index.repr idx model.table, k)) l))

let constraints_for ~(kept:Level.Set.t) model (fold : 'a constraint_fold) (accu : 'a) : 'a =
  let add_cst u knd v (cst : 'a) : 'a =
    fold (interp_univ model u, knd, interp_univ model v) cst
  in
  debug_constraints_for Pp.(fun () -> str"constraints_for kept: " ++ Level.Set.pr debug_pr_level kept ++ pr_clauses model);
  let keptp = Level.Set.fold (fun u accu -> PSet.add (Index.find u model.table) accu) kept PSet.empty in
  (* rmap: partial map from canonical points to kept points *)
  let rmap, csts = PSet.fold (fun u (rmap,csts) ->
    let arcu, ku = repr model u in
    if PSet.mem arcu.canon keptp then
      let csts =
        if Index.equal u arcu.canon then csts
        else
          add_cst (NeList.tip (u, 0)) Eq (NeList.tip (arcu.canon, ku)) csts
      in
      PMap.add arcu.canon arcu.canon rmap, csts
    else
      match PMap.find arcu.canon rmap with
      | v -> rmap, add_cst (NeList.tip (u, 0)) Eq (NeList.tip (v, 0)) csts
      | exception Not_found -> PMap.add arcu.canon u rmap, csts)
    keptp (PMap.empty, accu)
  in
  let removed =
    PMap.fold
      (fun idx entry removed ->
        match entry with
        | Equiv (_local, _, _k) ->
          (* We don't need to care about removed non-canonical universes *)
          removed
        | Canonical can ->
            if PSet.mem idx keptp then removed
            else
              if PMap.mem can.canon rmap then
                (* This canonical node is represented by a kept universe, don't remove *)
                removed
              else (* Removal of a canonical node, we need to modify the clauses *)
                PSet.add can.canon removed)
    model.entries PSet.empty
  in
  debug_constraints_for Pp.(fun () -> str"constraints_for removed: " ++ _pr_w model removed);
  let remove_can idx model =
    let can, k = repr model idx in
    assert (Int.equal k 0 && Index.equal can.canon idx);
    let fwd = can.clauses_fwd in
    let bwd = can.clauses_bwd in
    ForwardClauses.fold (fun ~kprem ~concl ~prems model ->
      let concl, k = repr model concl in
      let fwd = PartialClausesOf.shift k prems in
      PartialClausesOf.fold (fun (conclk, premsfwd) model ->
        (* premsfwd, can + kprem -> concl + conclk *)
        ClausesOf.fold (fun (cank, _local, premsbwd) model ->
          (* premsbwd -> can + cank *)
          let premsfwd = (cons_opt_nelist (can.canon, kprem) premsfwd) in
          let cl = merge_clauses premsbwd can.canon cank premsfwd concl.canon conclk in
          let cl = (repr_clause model cl) in
          debug_constraints_for Pp.(fun () -> str"constraints_for adding: " ++ pr_can_clause model cl);
          match add_can_clause_model model cl with
          | Some (_, m) -> m
          | None -> model)
        bwd model)
      fwd model)
    fwd model
  in
  (* At this point the clauses that don't mention removed universes are enough to
     derive the clauses between kept universes *)
  let model = PSet.fold remove_can removed model in
  let canon_repr can =
    match PMap.find can.canon rmap with
    | v -> v
    | exception Not_found -> assert false
  in
  let can_prem_to_prem l = NeList.map (fun (x, k) -> (canon_repr x, k)) l in
  let add_from uprev u csts prems k =
    let cprems = canonical_premises model prems in
    if not (NeList.exists (fun (v, _) -> PSet.mem v.canon removed) cprems) then
      (let cl = (prems, (u.canon,k)) in
      debug_constraints_for Pp.(fun () -> str"constraints_for adding (from " ++ pr_raw_index_point model uprev ++ str"): " ++ pr_clause model cl);
       add_cst (NeList.tip (canon_repr u, k)) Le (can_prem_to_prem cprems) csts)
    else csts
  in
  let fold u acc =
    let arc, uk = repr model u in
    if not (Index.equal arc.canon u) then acc else
    let cls = arc.clauses_bwd in
    ClausesOf.fold (fun (k, _local, prems) csts -> add_from u arc csts prems (k + uk)) cls acc
  in
  PSet.fold fold keptp csts

let domain model = Index.dom model.table

let choose p model p' =
  let canp' = repr_node model p' in
  let pointp' = Index.repr (fst canp').canon model.table in
  if p pointp' then Some pointp'
  else PMap.fold (fun idx e acc ->
      match acc with
      | Some _ -> acc
      | None ->
        match e with
        | Equiv (_local, idx', k) ->
          let canp'' = repr_expr_can model (idx', k) in
          if fst canp' == fst canp'' && Int.equal (snd canp') (snd canp'') then
            let pointp' = Index.repr idx model.table in
            if p pointp' then Some pointp'
            else acc
          else acc
        | Canonical _ -> acc)
      model.entries None


type node =
| Alias of LevelExpr.t
| Node of (int * Universe.t) list (** Nodes [(k_i, u_i); ...] s.t. u + k_i <= u_i *)

type repr = node Level.Map.t

let univ_of_expr model (l, k) =
  Universe.of_expr (Index.repr l model.table, k)

let universe_of_premise model prem =
  match prem with
  | NeList.Tip (l, k) -> univ_of_expr model (l, k)
  | NeList.Cons (e, xs) ->
    NeList.fold (fun (l, k) acc -> Universe.sup (univ_of_expr model (l, k)) acc) xs (univ_of_expr model e)

let repr model =
  PMap.fold (fun idx e acc ->
    let conclp = Index.repr idx model.table in
    let node = match e with
    | Equiv (_local, idx, k) -> Alias (Index.repr idx model.table, k)
    | Canonical can ->
      let prems = can.clauses_bwd in
      let cls =
        ClausesOf.fold (fun cli l ->
          let (k, _local, prem) = cli in
          let u = universe_of_premise model prem in
          (k, u) :: l) prems []
      in Node cls
    in
    Level.Map.add conclp node acc)
  model.entries Level.Map.empty

let pmap_to_point_map table pmap =
  PMap.fold (fun idx v acc ->
    let p = Index.repr idx table in
    Level.Map.add p v acc)
    pmap Level.Map.empty

let valuation_of_model (m : model) =
  let max = Option.default 0 (model_max m) in
  let valm = PMap.map (fun e -> max - Option.get (entry_value m e)) m.entries in
    pmap_to_point_map m.table valm

let valuation model = valuation_of_model model
