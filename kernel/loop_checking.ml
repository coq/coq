open Univ

let debug_loop_checking_invariants_flag, debug_loop_checking_invariants = CDebug.create_full ~name:"loop-checking-invariants" ()
let _debug_loop_checking_flag, debug_loop_checking = CDebug.create_full ~name:"loop-checking" ()

module Index :
sig
  type t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  module Set : Set.S with type elt = t
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

  let concat_map (f : 'a -> 'b t) (l : 'a t) : 'b t =
    let rec aux l =
      match l with
      | Tip x -> f x
      | Cons (x, xs) -> append (f x) (aux xs)
    in aux l

  let concat_map_with append (f : 'a -> 'b) (l : 'a t) : 'b =
    let rec aux l =
      match l with
      | Tip x -> f x
      | Cons (x, xs) -> append (f x) (aux xs)
    in aux l

  module Smart =
  struct
    let concat_map (f : 'a -> 'a t) (l : 'a t) : 'a t =
      let rec aux l =
        match l with
        | Tip x ->
          (match f x with
          | Tip x' as t' -> if x' == x then l else t'
          | e -> e)
        | Cons (x, xs) ->
          let xs' = aux xs in
          match f x with
          | Tip x' ->
            if x' == x then
              if xs' == xs then l
              else Cons (x, xs')
            else Cons (x', xs')
          | e -> append e xs'
      in aux l
  end

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

  let add_opt x l =
    match l with
    | None -> Tip x
    | Some l -> Cons (x, l)
end

module SetWithCardinal (O:OrderedType.S) (S : Set.S with type elt = O.t) =
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

  let map f s =
    let s' = S.map f s.set in
    if s' == s.set then s
    else { set = s'; cardinal = S.cardinal s' } (* Cardinal might change if f maps two elements to the same *)

  let _for_all p s = S.for_all p s.set
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

  let filter_map f s =
    let s' = S.filter_map f s.set in
    if s' == s.set then s
    else { set = s'; cardinal = S.cardinal s' }

  let filter f s =
    let s' = S.filter f s.set in
    if s' == s.set then s
    else { set = s'; cardinal = S.cardinal s' }
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

  let _remove x m =
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

  let _map f m =
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
  let exists = NeList.exists
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

  let _sort : t -> t = NeList.sort Premise.incl

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

type clause = Premises.t * (Index.t * int)

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
           | k' -> k <= k'
        in
        NeList.for_all find prems
      else false

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

  let shift n cls = if Int.equal n 0 then cls else map (fun (k, local, prems) -> (k + n, local, prems)) cls

  let add cl cls =
    if exists (fun cl' -> ClauseInfo.subsumes cl' cl) cls then cls
    else SWC.add cl cls

  let choose cls = SWC.choose cls

  let to_clauses concl cls : (locality * clause) list =
    let to_clauses (conclk, local, prems) cls =
      let to_clauses (concl, k) cls = (local, (prems, (concl, conclk + k))) :: cls in
      NeList.fold to_clauses concl cls
    in
    fold to_clauses cls []

end

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

  module IntMap = MapWithCardinal (Int) (PMap)
  (** [t] This type represents forward clauses [(_ + k, other -> concl + n)].
    The premises are necessarily non-empty, and the [(_ + k)] one is singled out.
    They are indexed by [k], then by the conlusion universe [concl] and finally
    by [n], in PartialClausesOf.t, which contains the potentially empty [other] premises.
    The cardinal is maintained for fast computations. *)
  type t = IntMap.t

  let add (cl : fwd_clause) (clauses : t) : t =
    if PartialClausesOf.is_empty cl.prems then clauses else
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

  let _filter (f : int -> Index.t -> PartialClausesOf.t -> bool) clauses =
    IntMap.fold (fun k fwd acc ->
      let fwd = PMap.filter (f k) fwd in
      IntMap.add k fwd acc)
      clauses IntMap.empty

  let _filter_map (f : int -> Index.t -> PartialClausesOf.t -> PartialClausesOf.t option) clauses =
    IntMap.fold (fun k fwd acc ->
      let fwd = PMap.filter_map (f k) fwd in
      if PMap.is_empty fwd then acc else IntMap.add k fwd acc)
      clauses IntMap.empty

  let cardinal (cls : t) : int = IntMap.cardinal cls
  let empty = IntMap.empty
  let is_empty x = IntMap.is_empty x
  let singleton cl = add cl empty

  let fold (f : kprem:int -> concl:Index.t -> prems:PartialClausesOf.t -> 'a -> 'a) (cls : t) : 'a -> 'a =
    IntMap.fold (fun kprem cls acc ->
      PMap.fold (fun concl prems acc ->
        f ~kprem ~concl ~prems acc) cls acc)
      cls

  let map f clauses =
    let f ~kprem ~concl ~prems cls =
      let f (kconcl, prems) cls =
        let kprem, concl, kconcl, prems = f ~kprem ~concl ~kconcl ~prems in
        add { kprem; concl; prems = PartialClausesOf.singleton (kconcl, prems) } cls
      in
      PartialClausesOf.fold f prems cls
    in
    fold f clauses empty

  let pr_clauses pr prem (cls : PMap.t) =
    let open Pp in
    PMap.fold (fun concl cls acc -> PartialClausesOf.pr pr prem concl cls ++ spc () ++ acc) cls (mt())

  let pr pr_prem prem (cls : t) =
    let open Pp in
    IntMap.fold
      (fun kprem cls acc -> pr_clauses pr_prem (prem, kprem) cls ++ acc)
      cls (mt ())

  let to_clauses u cls : clause list =
    let to_clause ~kprem ~concl ~prems cls =
      let to_clause (kconcl, prems) cls =
        match prems with
        | None -> (Premises.shift kprem u, (concl, kconcl)) :: cls
        | Some p -> (NeList.append (Premises.shift kprem u) p, (concl, kconcl)) :: cls
      in
      PartialClausesOf.fold to_clause prems cls
    in
    fold to_clause cls []

end

module PSet = SetWithCardinal(Index)(Index.Set)

(* Beware, do not use pointer equality, rather use the [canon] Index.t equality,
  as canonical nodes get updated clauses and values throughout the algorithms. *)
type canonical_node =
  { canon: Index.t;
    local: locality;
    rigid : bool; (* Prefer to maintain this canonical node when equating it with another *)
    value : int;
    clauses_bwd : ClausesOf.t; (* premises -> canon + k *)
    clauses_fwd : ForwardClauses.t (* canon + k, ... ->  concl + k' *) }

type model = {
  locality : locality;
  entries : canonical_node PMap.t; (* The canonical nodes *)
  subst : (Premises.t * locality * locality) PMap.t; (* The substitution from levels to universes:
    localities of the substituted universe and the constraints are recorded *)
  values : int PMap.t option; (* values, superseding the ones attached to canonical nodes if present *)
  canonical : int; (* Number of canonical nodes *)
  table : Index.table }

let set_local m = { m with locality = Local }

let empty_model = {
  locality = Global;
  entries = PMap.empty;
  subst = PMap.empty;
  values = None;
  canonical = 0;
  table = Index.empty
}

let empty = empty_model

let enter_equiv m u local v =
  { locality = m.locality;
    entries = PMap.remove u m.entries;
    subst = PMap.add u (v, local, m.locality) m.subst;
    canonical = m.canonical - 1;
    values = Option.map (PMap.remove u) m.values;
    table = m.table }

let change_node m n =
  { m with entries = PMap.set n.canon n m.entries }

exception Undeclared of Level.t

(* let _ = CErrors.register_handler *)
  (* (function Undeclared l -> Some Pp.(str"Undeclared universe level: " ++ Level.raw_pr l) | _ -> None) *)

(* canonical representative : we follow the Equiv links *)
let repr m u = PMap.find u m.entries

let repr_expr m (u, k) = (repr m u, k)

let repr_premises m p =
  NeList.map (repr_expr m) p

let rec canonical_repr m (u, k) =
  match PMap.find u m.entries with
  | can -> NeList.Tip (can, k)
  | exception Not_found ->
    match PMap.find u m.subst with
    | (p, _local, _local_eq) -> canonical_premises_repr m (Premises.shift k p)
    | exception Not_found -> raise (Undeclared (Index.repr u m.table))
and canonical_premises_repr m p =
  NeList.concat_map (canonical_repr m) p

let expr_of_can_premise m (can, k) = (Index.repr can.canon m.table, k)
let expr_of_premise m (idx, k) = (Index.repr idx m.table, k)

let univ_of_can_expr_list model u = Universe.unrepr (List.map (expr_of_can_premise model) u)

let univ_of_can_premises model u = Universe.unrepr (NeList.to_list (NeList.map (expr_of_can_premise model) u))

let univ_of_premises model u = Universe.unrepr (NeList.to_list (NeList.map (expr_of_premise model) u))

let rec canonical_premise m (u, k) : Premises.t =
  match PMap.find u m.entries with
  | can -> NeList.Tip (can.canon, k)
  | exception Not_found ->
    match PMap.find u m.subst with
    | (p, _local, _localeq) -> canonical_premises m (Premises.shift k p)
    | exception Not_found -> raise (Undeclared (Index.repr u m.table))
and canonical_premises m p =
  NeList.Smart.concat_map (canonical_premise m) p

let normalize m l =
  match Index.find l m.table with
  | exception Not_found -> None
  | idx ->
    match PMap.find idx m.entries with
    | _can -> None (* Already in canonical form *)
    | exception Not_found ->
      match PMap.find idx m.subst with
      | (p, _local, _localeq) ->
        let prems =  canonical_premises m p in
        Some (univ_of_premises m prems)
      | exception Not_found -> None

let normalize_subst model =
  let subst =
    PMap.map (fun (u, locality, locality_eq) -> canonical_premises model u, locality, locality_eq) model.subst
  in { model with subst }

let refresh_can_expr m (u, k) = repr_expr m (u.canon, k)

let pr_expr = LevelExpr.pr Level.raw_pr

let pr_raw_index_point m idx =
  try pr_expr (Index.repr idx m.table, 0)
  with Not_found -> Pp.str"<point not in table>"

let pr_raw_index_point_expr m (idx, n) =
  try pr_expr (Index.repr idx m.table, n)
  with Not_found -> Pp.str"<point not in table>"

let pr_raw_premises m p =
  try match p with
    | NeList.Tip e -> pr_raw_index_point_expr m e
    | NeList.Cons _ -> Pp.(str"max(" ++ prlist_with_sep (fun () -> str ", ") (pr_raw_index_point_expr m) (NeList.to_list p) ++ str")")
  with Not_found -> Pp.str"<point not in table>"

let pr_index_point m (idx, n) =
  let (idx, k) = try let can = repr m idx in (can.canon, n) with Not_found -> (idx, n) in
  try pr_expr (Index.repr idx m.table, k)
  with Not_found -> Pp.str"<point not in table>"

let _pr_clause_info m concl cl = ClausesOf.ClauseInfo.pr (pr_index_point m) concl cl

let pr_clauses_of m = ClausesOf.pr (pr_index_point m)

let eq_expr (idxu, ku as u) (idxv, kv as v) =
  u == v || (Index.equal idxu idxv && Int.equal ku kv)

let eq_can_expr (canu, ku as u) (canv, kv as v) =
  u == v || (canu == canv && Int.equal ku kv)

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

type clause_info = Index.t * ClausesOf.t

let _pr_clause_info m ((concl, kprem) : clause_info) =
  pr_clauses_of m concl kprem

type t = model

let eq_pointint x x' =
  let (idx, k) = x and (idx', k') = x' in
  Index.equal idx idx' && Int.equal k k'

let canonical_can_premises p =
  NeList.map (fun (can, k) -> (can.canon, k)) p

let _canonical_clause (prems, (concl, k)) =
  (canonical_can_premises prems, (concl.canon, k))

let _pr_clause_idx m cl = pr_clause (pr_index_point m) cl

let check_invariants ~(required_canonical:Level.t -> bool) model =
  let required_canonical u = required_canonical (Index.repr u model.table) in
  let n_canon = ref 0 in
  PMap.iter (fun idx can ->
    assert (Index.equal idx can.canon);
    assert (Index.mem (Index.repr idx model.table) model.table);
    (* assert (PMap.mem idx model.values); *)
    let cls = can.clauses_bwd in
    ClausesOf.iter
      (fun (k, _local, prems) ->
        (* prems -> can + k *)
        if not (k >= 0) then CErrors.user_err Pp.(str "A conclusion has negative weight") else ();
        let check_prem (l, lk) =
          if not (lk >= 0) then CErrors.user_err Pp.(str "A premise has negative weight") else ();
          assert (PMap.mem l model.entries);
          let lcan = repr model l in
          (* Ensure this backward clause of shape [max(... l + lk ... ) -> can + k] is registered as a forward clause for the premise l *)
          match ForwardClauses.IntMap.find_opt lk lcan.clauses_fwd with
          | Some fwd ->
            ForwardClauses.PMap.exists (fun idx kprem ->
            (* kprem = { (kconcl, max ( ... l' + lk' ... )) } -> idx *)
            let can' = repr model idx in
            can' == can &&
            PartialClausesOf.exists (fun (k', prems') ->
              let prems' = cons_opt_nelist (lcan.canon, lk) prems' in
              Int.equal k k' && NeList.equal eq_pointint prems prems') kprem)
              fwd
          | None -> false
        in
        Premises.iter
          (fun kprem -> if (check_prem kprem) then () else
          CErrors.user_err Pp.(str"Clause " ++
            pr_fwd_clause model (fst kprem)
            (ForwardClauses.singleton { concl = can.canon; kprem = (snd kprem);
              prems = PartialClausesOf.singleton (k, NeList.filter (fun x -> not (eq_expr kprem x)) prems) }) ++ str" is not registered as a forward clauses for "
            ++ pr_index_point model kprem ++ fnl () ++ str" prems = " ++ _pr_clause_idx model (prems, (can.canon, k)))) prems) cls;
      incr n_canon) model.entries;
  PMap.iter (fun idx (u, _local, _local_eq) ->
    Premises.iter (fun (idx', k) ->
      assert (k >= 0);
      assert (PMap.mem idx' model.entries || PMap.mem idx' model.subst); (* Lazy substitution *)
      assert (Index.mem (Index.repr idx' model.table) model.table)) u;
      (* The clauses should not mention aliases *)
    assert (not (required_canonical idx))) model.subst

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
    Some (PMap.fold (fun _ can acc -> max can.value acc) m.entries 0)
  | Some values ->
    PMap.fold (fun _ v acc -> max_opt (Some v) acc) values None

let model_min (m : model) : int option =
  match m.values with
  | None ->
    Some (PMap.fold (fun _ can acc -> min can.value acc) m.entries 0)
  | Some values ->
    PMap.fold (fun _ v acc -> min_opt (Some v) acc) values None

let clauses_cardinal (m : model) : int =
  PMap.fold (fun _ can acc -> acc + ClausesOf.cardinal can.clauses_bwd)
    m.entries 0

let without_bound (m : model) : int =
  PMap.fold (fun _ can acc ->
      let cls = can.clauses_bwd in
      if ClausesOf.is_empty cls then succ acc else acc)
    m.entries 0

let _pr_updates m s =
  let open Pp in
  prlist_with_sep spc (fun idx -> Level.raw_pr (Index.repr idx m.table)) (PSet.elements s)

let length_path_from m idx =
  let rec aux = function
    | None -> 0
    | Some (u, _local, _local_eq) ->
      succ (Premises._fold (fun (idx, _) acc ->
        max (aux (PMap.find_opt idx m.subst)) acc) u 0)
  in aux (PMap.find_opt idx m.subst)

let rec maximal_path m =
  PMap.fold (fun _ (u, _local, _local_eq) acc ->
    max (succ (maximal_premises_path m u)) acc) m.subst 0
and maximal_premises_path m p =
  Premises._fold (fun (idx, _) acc ->
    max (length_path_from m idx) acc) p 0

let _statistics model =
  let open Pp in
  str" " ++ int (PMap.cardinal model.entries) ++ str" canonical universes" ++
  str", " ++ int (PMap.cardinal model.subst) ++ str" defined universes" ++
  str ", maximal value in the model is " ++ pr_opt int (model_max model) ++
  str ", minimal value is " ++ pr_opt int (model_min model) ++
  str", " ++ int (clauses_cardinal model) ++ str" clauses." ++ spc () ++
  int (without_bound model) ++ str" canonical universes are not bounded above " ++
  str", " ++ int (maximal_path model) ++ str" maximal path length in equiv nodes"

let pr_can m can =
  Level.raw_pr (Index.repr can.canon m.table)

let pr_can_clauses m ?(local=false) can =
  if not local || (local && can.local == Local) then
    if ClausesOf.is_empty can.clauses_bwd && ForwardClauses.is_empty can.clauses_fwd then Pp.mt ()
    else
      Pp.(str"For " ++ pr_can m can ++ fnl () ++ pr_clauses_of m can.canon can.clauses_bwd ++ fnl () ++
          str"Forward" ++ spc () ++ pr_fwd_clause m can.canon can.clauses_fwd ++ fnl ())
  else Pp.mt ()

let pr_clauses_all ?(local=false) m =
  let open Pp in
  PMap.fold (fun _p can acc -> pr_can_clauses ~local m can ++ acc)
    m.entries (Pp.mt ()) ++
  PMap.fold (fun p (u, is_local, is_local_eq) acc ->
    if not local || (local && is_local_eq == Local) then
      pr_raw_index_point m p ++ str " = " ++ pr_raw_premises m u ++ pr_local is_local ++ spc () ++ acc
    else acc)
    m.subst (Pp.mt ())

let debug_check_invariants m =
  if CDebug.get_flag debug_loop_checking_invariants_flag then
    (try check_invariants ~required_canonical:(fun _ -> false) m
     with e ->
      debug_loop_checking_invariants Pp.(fun () -> str "Broken invariants on: " ++ pr_clauses_all m ++ CErrors.print e);
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
  let canon =
    try repr m l
    with Not_found -> raise (Undeclared (Index.repr l m.table))
  in (canonical_value m canon)

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

  let _pr m (w, _) =
    let open Pp in
    prlist_with_sep spc (fun (idx, _) -> Level.raw_pr (Index.repr idx m.table)) (PMap.bindings w)

  let _pr_clauses m (w, _) =
    let open Pp in
    prlist_with_sep spc (fun (idx, fwd) ->
      Level.raw_pr (Index.repr idx m.table) ++ str": " ++ spc () ++
      str" Forward clauses " ++ pr_fwd_clause m idx fwd)
      (PMap.bindings w)

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

let update_value premv concl m (clause : PartialClausesOf.ClauseInfo.t) : int option =
  let (conclk, premises) = clause in
  match min_premise m premv premises with
  | exception VacuouslyTrue -> None
  | k0 when k0 < 0 -> None
  | k0 ->
    let newk = conclk + k0 in
    let canv = canonical_value m concl in
    debug_loop_checking Pp.(fun () -> str "Min premise value + conclk: " ++ int newk ++ str", conclusion value:: " ++ pr_opt int canv);
    match canv with
    | Some v when newk <= v -> None
    | _ -> Some newk

let check_model_clauses_of_aux m prem premv concl cls =
  PartialClausesOf.fold (fun cls m ->
    let (conclk, prems) = cls in
    debug_loop_checking Pp.(fun () -> str "Checking clause: " ++ pr_clause (pr_index_point m) (NeList.add_opt prem prems, (concl.canon,conclk)));
    match update_value premv concl m cls with
    | None -> m
    | Some newk ->
      debug_loop_checking Pp.(fun () -> str "Updating value of " ++ pr_index_point m (concl.canon,0) ++ str " to " ++ int newk);
      set_canonical_value m concl newk)
    cls m

let find_bwd idx cls = ForwardClauses.PMap.find_opt idx cls

(** Check a set of forward clauses *)
let check_model_fwd_clause_aux ?early_stop prem (fwd : ForwardClauses.t) (acc : PSet.t * model) : PSet.t * model =
  let open ForwardClauses in
  let check () =
    IntMap.fold (fun premk fwd acc ->
      let premv = get_model_value (snd acc) prem premk in
      PMap.fold (fun concl fwd (* (prem + premk), premises -> concl + k *) (wcls, m as acc) ->
        let can = repr m concl in
        let m' = check_model_clauses_of_aux m (prem, premk) premv can fwd in
        if m == m' then (* not modifed *) acc
        else (PSet.add can.canon wcls, m')) fwd acc)
      fwd acc
  in
  match early_stop with
  | None -> check ()
  | Some (can, k) ->
      let (_, m) = acc in
      IntMap.iter (fun premk fwd ->
        match find_bwd can.canon fwd with
        | None -> ()
        | Some cls ->
          let premv = get_model_value (snd acc) prem premk in
          PartialClausesOf.iter (fun cls ->
            match update_value premv can m cls with
            | None -> ()
            | Some newk -> if k <= newk then raise FoundImplication)
            cls) fwd;
        check ()

let check_model_fwd_aux ?early_stop (cls, m) : PSet.t * model =
  CanSet.fold (fun can fwd m -> check_model_fwd_clause_aux ?early_stop can fwd m) cls (PSet.empty, m)

let check_clauses_with_premises ?early_stop (cls : CanSet.t) model : (PSet.t * model) option =
  let (updates, model') = check_model_fwd_aux ?early_stop (cls, model) in
  if model == model' then None
  else Some (updates, model')

type 'a result = Loop | Model of 'a * model

let canonical_cardinal m = m.canonical

let can_all_premises_in w prem =
  Premises.for_all (fun (l, _) -> PSet.mem l w) prem

let partition_clauses_of w cls =
  PartialClausesOf.partition (fun (_k, prems) ->
    Option.cata (can_all_premises_in w) true prems) cls

let add_bwd prems kprem concl clsof =
  if PartialClausesOf.is_empty prems then clsof
  else ForwardClauses.add { prems; kprem; concl } clsof

let add_canset idx (clauses : ForwardClauses.t) canset =
  if ForwardClauses.IntMap.is_empty clauses then canset
  else CanSet.add idx clauses canset

(* Partition the clauses according to the presence of w in the premises, and only w in the conclusions *)
let partition_clauses_fwd model (w : PSet.t) (cls : CanSet.t) : CanSet.t * CanSet.t * CanSet.t =
  CanSet.fold (fun prem fwd (allw, conclw, conclnw) ->
    let fwdw, fwdpremw, fwdnw =
      ForwardClauses.fold (fun ~kprem ~concl ~prems (fwdallw, fwdnallw, fwdnw) ->
        let concl = repr model concl in
        let concl = concl.canon in
        if PSet.mem concl w then
          let allw, nallw = partition_clauses_of w prems in
          (add_bwd allw kprem concl fwdallw,
           add_bwd nallw kprem concl fwdnallw,
           fwdnw)
        else (fwdallw, fwdnallw, add_bwd prems kprem concl fwdnw))
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
      let can = repr m idx in
      CanSet.add idx can.clauses_fwd cls)
 w cls

(* If early_stop is given, check raises FoundImplication as soon as
   it finds that the given atom is true *)

let _pr_w m w =
  let open Pp in
  PSet.fold (fun idx pp ->
    pr_index_point m (idx,0) ++ spc () ++ pp) w (mt())

let _pr_w m w = let open Pp in prlist_with_sep spc (fun x -> pr_index_point m (x,0)) (PSet.elements w)

let _pr_canset m (cls : CanSet.t) : Pp.t =
  let open Pp in
  CanSet.fold (fun idx fwd acc ->
    hov 1 (str "For " ++ pr_index_point m (idx,0) ++ str": " ++
      pr_fwd_clause m idx fwd) ++ fnl () ++ acc) cls (Pp.mt())

let _pr_clauses m = pr_clauses_all ~local:false m

(* model is a model for the clauses outside cls *)
let check_canset ?early_stop model ?(w=PSet.empty) (cls : CanSet.t) =
  let cV = canonical_cardinal model in
  debug_check_invariants model;
  let rec inner_loop w cardW premconclw conclw m =
    (* Should consider only clauses with conclusions in w *)
    (* Partition the clauses acscording to the presence of w in the premises *)
    (* Warning: m is not necessarily a model for w *)
    let rec inner_loop_partition w cardW premconclw conclw m =
      match loop cardW PSet.empty premconclw m with
      | Loop -> Loop
      | Model (wr, mr) ->
        (* This is only necessary when clauses do have multiple premises,
           otherwise each clause is either in premconclw and already considered
           or in conclw but then the premise cannot be updated and this is useless work *)
        (match check_clauses_with_premises ?early_stop conclw mr with
        | Some (_wconcl, mconcl) ->
          inner_loop_partition w cardW premconclw conclw mconcl
        | None -> Model (wr, mr))
      in
      inner_loop_partition w cardW premconclw conclw m
  and loop cV winit (cls : CanSet.t) m =
    match check_clauses_with_premises ?early_stop cls m with
    | None -> Model (cls, m)
    | Some (wupd, m) ->
      let w = PSet.union winit wupd in
      let cardW = PSet.cardinal w in
      if Int.equal cardW cV then Loop
      else begin
        let cls = add_fwd_clause m wupd cls in
        let (premconclw, conclw, premw) = partition_clauses_fwd m w cls in
        (match inner_loop w cardW premconclw conclw m with
        | Loop -> Loop
        | Model (wc, mc) ->
          (* wc is a subset of w *)
          (match check_clauses_with_premises ?early_stop premw mc with
          | None -> Model (wc, mc)
          | Some (w', mcls) ->
            let cls = add_fwd_clause mcls w' cls in
            loop cV (PSet.union w w') cls mcls))
      end
  in
  loop cV w cls model

let check ?early_stop model w =
  let cls = add_fwd_clause model w CanSet.empty in
  check_canset ?early_stop model ~w cls

let expr_value m (can, k) = add_opt (canonical_value m can) (- k)

let defined_expr_value m (can, k) = get_canonical_value m can - k

let _pr_levelmap (m : model) : Pp.t =
  let open Pp in
  h (prlist_with_sep fnl (fun (u, can) ->
    let value = canonical_value m can in
    let point = Index.repr u m.table in
    Level.raw_pr point ++ str" -> " ++ pr_opt int value) (PMap.bindings m.entries)) ++ fnl () ++
  h (prlist_with_sep fnl (fun (u, (e, _, _)) ->
    let value = NeList.concat_map_with max (expr_value m) (canonical_premises_repr m e) in
    let point = Index.repr u m.table in
    Level.raw_pr point ++ str" -> " ++ pr_opt int value) (PMap.bindings m.subst))

let pr_model ?(local=false) model =
  Pp.(str"clauses: " ++ pr_local model.locality ++ fnl () ++ pr_clauses_all ~local model)

type can_premises = (canonical_node * int) NeList.t
type can_expr = canonical_node * int
type can_clause = can_premises * can_expr

let _pr_can_clause m (prems, conclk) =
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
  in Some ((prems', refresh_can_expr m' (canl', conclk)), m')

let _clauses_levels cls =
  PMap.fold (fun concl _ acc -> PSet.add concl acc)
    (* (ClausesOf.fold (fun cli acc ->
      let (_, prems) = cli in
      List.fold_left (fun acc (l, _k') -> PSet.add (repr m l).canon acc) acc prems)
      cls acc)) *)
    cls PSet.empty

let infer_clauses_extension cans m =
  match check m cans with
  | Loop -> None
  | Model (_updates, model) ->
    debug_check_invariants model;
    Some model

(** [in_premises idx prems] is [true] iff [idx] appears in [prems] *)
let in_premises idx prems =
  Premises.exists (fun (idx', _) -> Index.equal idx idx') prems

(** 3 Substitution in forward and backward clauses
  of a level by an expression. *)

(** [subst_prem idx u prem] substitutes [idx] by [u] in a single premise [prem]. *)
let subst_prem idx (idx', k') (prem, k as x) =
  if Index.equal prem idx then (idx', k + k') else x

(** [subst_prems idx u prems] substitutes [idx] by [u] in all premises of [prems]. *)
let subst_prems idx u prems =
  Premises.smart_map (subst_prem idx u) prems

(** [subst_fwd_clauses idx u fwd] substitutes [idx] by [u] in the premises and conclusions of the forward clauses [fwd].
 @param fwd A set of forward clauses of shape [_, prems -> concl + k]. *)
let subst_fwd_clauses idx (idx', k' as u) fwd =
  ForwardClauses.map
    (fun ~kprem ~concl ~kconcl ~prems ->
      let prems' = Option.Smart.map (subst_prems idx u) prems in
      if Index.equal concl idx then (kprem, idx', kconcl + k', prems')
      else (kprem, concl, kconcl, prems')) fwd

(** [subst_bwd_clauses idx u bwd] substitute [idx] by [u] in the premises of the backward clauses [bwd].
  @param bwd A set of backward clauses of shape [prems -> _ + k]
  @return A set of backward clauses of shape [prems[idx/u] -> _ + k] *)
let subst_bwd_clauses idx u bwd  =
  ClausesOf.map (fun (kconcl, local, prems as cli) ->
    let prems' = subst_prems idx u prems in
    if prems' == prems then cli else (kconcl, local, prems')) bwd

(** [subst_fwd_of_prem idx u prem model] For a given premise [prem] substitute [idx] by [u]
  in the forward clauses of its canonical representative.
  @return An updated model. *)
let subst_fwd_of_prem idx u prem model =
  let can = repr model prem in
  let can = { can with clauses_fwd = subst_fwd_clauses idx u can.clauses_fwd } in
  change_node model can


(** [subst_fwd_of_bwd idx u bwd model] For a set of backward clauses [prems -> _ + kconcl] substitute
  [idx] by [u] in the forward clauses of [prems].
  @return An updated model. *)
let subst_fwd_of_bwd idx u bwd model =
  ClausesOf.fold (fun (_kconcl, _local, prems) model ->
    let f (prem, _) model = subst_fwd_of_prem idx u prem model in
    Premises._fold f prems model) bwd model

(** [subst_partial_clauses_of idx u cls model] For partial clauses [cls] of shape [(_, prems -> _)]
  substitute [idx] by [u] in the forward clauses of [prems]
  @return An updated model *)
let subst_partial_clauses_of idx u cls model =
  PartialClausesOf.fold (fun (_, prems) model ->
    Option.fold_left (fun model prems ->
      Premises._fold (fun (prem, _) -> subst_fwd_of_prem idx u prem) prems model) model prems)
    cls model

(** [subst_bwd_of_fwd_and_duplicates idx u fwd model] For forward clauses
  [_, prems -> concl + k], this substitutes [idx] by [u] in the backward clauses
  from [concl] and the forward clauses from [prems] in the model.
  @return An updated model *)
let subst_bwd_of_fwd_and_duplicates idx u fwd model =
  let f ~kprem:_ ~concl ~prems model =
    (* This s *)
    let model = subst_partial_clauses_of idx u prems model in
    let can = repr model concl in
    let bwd' = subst_bwd_clauses idx u can.clauses_bwd in
    if bwd' == can.clauses_bwd then model
    else
      let can = { can with clauses_bwd = bwd' } in
      change_node model can
  in
  ForwardClauses.fold f fwd model

module UnivSubst =
struct

(** [subst_fwd_clauses idx u fwd] substitutes [idx] by [u] in the premises and conclusions of the forward clauses [fwd].
 @param fwd A set of forward clauses [fwd] of shape [_, prems -> concl + k].
 @return A set of forward clauses representing [_, prems[idx/u] -> concl[idx/u] + k].
  Note that substituting in a single forward clause can produce multiple forward clauses,
  if [u] is a [max]. *)
let subst_fwd_clauses idx u fwd =
  ForwardClauses.fold
    (fun ~kprem ~concl ~prems fwd' ->
      let prems' =
        PartialClausesOf.map (fun (kconcl, prems) ->
          let prems' = Option.Smart.map (Premises.subst idx u) prems in
          kconcl, prems') prems
      in
      if Index.equal concl idx then
        NeList.fold (fun (concl, kconcl) fwd' ->
          ForwardClauses.add { kprem = kprem; concl; prems = PartialClausesOf.shift kconcl prems' } fwd') u fwd'
      else ForwardClauses.add { kprem; concl; prems = prems' } fwd')
      fwd ForwardClauses.empty

(** [remove_fwd_clauses idx fwd] removes forward clauses from [fwd] mentionning [idx] in either their premises or conclusions.
 @param fwd A set of forward clauses [fwd] of shape [_, prems -> concl + k]. *)
 let remove_fwd_clauses idx fwd =
  ForwardClauses.fold
    (fun ~kprem ~concl ~prems fwd' ->
      if Index.equal concl idx then fwd'
      else
        let prems' =
          PartialClausesOf.filter (fun (_kconcl, prems) ->
            Option.cata (fun p -> not (in_premises idx p)) true prems) prems
        in
        ForwardClauses.add { kprem; concl; prems = prems' } fwd')
      fwd ForwardClauses.empty

(** [subst_bwd_clauses idx u bwd] substitute [idx] by [u] in the premises of the backward clauses [bwd].
  @param bwd A set of backward clauses of shape [prems -> _ + k]
  @return A set of backward clauses of shape [prems[idx/u] -> _ + k] *)
let subst_bwd_clauses idx u bwd  =
  ClausesOf.map (fun (kconcl, local, prems as cli) ->
    let prems' = Premises.subst idx u prems in
    if prems' == prems then cli else (kconcl, local, prems')) bwd

(** [remove_bwd_clauses idx bwd] removes from the backward clauses [bwd] those that mention [idx] in one of their premises.
  @param bwd A set of backward clauses of shape [prems -> _ + k] *)
let remove_bwd_clauses idx bwd  =
  ClausesOf.filter (fun (_kconcl, _local, prems) -> not (in_premises idx prems)) bwd

(** [remove_from_fwd_clauses_of idx prem bwd] removes from the forward clauses of the canonical
  representative of [prem] those that mention [idx] in one of their premises or conclusion.
  @return An updated model *)
let remove_from_fwd_clauses_of idx prem model =
  let can = repr model prem in
  let fwd' = remove_fwd_clauses idx can.clauses_fwd in
  let can = { can with clauses_fwd = fwd' } in
  change_node model can

(** [remove_fwd_of_bwd idx bwd model] removes from the forward clauses of the canonical
  representatives in the premises of the backward clauses [bwd] those that mention [idx]
  in one of their premises or conclusion.
  @return An updated model *)
let remove_fwd_of_bwd idx bwd model =
  ClausesOf.fold (fun (_kconcl, _local, prems) model ->
    let f (prem, _) model = remove_from_fwd_clauses_of idx prem model in
    Premises._fold f prems model) bwd model

(** [remove_bwd_of_fwd_and_duplicates idx fwd model] for each forward clause [_, prems -> concl + k] in
  [fwd]: remove from the forward clauses of the canonical
  representatives of the premises [prems] those that mention [idx]
  in one of their premises or conclusion. Also removes the backward clauses of the canonical
  representative of [concl] mentionning [idx].
  @return An updated model *)
let remove_bwd_of_fwd_and_duplicates idx fwd model : t =
  let f ~kprem:_ ~concl ~prems model =
    let model =
      PartialClausesOf.fold (fun (_, prems) model ->
        Option.fold_left (fun model prems ->
          Premises._fold (fun (prem, _) -> remove_from_fwd_clauses_of idx prem) prems model) model prems)
      prems model
    in
    let can = repr model concl in
    let bwd' = remove_bwd_clauses idx can.clauses_bwd in
    if bwd' == can.clauses_bwd then model
    else
      let can = { can with clauses_bwd = bwd' } in
      change_node model can
  in
  ForwardClauses.fold f fwd model

end

let enter_equiv_expr m idx local idx' k =
  enter_equiv m idx local (NeList.Tip (idx', k))

(** [enforce_eq_can model canu canv]

  @requires canu.value = canv.value, so no new model needs to be computed.
  @returns the chosen (can + k') universe, the new [other = level + k] binding and the new model
*)
let enforce_eq_can model (canu, ku as _u) (canv, kv as _v) : (canonical_node * int) * (Index.t * (Index.t * int)) * t =
  (* assert (expr_value model u = expr_value model v); *)
  (* assert (canu != canv); *)
  (* v := u or u := v, depending on Level.is_set (for Set), and the [rigid] flags *)
  debug_check_invariants model;
  (* let model0 = model in *)
  let direction = (* true: canv := canu + k. false: canu := canv + k. *)
    if Level.is_set (Index.repr canu.canon model.table) then
      (* Set + k = l + k' -> k' < k
        -> l = Set + (k - k') *)
      (assert (kv <= ku); true)
    else if Level.is_set (Index.repr canv.canon model.table) then
      (assert (ku <= kv); false)
    else if Int.equal ku kv then
      if canu.rigid then true
      else if canv.rigid then false
      (* This heuristic choice seems to have real performance impact in e.g. math_classes/dyadics.v *)
      else if ForwardClauses.cardinal canu.clauses_fwd <= ForwardClauses.cardinal canv.clauses_fwd then
        false
      else true
    else if ku < kv then false
    else (* canu + ku = canv + kv /\ kv < ku -> canv = canu + (ku - kv) *)
      true
  in
  let can, k, other, diff, model =
    if direction then
      (canu, ku, canv, ku - kv, enter_equiv_expr model canv.canon canv.local canu.canon (ku - kv))
    else
      (canv, kv, canu, kv - ku, enter_equiv_expr model canu.canon canu.local canv.canon (kv - ku))
  in
  (* other = can + diff *)
  let can, model =
    let cank = (can.canon, diff) in
    let model, bwd, fwd =
      let newbwd = ClausesOf.union (subst_bwd_clauses other.canon cank can.clauses_bwd)
        (subst_bwd_clauses other.canon cank (ClausesOf.shift diff other.clauses_bwd))
      in
      (* prems -> other + k clauses are reindexed to become prems -> can + k clauses,
        but the forward clauses for each premise in prems still mentions the now equivalent universe *)
      let newfwd = ForwardClauses._union
        (subst_fwd_clauses other.canon cank can.clauses_fwd)
        (subst_fwd_clauses other.canon cank (ForwardClauses.shift diff other.clauses_fwd))
      in
      (* other, prems -> u + k clauses are reindexed to become can, prems -> u + k clauses,
        but the backward clauses for each u still mention other.
        We substitute to make all clauses canonical again *)
      let model = subst_fwd_of_bwd other.canon cank newbwd model in
      let model = subst_bwd_of_fwd_and_duplicates other.canon cank newfwd model in
      model, newbwd, newfwd
    in
    let can = { can with clauses_bwd = bwd; clauses_fwd = fwd } in
    can, change_node model can
  in
  debug_check_invariants model;
  (can, k), (other.canon, (can.canon, diff)), model

let _pr_can_constraints m can =
  let open Pp in
  pr_clauses_of m can.canon can.clauses_bwd ++ spc () ++
  str"Forward clauses: " ++ pr_fwd_clause m can.canon can.clauses_fwd

let pr_can_expr m (c, n) = pr_index_point m (c.canon, n)

let refresh_can_expr_can m (can, k) =
  match canonical_repr m (can.canon, k) with
  | NeList.Tip cank -> cank
  | NeList.Cons _ -> assert false (* We are only equating level expressions here. *)

let enforce_eq_can m can can' equivs =
  debug_loop_checking Pp.(fun () -> str"Merging " ++ pr_can_expr m can ++ str " and " ++ pr_can_expr m can');
  let can = refresh_can_expr_can m can in
  let can' = refresh_can_expr_can m can' in
  if fst can == fst can' then (can, equivs, m)
  else let can, other, m = enforce_eq_can m can can' in
    (can, other :: equivs, m)

let make_equiv m equiv =
  match equiv with
  | can :: can' :: tl ->
    (* We are about to merge all these universes as they should be equal in the model,
      they should hence have the same values *)
    if CDebug.(get_flag debug_loop_checking_invariants_flag) then
      assert (List.for_all (fun x -> expr_value m x = expr_value m can) (can' :: tl));
    let _can, equivs, m =
      List.fold_left (fun (can, equivs, m) can' -> enforce_eq_can m can can' equivs)
        (enforce_eq_can m can can' []) tl
    in
    m, equivs
  | _ -> m, []

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

module CN = struct
  type t = canonical_node
  let compare x y = Index.compare x.canon y.canon
end

module Status = struct

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

end


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
  let prems' = canonical_premises m prems in
  shrink_premises prems' concl conclk

let refresh_can_premises model prems =
  Premises._map (refresh_can_expr model) prems

let pr_path model path =
  let open Pp in
  prlist_with_sep spc (pr_can_expr model) path

let pr_paths model paths =
  let open Pp in
  if PathSet.is_empty paths then str"∅"
  else str"{ " ++ Pp.prlist_with_sep (fun () -> Pp.str ", ") (pr_path model) (PathSet.elements paths) ++ str" }"

let _pr_status model s =
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
  let canvalue = defined_expr_value model (canv, kv) in
  let rec backward status path (can, k) : Status.t * PathSet.t =
    match Status.find status can with
    | cstatus ->
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
      let domerge = isv || Premises.exists (fun (canu, ku) -> (can == canu && Int.equal k ku)) prems in
      let path = ((can, k) :: path) in
      let merge = if domerge then PathSet.singleton path else PathSet.empty in
      if isv then status, merge else
      let cls = can.clauses_bwd in
      if ClausesOf.is_empty cls then Status.replace status can Status.NonMerged, merge else begin
        let status = Status.replace status can Status.Processing in
        let merge_fn (clk, _local, prems) (status, merge) =
          (* Ensure there is indeed a backward clause of shape canv -> can *)
          (* prems -> can + clk *)
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
      let p = (prem, kprem + (k - clk)) in
      (* Stay in the same equivalence class *)
      let premvalue = defined_expr_value model p in
      if Int.equal premvalue canvalue then
        (* prem + kprem -> can + clk      , with k >= clk implies
            prem + kprem + (k - clk) -> can + k by upwards closure with shifting *)
          backward status path p
      else status, PathSet.empty
    in
    match prems with
    | NeList.Tip p -> merge_prem status p
    | NeList.Cons (p, ps) ->
      (* Multiple premises: we will merge the intersection of merged universes in each possible path,
         iff all premises are mergeable. *)
      let fold prem (status, merge) =
        if not (PathSet.is_empty merge) then
          let status, mergeprem = merge_prem status prem in
          if not (PathSet.is_empty mergeprem) then
            status, intersect_psets mergeprem merge
          else (* At least one premise is not bounded by v *)
            status, mergeprem
        else status, merge
      in
      NeList.fold fold ps (merge_prem status p)
  in
  let _status, merge = backward_premises 0 0 prems (status, []) in
  if PathSet.is_empty merge then []
  else
    let merge_fn p acc = if List.length p > 1 then p :: acc else acc in
    PathSet.fold merge_fn merge []

(** [get_explanation model prems concl] computes the path [concl -> prems] backward from prems, that make [prems -> concl] inconsistent

    @requires prems -> concl is inconsistent
*)
let get_explanation model prems (canv, kv) =
  let rec backward status path (can, k) : Status.t * PathSet.t =
    match Status.find status can with
    | cstatus ->
      (match cstatus with
      | Status.Processing ->
        (match find_loop can path with
        | Some path -> status, PathSet.singleton path
        | None -> status, PathSet.empty)
      | Status.Merged _ -> assert false (* No merging in get_explanation *)
      | Status.NonMerged -> status, PathSet.empty)
    | exception Not_found ->
      let isv = can == canv && k <= kv in
      let domerge = isv || Premises.exists (fun (canu, ku) -> (can == canu && Int.equal k ku)) prems in
      let path = ((can, k) :: path) in
      let path = if (k < kv) then (can, kv) :: path else path in
      let merge = if domerge then PathSet.singleton path else PathSet.empty in
      if isv then status, merge else
      let status = Status.replace status can Status.Processing in
      (* let () = incr nb_univs in *)
      let cls = can.clauses_bwd in
      if ClausesOf.is_empty cls then status, merge
      else begin
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
      let p = (prem, kprem + (k - clk)) in
      (* Stay in the same equivalence class *)
      (* prem + kprem -> can + clk      , with k >= clk implies
         prem + kprem + (k - clk) -> can + k by upwards closure with shifting *)
      backward status path p
    in
    match prems with
    | NeList.Tip p -> merge_prem status p
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
      NeList.fold fold ps (merge_prem status p)
  in
  let _status, merge = backward_premises 0 0 prems (Status.empty, []) in
  if PathSet.is_empty merge then []
  else
    let merge_fn p acc = p :: acc in
    PathSet.fold merge_fn merge []

type equivalences = (Index.t * (Index.t * int)) list

(** [simplify_clauses_between model u v] Checks if [v <= u] holds, in which case it
  merges the equivalence classes of universes between [u] and [v]. If [v] is the lub
  of [v1..vn], they might not be merged while other universes between [u] and [v] are merged.
    @param model Assumes [u <= v] holds already
    @return a potentially modified model, without changing any values *)
let simplify_clauses_between model u prems : t * equivalences =
  let premsmax = (Premises._fold (fun u m -> max_opt (expr_value model u) m) prems None) in
  if not (Option.equal Int.equal premsmax (expr_value model u)) then
      (* We know v -> u and check for u -> v, this can only be true if both expressions
        already have the same value *)
    model, []
  else
    let status = Status.empty in
    let equiv = find_to_merge_bwd model status prems u in
    let make_equiv (model, equivs) path =
      let m, equivs' = make_equiv model path in
      m, equivs' @ equivs
    in
    List.fold_left make_equiv (model,[]) equiv

type 'a check_function = t -> 'a -> 'a -> bool

let update_model_value (m : model) can k' : model =
  let v = canonical_value m can in
  let k' = max_opt v k' in
  if Option.equal Int.equal k' v then m
  else
    (debug_loop_checking Pp.(fun () -> str "Updating value of " ++ pr_index_point m (can.canon,0) ++ str " to " ++ int (Option.get k'));
    set_canonical_value m can (Option.get k'))

(** [min_can_premise model prem]
    @raises VacuouslyTrue if there is an undefined level in the premises *)
let _min_can_premise model prem =
  let g (l, k) = (match canonical_value model l with Some v -> v | None -> raise VacuouslyTrue) - k in
  let f prem minl = min minl (g prem) in
  Premises.fold_ne f g prem

let update_can_premises model prem =
  let g (model, canset) (l, k) =
    match canonical_value model l with
    | Some v -> let newv = v - k in
      if newv < 0 then
        let canset = CanSet.add l.canon l.clauses_fwd canset in
        ((update_model_value model l (Some k), canset), 0 (* k - k *)) (* Force enabling this l + k atom *)
      else ((model, canset), newv)
    | None -> raise VacuouslyTrue
  in
  let f prem (model, minl) =
    let model, gval = g model prem in
    (model, min minl gval)
  in
  Premises.fold_ne f (g model) prem


let update_model ((prems, (can, k)) : can_clause) (m : model) : PSet.t * model =
  match update_can_premises (m, CanSet.empty) prems with
  | exception VacuouslyTrue -> (PSet.empty, m)
  | ((m', canset), k0) ->
    let m' = update_model_value m' can (Some (k + k0)) in
    if m' != m then
      let canset = CanSet.add can.canon can.clauses_fwd canset in
      match check_clauses_with_premises canset m' with
      | Some (modified, wm) -> (modified, wm)
      | None -> (PSet.empty, m')
    else (PSet.empty, m)

let infer_clause_extension cl minit =
  debug_loop_checking Pp.(fun () -> str "infer_clause_extension " ++ pr_clause (pr_can_expr minit) cl);
  match add_can_clause_model minit cl with
  | None -> (* The clause was already present in the model *)
     Some minit
  | Some (cl, m) ->
    let cans, m = update_model cl m in
    if PSet.is_empty cans then begin
      (* The clause is already true in the current model,
        but might not be in an extension, so we keep it *)
      Some m
    end else
      (* The clauses are not valid in the current model, we have to find a new one *)
      (* debug Pp.(fun () -> str"Enforcing clauses requires a new inference"); *)
      infer_clauses_extension cans m

(* A clause premises -> concl + k might hold in the current minimal model without being valid in all
   its extensions.

   We generate a new minimal model starting from the premises with their minimal values making all clauses
   involving them active. I.e. we make the premises true but let the conclusion be inferred.
   Then we check that the conclusion holds in this new minimal model. *)

let check_one_clause model prems concl k =
  let model = NeList.fold (fun prem values ->
    let x, k = refresh_can_expr model prem in
    update_model_value values x (Some (max k x.value))) prems
    { model with values = Some PMap.empty }
  in
  let w, cls = NeList.fold (fun (prem, _k) (w, cls) -> (PSet.add prem.canon w, CanSet.add prem.canon prem.clauses_fwd cls)) prems (PSet.empty, CanSet.empty) in
  (* We have a model where only the premise is true, check if the conclusion follows *)
  match check_canset ~early_stop:(concl, k) model ~w cls with
  | exception FoundImplication -> true
  | Loop -> false
  | Model (_updates, model') ->
    match canonical_value model' concl with
    | None -> false
    | Some value -> k <= value

(** Enforce u <= v and check if v <= u already held, in that case, enforce u = v *)
let enforce_leq_can_internal (v, u) m =
  if (match v with NeList.Tip v -> eq_can_expr u v | _ -> false) then Some (m, [])
  else
  match infer_clause_extension (v, u) m with
  | None -> None
  | Some m' ->
    if m' != m then
      (* Looking for inverse clause and merging *)
      let u = refresh_can_expr m' u in
      let v = refresh_can_premises m' v in
      Some (simplify_clauses_between m' u v)
    else Some (m, [])

(** Simplify u <= max (Set, v) clauses to u <= v and filter away u <= ... u + n , ... clauses, always valid *)
let filter_trivial_can_clause m ((prems, (concl, k as conclk)) : can_clause) : can_clause option =
  (* Trivial ... u + k + n ... -> u + k clause *)
  if NeList.exists (fun (prem, k') -> prem == concl && k' >= k) prems then
    None
  else
    let filter (prem, k') = not (prem == concl && k' >= k) in
    match Premises.filter filter prems with
    | None -> (* We removed the only trivial premise (concl, k') -> concl, k *) None
    | Some prems ->
      (* Filter out `Set` from max(Set, u) -> v constraints *)
      let canset = Index.find Level.set m.table in
      let prems =
        match NeList.filter (fun (prem, k) -> not (Index.equal prem.canon canset && Int.equal k 0)) prems with
        | Some prems -> prems (* There were at least two premises in the rule *)
        | None -> prems
      in
      Some (prems, conclk)

let enforce_leq_can u v m =
  match filter_trivial_can_clause m (v, u) with
  | None -> Some (m, [])
  | Some cl -> enforce_leq_can_internal cl m

let canonical_repr_level_expr m (u, k) : can_premises =
  try canonical_repr m (Index.find u m.table, k)
  with Not_found ->
    CErrors.anomaly ~label:"Univ.repr"
      Pp.(str"Universe " ++ Level.raw_pr u ++ str" undefined" ++
      (if Index.mem u m.table then str" (index found)" else str " (index not found in " ++ Level.Set.pr Level.raw_pr (Index.dom m.table) ++ str")") ++ str".")

let level_expr_premises m (u, k) : Premises.t =
  try NeList.Tip (Index.find u m.table, k)
  with Not_found ->
    CErrors.anomaly ~label:"Univ.repr"
      Pp.(str"Universe " ++ Level.raw_pr u ++ str" undefined" ++
      (if Index.mem u m.table then str" (index found)" else str " (index not found in " ++ Level.Set.pr Level.raw_pr (Index.dom m.table) ++ str")") ++ str".")

let rec enforce_leq_premises (u : Premises.t) (v : Premises.t) m =
  NeList.fold (fun (u, k) res ->
    match res with
    | None -> None
    | Some (m, equivs) ->
      let canu = canonical_repr m (u, k) in
      let canv = canonical_premises_repr m v in
      match canu with
      | NeList.Tip canu ->
        (match enforce_leq_can canu canv m with
        | None -> None
        | Some (m, equivs') -> Some (m, equivs @ equivs'))
      | _ -> enforce_leq_premises (canonical_can_premises canu) v m) u (Some (m, []))

let _get_proper_value m can =
  match canonical_value m can with
  | Some v -> v
  | None -> raise (Undeclared (Index.repr can.canon m.table))

let check_eq_level_expr u v m =
  let u = canonical_repr_level_expr m u in
  let v = canonical_repr_level_expr m v in
  NeList.equal eq_can_expr u v

let _repr_can_clause m (prems, conclk) =
  let concl = refresh_can_expr m conclk in
  let prems = refresh_can_premises m prems in
  (prems, concl)

let unrepr_equivalences model (idxs : equivalences) =
  List.map (fun (idx, (idx', k)) -> (Index.repr idx model.table, (Index.repr idx' model.table, k))) idxs

let premises_of_universe m u =
  let ur = Universe.repr u in
  let prems = NeList.of_list ur in
  NeList.concat_map (level_expr_premises m) prems

let decompose_eq_constraints u k v =
  match k with
  | UnivConstraint.Le -> [(u, v)]
  | UnivConstraint.Eq -> [(u, v); (v, u)]

let enforce_constraint u k v (m : t) =
  let pu = premises_of_universe m u in
  let pv = premises_of_universe m v in
  let cls = decompose_eq_constraints pu k pv in
  List.fold_left (fun m (u, v) ->
    match m with
    | None -> None
    | Some (m, equivs) ->
      match enforce_leq_premises u v m with
      | None -> None
      | Some (m, equivs') -> Some (m, equivs @ equivs')) (Some (m, [])) cls

let enforce u k v m =
  let res = enforce_constraint u k v m in
  Option.map (fun (m, equivs) -> m, unrepr_equivalences m equivs) res

let enforce_eq u v m = enforce u UnivConstraint.Eq v m
let enforce_leq u v m = enforce u UnivConstraint.Le v m
let enforce_lt u v m = enforce_leq (Universe.addn u 1) v m

let check_leq_can canu canv model =
  match filter_trivial_can_clause model (canv, canu) with
  | None -> true
  | Some (prems, (concl, k)) ->
    check_one_clause model prems concl k

let rec check_leq_premises m (u, v) =
  NeList.fold (fun (u, k) res ->
    if res then
      let canu = canonical_repr m (u, k) in
      let canv = canonical_premises_repr m v in
      match canu with
      | NeList.Tip canu -> check_leq_can canu canv m
      | _ -> check_leq_premises m (canonical_can_premises canu, v)
    else res) u true

let check_constraint (m : t) u k u' =
  let pu = premises_of_universe m u in
  let pu' = premises_of_universe m u' in
  let cls = decompose_eq_constraints pu k pu' in
  List.fold_left (fun check cl -> check && check_leq_premises m cl) true cls

let check_leq m u v = check_constraint m u UnivConstraint.Le v
let check_eq m u v =
  match Universe.repr u, Universe.repr v with
  | [ur], [vr] -> check_eq_level_expr ur vr m
   (* || check_constraint m u UnivConstraint.Eq v *)
  | _, _ -> check_constraint m u UnivConstraint.Eq v

let enforce_constraint (u, k, v) (m : t) = enforce u k v m

exception AlreadyDeclared

let add_model ?(rigid=false) u { locality; entries; subst; table; values; canonical } =
  let idx, table =
    if Index.mem u table then
      let idx = Index.find u table in
      if PMap.mem idx entries || PMap.mem idx subst then raise AlreadyDeclared
      else (* Allow reuse *) idx, table
    else Index.fresh u table
  in
  let can = { canon = idx; value = 0; local = locality; rigid;
    clauses_fwd = ForwardClauses.empty; clauses_bwd = ClausesOf.empty } in
  let entries = PMap.add idx can entries in
  idx, { locality; entries; subst; table; values; canonical = canonical + 1; }

let add ?rigid u model =
  let _idx, model = add_model ?rigid u model in
  model

let check_declared model us =
  let check l = not (Index.mem l model.table) in
  let undeclared = Level.Set.filter check us in
  if Level.Set.is_empty undeclared then Ok ()
  else Error undeclared

let is_declared model l = Index.mem l model.table

type extended_constraint_type =
  | ULe | ULt | UEq

type explanation = Universe.t * (extended_constraint_type * Universe.t) list

let univs_of_can_premises model (hd, p) =
  (Universe.of_expr (expr_of_can_premise model hd), List.map (fun (d, e) -> (d, Universe.of_expr (expr_of_can_premise model e))) p)

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

let canonical_repr_level_expr_eq m (u, k) =
  match canonical_repr_level_expr m (u, k) with
  | NeList.Tip (can, _k' as e) ->
    let canl = Index.repr can.canon m.table in
    if not (Level.equal canl u) then
      NeList.Tip (Some (u, k), e)
    else NeList.Tip (None, e)
  | e -> NeList.map (fun x -> (None, x)) e

let _can_clause_of_clause_eqs m (prems, concl) =
  let prems = NeList.of_list prems in
  let prems = NeList.concat_map (fun prem -> canonical_repr_level_expr_eq m prem) prems in
  let premeqs =
    if NeList.exists (fun (premeq, _) -> Option.has_some premeq) prems then
      let gete (premeq, (can, k)) =
        match premeq with
        | Some e -> e
        | None -> expr_of_can_premise m (can, k)
      in
      Some (NeList.map gete prems)
    else None
  in
  let prems = NeList.map snd prems in
  let concleq, concl =
    match canonical_repr_level_expr_eq m concl with
    | NeList.Tip (concleq, concl)
    | NeList.Cons ((concleq, concl), _) -> concleq, concl (* FIXME ignoring rest of univ *)
  in
  (premeqs, concleq), (prems, concl)

let get_explanation ((l, k, r) : UnivConstraint.t) model : explanation =
  let get_explanation (prems, concl) =
    let head = Universe.super prems in
    let conclcan = canonical_repr_level_expr model concl in
    let eqconcl =
      let canu = univ_of_can_premises model conclcan in
      if Universe.equal canu (Universe.of_expr concl) then None
      else Some canu
    in
    let canprems = repr_premises model (premises_of_universe model head) in
    let expl = NeList.fold (fun concl acc ->
      match get_explanation model canprems concl with
        | [] -> acc
        | l -> List.find_opt (fun p -> List.exists (fun (can, _) -> can == fst concl) p) l) conclcan None in
    match expl with
    | None -> None
    | Some p ->
      let (hd, path) = univs_of_can_premises model (normalize_path (List.rev p)) in
      let path = match eqconcl with None -> path | Some e -> path @ [UEq, e] in
      Some (prems, (ULt, hd) :: path)
  in
  let get_explanation_le u v =
    let res = List.fold_left (fun acc l ->
      match acc with
      | None -> get_explanation (v, l)
      | Some _ -> acc) None (Universe.repr u)
    in
    match res with
    | Some expl -> expl
    | None -> (u, [])
  in
  match k with
  | UnivConstraint.Le -> get_explanation_le l r
  | UnivConstraint.Eq -> if check_leq model l r then get_explanation_le r l else get_explanation_le l r

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
  (NeList.concat_map (canonical_repr model) prems, canonical_repr model concl)

let level_expr_of_premise model (idx, k) = (Index.repr idx model.table, k)

let level_exprs_of_premises model prems =
  NeList.map (level_expr_of_premise model) prems

let univ_of_premises model u =
  Universe.unrepr (NeList.to_list (level_exprs_of_premises model u))

let repr_univ model u =
  NeList.concat_map (canonical_repr_level_expr model) (NeList.of_list (Universe.repr u))

(** Simplify u <= max (Set, v) clauses to u <= v and filter away u <= ... u + n , ... clauses, always valid. *)
let filter_trivial_clause m (prems, (concl, k as conclk)) =
  (* Trivial ... u + k + n ... -> u + k clause *)
  if NeList.exists (fun (prem, k') -> Index.equal prem concl && k' >= k) prems then None
  else
    let filter (prem, k') = not (Index.equal prem concl && k' >= k) in
    match Premises.filter filter prems with
    | None -> (* We removed the only trivial premise (concl, k') -> concl, k *) None
    | Some prems ->
      (* Filter out `Set` from max(Set, u) -> v constraints *)
      let canset = Index.find Level.set m.table in
      let prems =
        match NeList.filter (fun (prem, k) -> not (Index.equal prem canset && Int.equal k 0)) prems with
        | Some prems -> prems (* There were at least two premises in the rule *)
        | None -> prems
      in
      Some (prems, conclk)

let enforce_clause (prems, concl) model =
  enforce_leq_premises (NeList.Tip concl) prems model

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
  let newfwd = UnivSubst.subst_fwd_clauses can.canon uprems fwd in
  let newbwd = UnivSubst.subst_bwd_clauses can.canon uprems bwd in
  let model = UnivSubst.remove_bwd_of_fwd_and_duplicates can.canon newfwd model in
  let model = UnivSubst.remove_fwd_of_bwd can.canon newbwd model in
  let model = enter_equiv model can.canon can.local uprems in
  let fwdcls = ForwardClauses.to_clauses uprems newfwd in
  let bwdcls = ClausesOf.to_clauses uprems newbwd in
  let newcls = fwdcls @ List.map snd bwdcls in
  let newcls = List.filter_map (filter_trivial_clause model) newcls in
  let enforce_clause (model, equivs) cl =
    match enforce_clause cl model with
    | Some (model, equivs') -> (model, equivs' @ equivs)
    | None -> raise InconsistentEquality
  in List.fold_left enforce_clause (model, []) newcls

exception OccurCheck
exception NotCanonical

let set_can cank u model =
  if NeList.exists (fun (can', _k') -> fst cank == can') u then raise OccurCheck
  else
    let setidx = Index.find Level.set model.table in
    if Index.equal (fst cank).canon setidx then raise InconsistentEquality
    else
      let model, equivs = set_can cank u model in
      let equivs = unrepr_equivalences model equivs in
      model, equivs

let set lvl u model =
  let cank = canonical_repr_level_expr model (lvl, 0) in
  let cank =
    match cank with
    | NeList.Tip cank -> cank
    | _ -> raise NotCanonical
  in
  let u = repr_univ model u in
  set_can cank u model

type level_equivalences = (Level.t * (Level.t * int)) list

type 'a simplification_result =
  | HasSubst of 'a * level_equivalences * Universe.t
  | NoBound
  | CannotSimplify

(** [minimize idx model] returns a new model where the universe level idx has been set
  to its greatest lower bound and the new constraints are enough to derive the previous ones on all other universes.
  It returns a lower bound on idx in the original constraints, or None if it cannot be expressed.
  E.g. minimizing k when the only constraint is l + 1 <= k + 2 would result in k = l - 1 which is not a valid universe.  *)
let minimize_can can k model =
  let fwd = can.clauses_fwd in
  let glb =
    ForwardClauses.fold (fun ~kprem ~concl ~prems glb ->
      let concl = repr model concl in
      PartialClausesOf.fold (fun (conclk, _premsfwd) glb ->
        (* premsfwd, can + kprem -> concl + conclk *)
        (concl, (conclk - kprem)) :: glb)
        prems glb)
    fwd []
  in
  let sort (idx, k) (idx', k') =
    match Index.compare idx.canon idx'.canon with
    | 0 -> Int.compare k k'
    | n -> n
  in
  let glb = List.sort_uniq sort glb in
  let glb = List.remove_assq can glb in
  if CList.is_empty glb then NoBound
  else
    if List.for_all (fun (_, k) -> k >= 0) glb
    then
      let u = NeList.of_list glb in
      try
        let model, equivs = set_can (can,k) u model in
        debug_check_invariants model;
        HasSubst (model, equivs, univ_of_can_expr_list model glb)
      with InconsistentEquality | OccurCheck -> CannotSimplify
    else CannotSimplify


let minimize level model =
  match repr model (Index.find level model.table) with
  | exception Not_found -> CannotSimplify
  | can -> minimize_can can 0 model

let maximize_can can model =
  let bwd = can.clauses_bwd in
  let card = ClausesOf.cardinal bwd in
  match card with
  | 0 -> NoBound
  | n when n <> 1 -> CannotSimplify
  | _ ->
    let cank, _local, ubound = ClausesOf.choose bwd in
    if NeList.for_all (fun (_, k) -> cank <= k) ubound then
      let ubound = NeList.map (fun (can, k) -> (can, k - cank)) ubound in
      let ubound = repr_premises model ubound in
      try
        let model, equivs = set_can (can, 0) ubound model in
        HasSubst (model, equivs, univ_of_can_premises model ubound)
      with InconsistentEquality | OccurCheck -> CannotSimplify
    else CannotSimplify

let maximize level model =
  match repr model (Index.find level model.table) with
  | exception Not_found -> CannotSimplify
  | can -> maximize_can can model

let remove_bwd_clauses_from model idx k other =
  let can = repr model idx in
  let bwd = can.clauses_bwd in
  let bwd' = ClausesOf.filter (fun (kconcl, _, prems) ->
    not (Int.equal kconcl k) ||
    match prems with
    | NeList.Tip (prem, 0) -> not (Index.equal prem other)
    | _ -> true) bwd
  in
  change_node model { can with clauses_bwd = bwd' }

let replace_bwd prems kprem concl clsof =
  ForwardClauses.replace { prems; kprem; concl } clsof

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
      remove_bwd_clauses_from model setidx 0 can.canon

let remove_set_clauses l model =
  match repr model (Index.find l model.table) with
  | exception Not_found -> model
  | can -> remove_set_clauses_can can model

let pr_constraint_type k =
  let open Pp in
  match k with
  | UnivConstraint.Eq -> str " = "
  | UnivConstraint.Le -> str " ≤ "

let constraint_type_ord c1 c2 = match c1, c2 with
| UnivConstraint.Le, UnivConstraint.Le -> 0
| UnivConstraint.Le, UnivConstraint.Eq -> -1
| UnivConstraint.Eq, UnivConstraint.Eq -> 0
| UnivConstraint.Eq, UnivConstraint.Le -> 1

type univ_constraint = Universe.t * UnivConstraint.kind * Universe.t

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

let subst ~local model =
  PMap.fold (fun idx (v, locality, locality_eq) acc ->
    if not local || (local && locality_eq == Local) then
      let conclp = Index.repr idx model.table in
      let node = univ_of_premises model v in
      Level.Map.add conclp (locality, node) acc
    else acc)
  model.subst Level.Map.empty

let constraints_of_clauses ?(only_local = false) m clauses =
  PMap.fold (fun concl bwd cstrs ->
    ClausesOf.fold (fun (k, local, prems) cstrs ->
      if only_local && local == Global then cstrs
      else
      let prems = NeList.to_list prems in
      let prems =
        List.map (fun (v, k) ->
          let vcan = repr m v in
          let vp = Index.repr vcan.canon m.table in
          (vp, k)) prems
      in
      let prem = Universe.unrepr prems in
      Constraints.add (Universe.of_list [(Index.repr concl m.table, k)], UnivConstraint.Le, prem) cstrs)
      bwd cstrs)
    clauses Constraints.empty

let constraints_of model ?(only_local = false) fold acc =
  let bwd = ref PMap.empty in
  let locals = ref Level.Set.empty in
  let constraints_of _u can =
    if only_local && can.local == Local then locals := Level.Set.add (Index.repr can.canon model.table) !locals;
    bwd := PMap.add can.canon can.clauses_bwd !bwd
  in
  let () = PMap.iter constraints_of model.entries in
  let equivs_of u (v, local, local_eq) equiv =
    if only_local && local_eq == Global then equiv else
    let u = Index.repr u model.table in
    let v = canonical_premises model v in
    let v = univ_of_premises model v in
    Level.Map.add u (local, v) equiv
  in
  let equiv = PMap.fold equivs_of model.subst Level.Map.empty in
  let cstrs = constraints_of_clauses model ~only_local !bwd in
  !locals, Constraints.fold fold cstrs acc, equiv

type 'a constraint_fold = univ_constraint -> 'a -> 'a

let interp_univ model l =
  Universe.of_list (NeList.to_list (NeList.map (fun (idx, k) -> (Index.repr idx model.table, k)) l))

let constraints_for ~(kept:Level.Set.t) model (fold : 'a constraint_fold) (accu : 'a) : 'a =
  let add_cst u knd v (cst : 'a) : 'a =
    fold (interp_univ model u, knd, interp_univ model v) cst
  in
  let keptp = Level.Set.fold (fun u accu -> PSet.add (Index.find u model.table) accu) kept PSet.empty in
  (* rmap: partial map from canonical points to kept points *)
  let rmap, csts = PSet.fold (fun u (rmap,csts) ->
    let arcu = canonical_repr model (u, 0) in
    let arcu, k = match arcu with
      | NeList.Tip cank -> cank
      | NeList.Cons _ -> raise NotCanonical
    in
    if PSet.mem arcu.canon keptp then
      let csts =
        if Index.equal u arcu.canon then csts
        else
          add_cst (NeList.tip (u, 0)) UnivConstraint.Eq (NeList.tip (arcu.canon, k)) csts
      in
      PMap.add arcu.canon arcu.canon rmap, csts
    else
      match PMap.find arcu.canon rmap with
      | v -> rmap, add_cst (NeList.tip (u, 0)) UnivConstraint.Eq (NeList.tip (v, k)) csts
      | exception Not_found -> PMap.add arcu.canon u rmap, csts)
    keptp (PMap.empty, accu)
  in
  let removed =
    PMap.fold
      (fun idx can removed ->
        if PSet.mem idx keptp then removed
        else
          if PMap.mem can.canon rmap then
            (* This canonical node is represented by a kept universe, don't remove *)
            removed
          else (* Removal of a canonical node, we need to modify the clauses *)
            PSet.add can.canon removed)
    model.entries PSet.empty
  in
  let remove_can idx model =
    let can = repr model idx in
    assert (Index.equal can.canon idx);
    let fwd = can.clauses_fwd in
    let bwd = can.clauses_bwd in
    ForwardClauses.fold (fun ~kprem ~concl ~prems model ->
      let concl = repr model concl in
      PartialClausesOf.fold (fun (conclk, premsfwd) model ->
        (* premsfwd, can + kprem -> concl + conclk *)
        ClausesOf.fold (fun (cank, _local, premsbwd) model ->
          (* premsbwd -> can + cank *)
          let premsfwd = (cons_opt_nelist (can.canon, kprem) premsfwd) in
          let cl = merge_clauses premsbwd can.canon cank premsfwd concl.canon conclk in
          let cl =
            match repr_clause model cl with
            | (prems, NeList.Tip concl) -> (prems, concl)
            | _ -> assert false (* The conclusion was already canonical, cannot expand to a list of universes *)
          in
          match add_can_clause_model model cl with
          | Some (_, m) -> m
          | None -> model)
        bwd model)
      prems model)
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
  let add_from u csts prems k =
    let cprems = repr_premises model prems in
    if not (NeList.exists (fun (v, _) -> PSet.mem v.canon removed) cprems) then
      (add_cst (NeList.tip (canon_repr u, k)) UnivConstraint.Le (can_prem_to_prem cprems) csts)
    else csts
  in
  let fold u acc =
    let arc, uk =
      match canonical_repr model (u, 0) with
      | NeList.Tip can -> can
      | NeList.Cons _ -> raise NotCanonical
    in
    if not (Index.equal arc.canon u) then acc else
    let cls = arc.clauses_bwd in
    ClausesOf.fold (fun (k, _local, prems) csts -> add_from arc csts prems (k + uk)) cls acc
  in
  PSet.fold fold keptp csts

let occurs_in_premises idxs prems =
  Premises.exists (fun (idx', _) -> PSet.mem idx' idxs) prems

let remove_from_fwd idxs fwd =
  let f _kprem concl prems =
    if PSet.mem concl idxs then None
    else
      let prems = PartialClausesOf.filter (fun (_kconcl, prems) ->
        match prems with
        | None -> true
        | Some prems -> not (occurs_in_premises idxs prems))
        prems
      in
      if PartialClausesOf.is_empty prems then None else Some prems
  in
  ForwardClauses._filter_map f fwd

let remove_from_bwd idxs bwd =
  let f (_kconcl, _local, prems) = not (occurs_in_premises idxs prems) in
  ClausesOf.filter f bwd

(** [remove_from_model idxs model] Removes all clauses mentionning [idxs] and
  the canonical nodes for [idxs] from the model. The substitution is also filtered to not mention [idxs].
  The levels are still registered in the [Index] table, for possible reuse (see [add_model]) *)
let remove_from_model idxs model =
  let f idx' can =
    if PSet.mem idx' idxs then None
    else
      let clauses_fwd = remove_from_fwd idxs can.clauses_fwd in
      let clauses_bwd = remove_from_bwd idxs can.clauses_bwd in
      Some { can with clauses_fwd; clauses_bwd }
  in
  let feq idx (u, _local, _local_eq as eq) =
    if PSet.mem idx idxs then None
    else if occurs_in_premises idxs u then None
    else Some eq
  in
  let entries = PMap.filter_map f model.entries in
  let subst = PMap.filter_map feq model.subst in
  { model with entries; subst; canonical = PMap.cardinal entries }

let remove removed model =
  let removed = Level.Set.fold (fun u accu -> PSet.add (Index.find u model.table) accu) removed PSet.empty in
  (** Ensure the substitution goes to canonical universes *)
  let model = normalize_subst model in
  let remove_can idx model =
    let can = repr model idx in
    assert (Index.equal can.canon idx);
    let fwd = can.clauses_fwd in
    let bwd = can.clauses_bwd in
    ForwardClauses.fold (fun ~kprem ~concl ~prems model ->
      let concl = repr model concl in
      PartialClausesOf.fold (fun (conclk, premsfwd) model ->
        (* premsfwd, can + kprem -> concl + conclk *)
        ClausesOf.fold (fun (cank, _local, premsbwd) model ->
          (* premsbwd -> can + cank *)
          let premsfwd = (cons_opt_nelist (can.canon, kprem) premsfwd) in
          let cl = merge_clauses premsbwd can.canon cank premsfwd concl.canon conclk in
          let cl =
            match repr_clause model cl with
            | (prems, NeList.Tip concl) -> (prems, concl)
            | _ -> assert false (* The conclusion was already canonical, cannot expand to a list of universes *)
          in
          match add_can_clause_model model cl with
          | Some (_, m) -> m
          | None -> model)
        bwd model)
      prems model)
    fwd model
  in
  let removed, subst =
    let remove_from_subst idx (removed, subst) =
      if PMap.mem idx subst then (PSet.remove idx removed, PMap.remove idx subst)
      else removed, subst
    in
    PSet.fold remove_from_subst removed (removed, model.subst)
  in
  (* At this point the clauses that don't mention removed universes are enough to
     derive the clauses between kept universes *)
  let model = PSet.fold remove_can removed { model with subst } in
  remove_from_model removed model

let domain model = Index.dom model.table

let variables ~local ~with_subst model =
  let entries = if local then PMap.filter (fun _ can -> can.local == Local) model.entries else model.entries in
  let canon =
    let add idx _ = Level.Set.add (Index.repr idx model.table) in
    Index.Map.fold add entries Level.Set.empty
  in
  if with_subst then
    let add idx (_, locality, _) acc =
      if not local || locality == Local then
        Level.Set.add (Index.repr idx model.table) acc
      else acc
    in
    PMap.fold add model.subst canon
  else canon

let flip_locality = function Global -> Local | Local -> Global

let switch_locality l model =
  let can = repr model (Index.find l model.table) in
  change_node model { can with local = flip_locality can.local }

let is_local l model =
  let idx = Index.find l model.table in
  try let can = repr model idx in
    can.local == Local
  with Not_found ->
    let (_, local, _) = PMap.find idx model.subst in
    local == Local


type node =
| Alias of Universe.t
| Node of (int * Universe.t) list (** Nodes [(k_i, u_i); ...] s.t. u + k_i <= u_i *)

type repr = node Level.Map.t


let univ_of_expr model (l, k) =
  Universe.of_expr (Index.repr l model.table, k)

let universe_of_premise model prem =
  match prem with
  | NeList.Tip (l, k) -> univ_of_expr model (l, k)
  | NeList.Cons (e, xs) ->
    NeList.fold (fun (l, k) acc -> Universe.sup (univ_of_expr model (l, k)) acc) xs (univ_of_expr model e)

let repr ~local model =
  let model = normalize_subst model in
  let acc =
    PMap.fold (fun idx can acc ->
      let conclp = Index.repr idx model.table in
      let prems = can.clauses_bwd in
      let cls =
        ClausesOf.fold (fun cli l ->
          let (k, locality, prem) = cli in
          if not local || (local && locality == Local) then
            let u = universe_of_premise model prem in
            (k, u) :: l
          else l) prems []
        in
      if local && can.local == Global && CList.is_empty cls then acc
      else Level.Map.add conclp (Node cls) acc)
    model.entries Level.Map.empty
  in
  PMap.fold (fun idx (v, _, locality_eq) acc ->
    if not local || (local && locality_eq == Local) then
      let conclp = Index.repr idx model.table in
      let node = Alias (univ_of_premises model v) in
      Level.Map.add conclp node acc
    else acc)
  model.subst acc

let pmap_to_point_map table pmap =
  PMap.fold (fun idx v acc ->
    let p = Index.repr idx table in
    Level.Map.add p v acc)
    pmap Level.Map.empty

let valuation_of_model (m : model) =
  let mmax = Option.default 0 (model_max m) in
  let valm = PMap.map (fun e -> mmax - Option.get (canonical_value m e)) m.entries in
  let equivsm = PMap.map (fun (v, _, _) ->
    let v = canonical_premises_repr m v in
    let value = NeList.fold (fun (e, k) acc -> max (Option.get (canonical_value m e) - k) acc) v 0 in
    mmax - value) m.subst
  in
  Level.Map.union (fun _ x y -> Some (max x y))
    (pmap_to_point_map m.table valm)
    (pmap_to_point_map m.table equivsm)

let valuation model = valuation_of_model model
