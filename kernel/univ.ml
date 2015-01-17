(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created in Caml by Gérard Huet for CoC 4.8 [Dec 1988] *)
(* Functional code by Jean-Christophe Filliâtre for Coq V7.0 [1999] *)
(* Extension with algebraic universes by HH for Coq V7.0 [Sep 2001] *)
(* Additional support for sort-polymorphic inductive types by HH [Mar 2006] *)
(* Support for universe polymorphism by MS [2014] *)

(* Revisions by Bruno Barras, Hugo Herbelin, Pierre Letouzey, Matthieu Sozeau, 
   Pierre-Marie Pédrot *)

open Pp
open Errors
open Util

(* Universes are stratified by a partial ordering $\le$.
   Let $\~{}$ be the associated equivalence. We also have a strict ordering
   $<$ between equivalence classes, and we maintain that $<$ is acyclic,
   and contained in $\le$ in the sense that $[U]<[V]$ implies $U\le V$.

   At every moment, we have a finite number of universes, and we
   maintain the ordering in the presence of assertions $U<V$ and $U\le V$.

   The equivalence $\~{}$ is represented by a tree structure, as in the
   union-find algorithm. The assertions $<$ and $\le$ are represented by
   adjacency lists *)

module type Hashconsed =
sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val hcons : t -> t
end

module HashedList (M : Hashconsed) :
sig
  type t = private Nil | Cons of M.t * int * t
  val nil : t
  val cons : M.t -> t -> t
end =
struct
  type t = Nil | Cons of M.t * int * t
  module Self =
  struct
    type _t = t
    type t = _t
    type u = (M.t -> M.t)
    let hash = function Nil -> 0 | Cons (_, h, _) -> h
    let equal l1 l2 = match l1, l2 with
    | Nil, Nil -> true
    | Cons (x1, _, l1), Cons (x2, _, l2) -> x1 == x2 && l1 == l2
    | _ -> false
    let hashcons hc = function
    | Nil -> Nil
    | Cons (x, h, l) -> Cons (hc x, h, l)
  end
  module Hcons = Hashcons.Make(Self)
  let hcons = Hashcons.simple_hcons Hcons.generate Hcons.hcons M.hcons
  (** No recursive call: the interface guarantees that all HLists from this
      program are already hashconsed. If we get some external HList, we can
      still reconstruct it by traversing it entirely. *)
  let nil = Nil
  let cons x l =
    let h = M.hash x in
    let hl = match l with Nil -> 0 | Cons (_, h, _) -> h in
    let h = Hashset.Combine.combine h hl in
    hcons (Cons (x, h, l))
end

module HList = struct

  module type S = sig
    type elt
    type t = private Nil | Cons of elt * int * t
    val hash : t -> int
    val nil : t
    val cons : elt -> t -> t
    val tip : elt -> t
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val map : (elt -> elt) -> t -> t
    val smartmap : (elt -> elt) -> t -> t
    val exists : (elt -> bool) -> t -> bool
    val for_all : (elt -> bool) -> t -> bool
    val for_all2 : (elt -> elt -> bool) -> t -> t -> bool
    val mem : elt -> t -> bool
    val remove : elt -> t -> t
    val to_list : t -> elt list
    val compare : (elt -> elt -> int) -> t -> t -> int
  end

  module Make (H : Hashconsed) : S with type elt = H.t =
  struct
  type elt = H.t
  include HashedList(H)

  let hash = function Nil -> 0 | Cons (_, h, _) -> h

  let tip e = cons e nil

  let rec fold f l accu = match l with
  | Nil -> accu
  | Cons (x, _, l) -> fold f l (f x accu)

  let rec map f = function
  | Nil -> nil
  | Cons (x, _, l) -> cons (f x) (map f l)

  let smartmap = map
  (** Apriori hashconsing ensures that the map is equal to its argument *)

  let rec exists f = function
  | Nil -> false
  | Cons (x, _, l) -> f x || exists f l

  let rec for_all f = function
  | Nil -> true
  | Cons (x, _, l) -> f x && for_all f l

  let rec for_all2 f l1 l2 = match l1, l2 with
  | Nil, Nil -> true
  | Cons (x1, _, l1), Cons (x2, _, l2) -> f x1 x2 && for_all2 f l1 l2
  | _ -> false

  let rec to_list = function
  | Nil -> []
  | Cons (x, _, l) -> x :: to_list l

  let rec remove x = function
  | Nil -> nil
  | Cons (y, _, l) ->
    if H.equal x y then l
    else cons y (remove x l)

  let rec mem x = function
  | Nil -> false
  | Cons (y, _, l) -> H.equal x y || mem x l

  let rec compare cmp l1 l2 = match l1, l2 with
  | Nil, Nil -> 0
  | Cons (x1, h1, l1), Cons (x2, h2, l2) ->
    let c = Int.compare h1 h2 in
    if c == 0 then
      let c = cmp x1 x2 in
      if c == 0 then
        compare cmp l1 l2
      else c
    else c
  | Cons _, Nil -> 1
  | Nil, Cons _ -> -1

  end
end

module RawLevel =
struct
  open Names
  type t =
    | Prop
    | Set
    | Level of int * DirPath.t
    | Var of int

  (* Hash-consing *)

  let equal x y =
    x == y ||
      match x, y with
      | Prop, Prop -> true
      | Set, Set -> true
      | Level (n,d), Level (n',d') ->
        Int.equal n n' && DirPath.equal d d'
      | Var n, Var n' -> Int.equal n n'
      | _ -> false

  let compare u v =
    match u, v with
    | Prop,Prop -> 0
    | Prop, _ -> -1
    | _, Prop -> 1
    | Set, Set -> 0
    | Set, _ -> -1
    | _, Set -> 1
    | Level (i1, dp1), Level (i2, dp2) ->
      if i1 < i2 then -1
      else if i1 > i2 then 1
      else DirPath.compare dp1 dp2
    | Level _, _ -> -1
    | _, Level _ -> 1
    | Var n, Var m -> Int.compare n m
      
  let hcons = function
    | Prop as x -> x
    | Set as x -> x
    | Level (n,d) as x -> 
      let d' = Names.DirPath.hcons d in
        if d' == d then x else Level (n,d')
    | Var n as x -> x

  open Hashset.Combine

  let hash = function
    | Prop -> combinesmall 1 0
    | Set -> combinesmall 1 1
    | Var n -> combinesmall 2 n
    | Level (n, d) -> combinesmall 3 (combine n (Names.DirPath.hash d))

end

module Level = struct

  open Names

  type raw_level = RawLevel.t =
  | Prop
  | Set
  | Level of int * DirPath.t
  | Var of int

  (** Embed levels with their hash value *)
  type t = { 
    hash : int;
    data : RawLevel.t }

  let equal x y = 
    x == y || Int.equal x.hash y.hash && RawLevel.equal x.data y.data

  let hash x = x.hash

  let hcons x = 
    let data' = RawLevel.hcons x.data in
      if data' == x.data then x
      else { x with data = data' }

  let data x = x.data

  (** Hashcons on levels + their hash *)

  let make =
    let module Self = struct
      type _t = t
      type t = _t
      let equal = equal
      let hash = hash
    end in
    let module WH = Weak.Make(Self) in
    let pool = WH.create 4910 in fun x ->
    let x = { hash = RawLevel.hash x; data = x } in
    try WH.find pool x
    with Not_found -> WH.add pool x; x

  let set = make Set
  let prop = make Prop

  let is_small x = 
    match data x with
    | Level _ -> false
    | _ -> true

  let is_prop x =
    match data x with
    | Prop -> true
    | _ -> false

  let is_set x =
    match data x with
    | Set -> true
    | _ -> false

  let compare u v =
    if u == v then 0
    else
      let c = Int.compare (hash u) (hash v) in
	if c == 0 then RawLevel.compare (data u) (data v)
	else c

  let natural_compare u v =
    if u == v then 0
    else RawLevel.compare (data u) (data v)
	    
  let to_string x = 
    match data x with
    | Prop -> "Prop"
    | Set -> "Set"
    | Level (n,d) -> Names.DirPath.to_string d^"."^string_of_int n
    | Var n -> "Var(" ^ string_of_int n ^ ")"

  let pr u = str (to_string u)

  let apart u v =
    match data u, data v with
    | Prop, Set | Set, Prop -> true
    | _ -> false

  let vars = Array.init 20 (fun i -> make (Var i))

  let var n = 
    if n < 20 then vars.(n) else make (Var n)

  let var_index u =
    match data u with
    | Var n -> Some n | _ -> None

  let make m n = make (Level (n, Names.DirPath.hcons m))

end

(** Level maps *)
module LMap = struct 
  module M = HMap.Make (Level)
  include M

  let union l r = 
    merge (fun k l r -> 
      match l, r with
      | Some _, _ -> l
      | _, _ -> r) l r

  let subst_union l r = 
    merge (fun k l r -> 
      match l, r with
      | Some (Some _), _ -> l
      | Some None, None -> l
      | _, _ -> r) l r

  let diff ext orig =
    fold (fun u v acc -> 
      if mem u orig then acc 
      else add u v acc)
      ext empty

  let pr f m =
    h 0 (prlist_with_sep fnl (fun (u, v) ->
      Level.pr u ++ f v) (bindings m))
end

module LSet = struct
  include LMap.Set

  let pr prl s =
    str"{" ++ prlist_with_sep spc prl (elements s) ++ str"}"

  let of_array l =
    Array.fold_left (fun acc x -> add x acc) empty l

end


type 'a universe_map = 'a LMap.t

type universe_level = Level.t

type universe_level_subst_fn = universe_level -> universe_level

type universe_set = LSet.t

(* An algebraic universe [universe] is either a universe variable
   [Level.t] or a formal universe known to be greater than some
   universe variables and strictly greater than some (other) universe
   variables

   Universes variables denote universes initially present in the term
   to type-check and non variable algebraic universes denote the
   universes inferred while type-checking: it is either the successor
   of a universe present in the initial term to type-check or the
   maximum of two algebraic universes
*)

module Universe =
struct
  (* Invariants: non empty, sorted and without duplicates *)

  module Expr = 
  struct
    type t = Level.t * int
    type _t = t
	
    (* Hashing of expressions *)
    module ExprHash = 
    struct
      type t = _t
      type u = Level.t -> Level.t
      let hashcons hdir (b,n as x) = 
	let b' = hdir b in 
	  if b' == b then x else (b',n)
      let equal l1 l2 =
        l1 == l2 || 
        match l1,l2 with
	| (b,n), (b',n') -> b == b' && n == n'

      let hash (x, n) = n + Level.hash x

    end

    module HExpr = 
    struct 

      module H = Hashcons.Make(ExprHash)

      type t = ExprHash.t

      let hcons =
	Hashcons.simple_hcons H.generate H.hcons Level.hcons
      let hash = ExprHash.hash
      let equal x y = x == y ||
	(let (u,n) = x and (v,n') = y in
	   Int.equal n n' && Level.equal u v)

    end

    let hcons = HExpr.hcons

    let make l = hcons (l, 0)

    let compare u v =
      if u == v then 0
      else 
	let (x, n) = u and (x', n') = v in
	  if Int.equal n n' then Level.compare x x'
	  else n - n'

    let prop = make Level.prop
    let set = make Level.set
    let type1 = hcons (Level.set, 1)

    let is_prop = function
      | (l,0) -> Level.is_prop l
      | _ -> false
	
    let is_small = function
      | (l,0) -> Level.is_small l
      | _ -> false

    let equal x y = x == y ||
      (let (u,n) = x and (v,n') = y in
	 Int.equal n n' && Level.equal u v)

    let leq (u,n) (v,n') =
      let cmp = Level.compare u v in
	if Int.equal cmp 0 then n <= n'
	else if n <= n' then 
	  (Level.is_prop u && Level.is_small v)
	else false

    let successor (u,n) =
      if Level.is_prop u then type1
      else hcons (u, n + 1)

    let addn k (u,n as x) = 
      if k = 0 then x 
      else if Level.is_prop u then
	hcons (Level.set,n+k)
      else hcons (u,n+k)
	
    let super (u,n as x) (v,n' as y) =
      let cmp = Level.compare u v in
	if Int.equal cmp 0 then 
	  if n < n' then Inl true
	  else Inl false
	else if is_prop x then Inl true
	else if is_prop y then Inl false
	else Inr cmp

    let to_string (v, n) =
      if Int.equal n 0 then Level.to_string v
      else Level.to_string v ^ "+" ^ string_of_int n

    let pr x = str(to_string x)

    let pr_with f (v, n) = 
      if Int.equal n 0 then f v
      else f v ++ str"+" ++ int n

    let is_level = function
      | (v, 0) -> true
      | _ -> false

    let level = function
      | (v,0) -> Some v
      | _ -> None
	
    let get_level (v,n) = v

    let map f (v, n as x) = 
      let v' = f v in 
	if v' == v then x
	else if Level.is_prop v' && n != 0 then
	  hcons (Level.set, n)
	else hcons (v', n)

  end
    
  let compare_expr = Expr.compare

  module Huniv = HList.Make(Expr.HExpr)
  type t = Huniv.t
  open Huniv
    
  let equal x y = x == y || 
    (Huniv.hash x == Huniv.hash y && 
       Huniv.for_all2 Expr.equal x y)

  let hash = Huniv.hash

  let compare x y =
    if x == y then 0
    else 
      let hx = Huniv.hash x and hy = Huniv.hash y in
      let c = Int.compare hx hy in 
	if c == 0 then
	  Huniv.compare (fun e1 e2 -> compare_expr e1 e2) x y
	else c

  let rec hcons = function
  | Nil -> Huniv.nil
  | Cons (x, _, l) -> Huniv.cons x (hcons l)

  let make l = Huniv.tip (Expr.make l)
  let tip x = Huniv.tip x

  let pr l = match l with
    | Cons (u, _, Nil) -> Expr.pr u
    | _ -> 
      str "max(" ++ hov 0
	(prlist_with_sep pr_comma Expr.pr (to_list l)) ++
        str ")"

  let pr_with f l = match l with
    | Cons (u, _, Nil) -> Expr.pr_with f u
    | _ -> 
      str "max(" ++ hov 0
	(prlist_with_sep pr_comma (Expr.pr_with f) (to_list l)) ++
        str ")"

  let is_level l = match l with
    | Cons (l, _, Nil) -> Expr.is_level l
    | _ -> false

  let level l = match l with
    | Cons (l, _, Nil) -> Expr.level l
    | _ -> None

  let levels l = 
    fold (fun x acc -> LSet.add (Expr.get_level x) acc) l LSet.empty

  let is_small u = 
    match u with
    | Cons (l, _, Nil) -> Expr.is_small l
    | _ -> false

  (* The lower predicative level of the hierarchy that contains (impredicative)
     Prop and singleton inductive types *)
  let type0m = tip Expr.prop

  (* The level of sets *)
  let type0 = tip Expr.set

  (* When typing [Prop] and [Set], there is no constraint on the level,
     hence the definition of [type1_univ], the type of [Prop] *)    
  let type1 = tip (Expr.successor Expr.set)

  let is_type0m x = equal type0m x
  let is_type0 x = equal type0 x

  (* Returns the formal universe that lies juste above the universe variable u.
     Used to type the sort u. *)
  let super l = 
    if is_small l then type1
    else
      Huniv.map (fun x -> Expr.successor x) l

  let addn n l =
    Huniv.map (fun x -> Expr.addn n x) l

  let rec merge_univs l1 l2 =
    match l1, l2 with
    | Nil, _ -> l2
    | _, Nil -> l1
    | Cons (h1, _, t1), Cons (h2, _, t2) ->
      (match Expr.super h1 h2 with
      | Inl true (* h1 < h2 *) -> merge_univs t1 l2
      | Inl false -> merge_univs l1 t2
      | Inr c -> 
        if c <= 0 (* h1 < h2 is name order *)
	then cons h1 (merge_univs t1 l2)
	else cons h2 (merge_univs l1 t2))

  let sort u =
    let rec aux a l = 
      match l with
      | Cons (b, _, l') ->
        (match Expr.super a b with
	| Inl false -> aux a l'
	| Inl true -> l
	| Inr c ->
	  if c <= 0 then cons a l
	  else cons b (aux a l'))
      | Nil -> cons a l
    in 
      fold (fun a acc -> aux a acc) u nil
	
  (* Returns the formal universe that is greater than the universes u and v.
     Used to type the products. *)
  let sup x y = merge_univs x y

  let empty = nil

  let exists = Huniv.exists

  let for_all = Huniv.for_all

  let smartmap = Huniv.smartmap

end

type universe = Universe.t

(* The level of predicative Set *)
let type0m_univ = Universe.type0m
let type0_univ = Universe.type0
let type1_univ = Universe.type1
let is_type0m_univ = Universe.is_type0m
let is_type0_univ = Universe.is_type0
let is_univ_variable l = Universe.level l != None
let is_small_univ = Universe.is_small
let pr_uni = Universe.pr

let sup = Universe.sup
let super = Universe.super

open Universe

let universe_level = Universe.level

type status = Unset | SetLe | SetLt

(* Comparison on this type is pointer equality *)
type canonical_arc =
    { univ: Level.t;
      lt: Level.t list;
      le: Level.t list;
      rank : int;
      predicative : bool;
      mutable status : status;
      (** Guaranteed to be unset out of the [compare_neq] functions. It is used
          to do an imperative traversal of the graph, ensuring a O(1) check that
          a node has already been visited. Quite performance critical indeed. *)
    }

let arc_is_le arc = match arc.status with
| Unset -> false
| SetLe | SetLt -> true

let arc_is_lt arc = match arc.status with
| Unset | SetLe -> false
| SetLt -> true

let terminal u = {univ=u; lt=[]; le=[]; rank=0; predicative=false; status = Unset}

module UMap :
sig
  type key = Level.t
  type +'a t
  val empty : 'a t
  val add : key -> 'a -> 'a t -> 'a t
  val find : key -> 'a t -> 'a
  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
end = HMap.Make(Level)

(* A Level.t is either an alias for another one, or a canonical one,
   for which we know the universes that are above *)

type univ_entry =
    Canonical of canonical_arc
  | Equiv of Level.t

type universes = univ_entry UMap.t

(** Used to cleanup universes if a traversal function is interrupted before it
    has the opportunity to do it itself. *)
let unsafe_cleanup_universes g =
  let iter _ arc = match arc with
  | Equiv _ -> ()
  | Canonical arc -> arc.status <- Unset
  in
  UMap.iter iter g

let rec cleanup_universes g =
  try unsafe_cleanup_universes g
  with e ->
    (** The only way unsafe_cleanup_universes may raise an exception is when
        a serious error (stack overflow, out of memory) occurs, or a signal is
        sent. In this unlikely event, we relaunch the cleanup until we finally
        succeed. *)
    cleanup_universes g; raise e

let enter_equiv_arc u v g =
  UMap.add u (Equiv v) g

let enter_arc ca g =
  UMap.add ca.univ (Canonical ca) g

(* Every Level.t has a unique canonical arc representative *)

(* repr : universes -> Level.t -> canonical_arc *)
(* canonical representative : we follow the Equiv links *)

let repr g u =
  let rec repr_rec u =
    let a =
      try UMap.find u g
      with Not_found -> anomaly ~label:"Univ.repr"
	  (str"Universe " ++ Level.pr u ++ str" undefined")
    in
    match a with
      | Equiv v -> repr_rec v
      | Canonical arc -> arc
  in
  repr_rec u

(* [safe_repr] also search for the canonical representative, but
   if the graph doesn't contain the searched universe, we add it. *)

let safe_repr g u =
  let rec safe_repr_rec u =
    match UMap.find u g with
      | Equiv v -> safe_repr_rec v
      | Canonical arc -> arc
  in
  try g, safe_repr_rec u
  with Not_found ->
    let can = terminal u in
    enter_arc can g, can

(* reprleq : canonical_arc -> canonical_arc list *)
(* All canonical arcv such that arcu<=arcv with arcv#arcu *)
let reprleq g arcu =
  let rec searchrec w = function
    | [] -> w
    | v :: vl ->
	let arcv = repr g v in
        if List.memq arcv w || arcu==arcv then
	  searchrec w vl
        else
	  searchrec (arcv :: w) vl
  in
  searchrec [] arcu.le


(* between : Level.t -> canonical_arc -> canonical_arc list *)
(* between u v = { w | u<=w<=v, w canonical }          *)
(* between is the most costly operation *)

let between g arcu arcv =
  (* good are all w | u <= w <= v  *)
  (* bad are all w | u <= w ~<= v *)
    (* find good and bad nodes in {w | u <= w} *)
    (* explore b u = (b or "u is good") *)
  let rec explore ((good, bad, b) as input) arcu =
    if List.memq arcu good then
      (good, bad, true) (* b or true *)
    else if List.memq arcu bad then
      input    (* (good, bad, b or false) *)
    else
      let leq = reprleq g arcu in
	(* is some universe >= u good ? *)
      let good, bad, b_leq =
	List.fold_left explore (good, bad, false) leq
      in
	if b_leq then
	  arcu::good, bad, true (* b or true *)
	else
	  good, arcu::bad, b    (* b or false *)
  in
  let good,_,_ = explore ([arcv],[],false) arcu in
    good

(* We assume  compare(u,v) = LE with v canonical (see compare below).
   In this case List.hd(between g u v) = repr u
   Otherwise, between g u v = []
 *)

type constraint_type = Lt | Le | Eq

type explanation = (constraint_type * universe) list

let constraint_type_ord c1 c2 = match c1, c2 with
| Lt, Lt -> 0
| Lt, _ -> -1
| Le, Lt -> 1
| Le, Le -> 0
| Le, Eq -> -1
| Eq, Eq -> 0
| Eq, _ -> 1

(** [fast_compare_neq] : is [arcv] in the transitive upward closure of [arcu] ?

  In [strict] mode, we fully distinguish between LE and LT, while in
  non-strict mode, we simply answer LE for both situations.

  If [arcv] is encountered in a LT part, we could directly answer
  without visiting unneeded parts of this transitive closure.
  In [strict] mode, if [arcv] is encountered in a LE part, we could only
  change the default answer (1st arg [c]) from NLE to LE, since a strict
  constraint may appear later. During the recursive traversal,
  [lt_done] and [le_done] are universes we have already visited,
  they do not contain [arcv]. The 4rd arg is [(lt_todo,le_todo)],
  two lists of universes not yet considered, known to be above [arcu],
  strictly or not.

  We use depth-first search, but the presence of [arcv] in [new_lt]
  is checked as soon as possible : this seems to be slightly faster
  on a test.

  We do the traversal imperatively, setting the [status] flag on visited nodes.
  This ensures O(1) check, but it also requires unsetting the flag when leaving
  the function. Some special care has to be taken in order to ensure we do not
  recover a messed up graph at the end. This occurs in particular when the
  traversal raises an exception. Even though the code below is exception-free,
  OCaml may still raise random exceptions, essentially fatal exceptions or
  signal handlers. Therefore we ensure the cleanup by a catch-all clause. Note
  also that the use of an imperative solution does make this function
  thread-unsafe. For now we do not check universes in different threads, but if
  ever this is to be done, we would need some lock somewhere.

*)

let get_explanation strict g arcu arcv =
  (* [c] characterizes whether (and how) arcv has already been related
     to arcu among the lt_done,le_done universe *)
  let rec cmp c to_revert lt_todo le_todo = match lt_todo, le_todo with
  | [],[] -> (to_revert, c)
  | (arc,p)::lt_todo, le_todo ->
    if arc_is_lt arc then
      cmp c to_revert lt_todo le_todo
    else
      let rec find lt_todo lt le = match le with
      | [] ->
        begin match lt with
        | [] ->
          let () = arc.status <- SetLt in
          cmp c (arc :: to_revert) lt_todo le_todo
        | u :: lt ->
          let arc = repr g u in
          let p = (Lt, make u) :: p in
          if arc == arcv then
            if strict then (to_revert, p) else (to_revert, p)
          else find ((arc, p) :: lt_todo) lt le
        end
      | u :: le ->
        let arc = repr g u in
        let p = (Le, make u) :: p in
        if arc == arcv then
          if strict then (to_revert, p) else (to_revert, p)
        else find ((arc, p) :: lt_todo) lt le
      in
      find lt_todo arc.lt arc.le
  | [], (arc,p)::le_todo ->
    if arc == arcv then
      (* No need to continue inspecting universes above arc:
	 if arcv is strictly above arc, then we would have a cycle.
         But we cannot answer LE yet, a stronger constraint may
	 come later from [le_todo]. *)
      if strict then cmp p to_revert [] le_todo else (to_revert, p)
    else
      if arc_is_le arc then
        cmp c to_revert [] le_todo
      else
        let rec find lt_todo lt = match lt with
        | [] ->
          let fold accu u =
            let p = (Le, make u) :: p in
            let node = (repr g u, p) in
            node :: accu
          in
          let le_new = List.fold_left fold le_todo arc.le in
          let () = arc.status <- SetLe in
          cmp c (arc :: to_revert) lt_todo le_new
        | u :: lt ->
          let arc = repr g u in
          let p = (Lt, make u) :: p in
          if arc == arcv then
            if strict then (to_revert, p) else (to_revert, p)
          else find ((arc, p) :: lt_todo) lt
        in
        find [] arc.lt
  in
  try
    let (to_revert, c) = cmp [] [] [] [(arcu, [])] in
    (** Reset all the touched arcs. *)
    let () = List.iter (fun arc -> arc.status <- Unset) to_revert in
    List.rev c
  with e ->
    (** Unlikely event: fatal error or signal *)
    let () = cleanup_universes g in
    raise e

let get_explanation strict g arcu arcv =
  if !Flags.univ_print then Some (get_explanation strict g arcu arcv)
  else None

type fast_order = FastEQ | FastLT | FastLE | FastNLE

let fast_compare_neq strict g arcu arcv =
  (* [c] characterizes whether arcv has already been related
     to arcu among the lt_done,le_done universe *)
  let rec cmp c to_revert lt_todo le_todo = match lt_todo, le_todo with
  | [],[] -> (to_revert, c)
  | arc::lt_todo, le_todo ->
    if arc_is_lt arc then
      cmp c to_revert lt_todo le_todo
    else
      let rec find lt_todo lt le = match le with
      | [] ->
        begin match lt with
        | [] ->
          let () = arc.status <- SetLt in
          cmp c (arc :: to_revert) lt_todo le_todo
        | u :: lt ->
          let arc = repr g u in
          if arc == arcv then
            if strict then (to_revert, FastLT) else (to_revert, FastLE)
          else find (arc :: lt_todo) lt le
        end
      | u :: le ->
        let arc = repr g u in
        if arc == arcv then
          if strict then (to_revert, FastLT) else (to_revert, FastLE)
        else find (arc :: lt_todo) lt le
      in
      find lt_todo arc.lt arc.le
  | [], arc::le_todo ->
    if arc == arcv then
      (* No need to continue inspecting universes above arc:
	 if arcv is strictly above arc, then we would have a cycle.
         But we cannot answer LE yet, a stronger constraint may
	 come later from [le_todo]. *)
      if strict then cmp FastLE to_revert [] le_todo else (to_revert, FastLE)
    else
      if arc_is_le arc then
        cmp c to_revert [] le_todo
      else
        let rec find lt_todo lt = match lt with
        | [] ->
          let fold accu u =
            let node = repr g u in
            node :: accu
          in
          let le_new = List.fold_left fold le_todo arc.le in
          let () = arc.status <- SetLe in
          cmp c (arc :: to_revert) lt_todo le_new
        | u :: lt ->
          let arc = repr g u in
          if arc == arcv then
            if strict then (to_revert, FastLT) else (to_revert, FastLE)
          else find (arc :: lt_todo) lt
        in
        find [] arc.lt
  in
  try
    let (to_revert, c) = cmp FastNLE [] [] [arcu] in
    (** Reset all the touched arcs. *)
    let () = List.iter (fun arc -> arc.status <- Unset) to_revert in
    c
  with e ->
    (** Unlikely event: fatal error or signal *)
    let () = cleanup_universes g in
    raise e

let get_explanation_strict g arcu arcv = get_explanation true g arcu arcv

let fast_compare g arcu arcv =
  if arcu == arcv then FastEQ else fast_compare_neq true g arcu arcv

let is_leq g arcu arcv =
  arcu == arcv ||
    (match fast_compare_neq false g arcu arcv with
    | FastNLE -> false
    | (FastEQ|FastLE|FastLT) -> true)
    
let is_lt g arcu arcv =
  if arcu == arcv then false
  else
    match fast_compare_neq true g arcu arcv with
    | FastLT -> true
    | (FastEQ|FastLE|FastNLE) -> false

(* Invariants : compare(u,v) = EQ <=> compare(v,u) = EQ
                compare(u,v) = LT or LE => compare(v,u) = NLE
                compare(u,v) = NLE => compare(v,u) = NLE or LE or LT

   Adding u>=v is consistent iff compare(v,u) # LT
    and then it is redundant iff compare(u,v) # NLE
   Adding u>v is consistent iff compare(v,u) = NLE
    and then it is redundant iff compare(u,v) = LT *)

(** * Universe checks [check_eq] and [check_leq], used in coqchk *)

(** First, checks on universe levels *)

let check_equal g u v =
  let g, arcu = safe_repr g u in
  let _, arcv = safe_repr g v in
  arcu == arcv

let check_eq_level g u v = u == v || check_equal g u v

let is_set_arc u = Level.is_set u.univ
let is_prop_arc u = Level.is_prop u.univ
let get_prop_arc g = snd (safe_repr g Level.prop)

let check_smaller g strict u v =
  let g, arcu = safe_repr g u in
  let g, arcv = safe_repr g v in
  if strict then
    is_lt g arcu arcv
  else
    is_prop_arc arcu 
    || (is_set_arc arcu && arcv.predicative) 
    || is_leq g arcu arcv

(** Then, checks on universes *)

type 'a check_function = universes -> 'a -> 'a -> bool

let check_equal_expr g x y =
  x == y || (let (u, n) = x and (v, m) = y in 
	       Int.equal n m && check_equal g u v)

let check_eq_univs g l1 l2 =
  let f x1 x2 = check_equal_expr g x1 x2 in
  let exists x1 l = Huniv.exists (fun x2 -> f x1 x2) l in
    Huniv.for_all (fun x1 -> exists x1 l2) l1
    && Huniv.for_all (fun x2 -> exists x2 l1) l2

let check_eq g u v =
  Universe.equal u v || check_eq_univs g u v

let check_smaller_expr g (u,n) (v,m) =
  let diff = n - m in
    match diff with
    | 0 -> check_smaller g false u v
    | 1 -> check_smaller g true u v
    | x when x < 0 -> check_smaller g false u v
    | _ -> false

let exists_bigger g ul l =
  Huniv.exists (fun ul' -> 
    check_smaller_expr g ul ul') l

let real_check_leq g u v =
  Huniv.for_all (fun ul -> exists_bigger g ul v) u
    
let check_leq g u v =
  Universe.equal u v ||
    Universe.is_type0m u ||
    check_eq_univs g u v || real_check_leq g u v

(** Enforcing new constraints : [setlt], [setleq], [merge], [merge_disc] *)

(** To speed up tests of Set </<= i *)
let set_predicative g arcv = 
  enter_arc {arcv with predicative = true} g

(* setlt : Level.t -> Level.t -> reason -> unit *)
(* forces u > v *)
(* this is normally an update of u in g rather than a creation. *)
let setlt g arcu arcv =
  let arcu' = {arcu with lt=arcv.univ::arcu.lt} in
  let g = 
    if is_set_arc arcu then set_predicative g arcv
    else g
  in
    enter_arc arcu' g, arcu'

(* checks that non-redundant *)
let setlt_if (g,arcu) v =
  let arcv = repr g v in
  if is_lt g arcu arcv then g, arcu
  else setlt g arcu arcv

(* setleq : Level.t -> Level.t -> unit *)
(* forces u >= v *)
(* this is normally an update of u in g rather than a creation. *)
let setleq g arcu arcv =
  let arcu' = {arcu with le=arcv.univ::arcu.le} in
  let g = 
    if is_set_arc arcu' then
      set_predicative g arcv
    else g
  in
    enter_arc arcu' g, arcu'

(* checks that non-redundant *)
let setleq_if (g,arcu) v =
  let arcv = repr g v in
  if is_leq g arcu arcv then g, arcu
  else setleq g arcu arcv

(* merge : Level.t -> Level.t -> unit *)
(* we assume  compare(u,v) = LE *)
(* merge u v  forces u ~ v with repr u as canonical repr *)
let merge g arcu arcv =
  (* we find the arc with the biggest rank, and we redirect all others to it *)
  let arcu, g, v =
    let best_ranked (max_rank, old_max_rank, best_arc, rest) arc =
      if Level.is_small arc.univ || arc.rank >= max_rank
      then (arc.rank, max_rank, arc, best_arc::rest)
      else (max_rank, old_max_rank, best_arc, arc::rest)
    in
      match between g arcu arcv with
      | [] -> anomaly (str "Univ.between")
      | arc::rest ->
        let (max_rank, old_max_rank, best_arc, rest) =
          List.fold_left best_ranked (arc.rank, min_int, arc, []) rest in
          if max_rank > old_max_rank then best_arc, g, rest
          else begin
              (* one redirected node also has max_rank *)
            let arcu = {best_arc with rank = max_rank + 1} in
	      arcu, enter_arc arcu g, rest
          end 
  in
  let redirect (g,w,w') arcv =
    let g' = enter_equiv_arc arcv.univ arcu.univ g in
    (g',List.unionq arcv.lt w,arcv.le@w')
  in
  let (g',w,w') = List.fold_left redirect (g,[],[]) v in
  let g_arcu = (g',arcu) in
  let g_arcu = List.fold_left setlt_if g_arcu w in
  let g_arcu = List.fold_left setleq_if g_arcu w' in
  fst g_arcu

(* merge_disc : Level.t -> Level.t -> unit *)
(* we assume  compare(u,v) = compare(v,u) = NLE *)
(* merge_disc u v  forces u ~ v with repr u as canonical repr *)
let merge_disc g arc1 arc2 =
  let arcu, arcv = if arc1.rank < arc2.rank then arc2, arc1 else arc1, arc2 in
  let arcu, g = 
    if not (Int.equal arc1.rank arc2.rank) then arcu, g
    else
      let arcu = {arcu with rank = succ arcu.rank} in 
      arcu, enter_arc arcu g
  in
  let g' = enter_equiv_arc arcv.univ arcu.univ g in
  let g_arcu = (g',arcu) in
  let g_arcu = List.fold_left setlt_if g_arcu arcv.lt in
  let g_arcu = List.fold_left setleq_if g_arcu arcv.le in
  fst g_arcu

(* Universe inconsistency: error raised when trying to enforce a relation
   that would create a cycle in the graph of universes. *)

type univ_inconsistency = constraint_type * universe * universe * explanation option

exception UniverseInconsistency of univ_inconsistency

let error_inconsistency o u v (p:explanation option) =
  raise (UniverseInconsistency (o,make u,make v,p))

(* enforc_univ_eq : Level.t -> Level.t -> unit *)
(* enforc_univ_eq u v will force u=v if possible, will fail otherwise *)

let enforce_univ_eq u v g =
  let g,arcu = safe_repr g u in
  let g,arcv = safe_repr g v in
    match fast_compare g arcu arcv with
    | FastEQ -> g
    | FastLT ->
      let p = get_explanation_strict g arcu arcv in
      error_inconsistency Eq v u p
    | FastLE -> merge g arcu arcv
    | FastNLE ->
      (match fast_compare g arcv arcu with
      | FastLT ->
        let p = get_explanation_strict g arcv arcu in
        error_inconsistency Eq u v p
      | FastLE -> merge g arcv arcu
      | FastNLE -> merge_disc g arcu arcv
      | FastEQ -> anomaly (Pp.str "Univ.compare"))

(* enforce_univ_leq : Level.t -> Level.t -> unit *)
(* enforce_univ_leq u v will force u<=v if possible, will fail otherwise *)
let enforce_univ_leq u v g =
  let g,arcu = safe_repr g u in
  let g,arcv = safe_repr g v in
  if is_leq g arcu arcv then g
  else
    match fast_compare g arcv arcu with
    | FastLT ->
      let p = get_explanation_strict g arcv arcu in
      error_inconsistency Le u v p
    | FastLE  -> merge g arcv arcu
    | FastNLE -> fst (setleq g arcu arcv)
    | FastEQ -> anomaly (Pp.str "Univ.compare")

(* enforce_univ_lt u v will force u<v if possible, will fail otherwise *)
let enforce_univ_lt u v g =
  let g,arcu = safe_repr g u in
  let g,arcv = safe_repr g v in
    match fast_compare g arcu arcv with
    | FastLT -> g
    | FastLE -> fst (setlt g arcu arcv)
    | FastEQ -> error_inconsistency Lt u v (Some [(Eq,make v)])
    | FastNLE ->
      match fast_compare_neq false g arcv arcu with
	FastNLE -> fst (setlt g arcu arcv)
      | FastEQ -> anomaly (Pp.str "Univ.compare")
      | (FastLE|FastLT) ->
        let p = get_explanation false g arcv arcu  in
        error_inconsistency Lt u v p

let empty_universes = UMap.empty

(* Prop = Set is forbidden here. *)
let initial_universes = enforce_univ_lt Level.prop Level.set UMap.empty

let is_initial_universes g = UMap.equal (==) g initial_universes

let add_universe vlev g = 
  let v = terminal vlev in
  let proparc = get_prop_arc g in
    enter_arc {proparc with le=vlev::proparc.le}
      (enter_arc v g)
      
(* Constraints and sets of constraints. *)    

type univ_constraint = Level.t * constraint_type * Level.t

let enforce_constraint cst g =
  match cst with
    | (u,Lt,v) -> enforce_univ_lt u v g
    | (u,Le,v) -> enforce_univ_leq u v g
    | (u,Eq,v) -> enforce_univ_eq u v g
      
let pr_constraint_type op = 
  let op_str = match op with
    | Lt -> " < "
    | Le -> " <= "
    | Eq -> " = "
  in str op_str

module UConstraintOrd =
struct
  type t = univ_constraint
  let compare (u,c,v) (u',c',v') =
    let i = constraint_type_ord c c' in
    if not (Int.equal i 0) then i
    else
      let i' = Level.compare u u' in
      if not (Int.equal i' 0) then i'
      else Level.compare v v'
end

module Constraint = 
struct 
  module S = Set.Make(UConstraintOrd)
  include S

  let pr prl c =
    fold (fun (u1,op,u2) pp_std ->
      pp_std ++ prl u1 ++ pr_constraint_type op ++
	prl u2 ++ fnl () )  c (str "")

end

let empty_constraint = Constraint.empty
let union_constraint = Constraint.union
let eq_constraint = Constraint.equal
let merge_constraints c g =
  Constraint.fold enforce_constraint c g

type constraints = Constraint.t

module Hconstraint =
  Hashcons.Make(
    struct
      type t = univ_constraint
      type u = universe_level -> universe_level
      let hashcons hul (l1,k,l2) = (hul l1, k, hul l2)
      let equal (l1,k,l2) (l1',k',l2') =
	l1 == l1' && k == k' && l2 == l2'
      let hash = Hashtbl.hash
    end)

module Hconstraints =
  Hashcons.Make(
    struct
      type t = constraints
      type u = univ_constraint -> univ_constraint
      let hashcons huc s =
	Constraint.fold (fun x -> Constraint.add (huc x)) s Constraint.empty
      let equal s s' =
	List.for_all2eq (==)
	  (Constraint.elements s)
	  (Constraint.elements s')
      let hash = Hashtbl.hash
    end)

let hcons_constraint = Hashcons.simple_hcons Hconstraint.generate Hconstraint.hcons Level.hcons
let hcons_constraints = Hashcons.simple_hcons Hconstraints.generate Hconstraints.hcons hcons_constraint


(** A value with universe constraints. *)
type 'a constrained = 'a * constraints

let constraints_of (_, cst) = cst

(** Constraint functions. *)

type 'a constraint_function = 'a -> 'a -> constraints -> constraints

let enforce_eq_level u v c =
  (* We discard trivial constraints like u=u *)
  if Level.equal u v then c 
  else if Level.apart u v then
    error_inconsistency Eq u v None
  else Constraint.add (u,Eq,v) c

let enforce_eq u v c =
  match Universe.level u, Universe.level v with
    | Some u, Some v -> enforce_eq_level u v c
    | _ -> anomaly (Pp.str "A universe comparison can only happen between variables")

let check_univ_eq u v = Universe.equal u v

let enforce_eq u v c =
  if check_univ_eq u v then c
  else enforce_eq u v c

let constraint_add_leq v u c =
  (* We just discard trivial constraints like u<=u *)
  if Expr.equal v u then c
  else 
    match v, u with
    | (x,n), (y,m) -> 
    let j = m - n in
      if j = -1 (* n = m+1, v+1 <= u <-> v < u *) then
	Constraint.add (x,Lt,y) c
      else if j <= -1 (* n = m+k, v+k <= u <-> v+(k-1) < u *) then
	if Level.equal x y then (* u+(k+1) <= u *)
	  raise (UniverseInconsistency (Le, Universe.tip v, Universe.tip u, None))
	else anomaly (Pp.str"Unable to handle arbitrary u+k <= v constraints")
      else if j = 0 then
	Constraint.add (x,Le,y) c
      else (* j >= 1 *) (* m = n + k, u <= v+k *)
	if Level.equal x y then c (* u <= u+k, trivial *)
	else if Level.is_small x then c (* Prop,Set <= u+S k, trivial *)
	else anomaly (Pp.str"Unable to handle arbitrary u <= v+k constraints")
	  
let check_univ_leq_one u v = Universe.exists (Expr.leq u) v

let check_univ_leq u v = 
  Universe.for_all (fun u -> check_univ_leq_one u v) u

let enforce_leq u v c =
  let open Universe.Huniv in
  match v with
  | Cons (v, _, Nil) ->
    fold (fun u -> constraint_add_leq u v) u c
  | _ -> anomaly (Pp.str"A universe bound can only be a variable")

let enforce_leq u v c =
  if check_univ_leq u v then c
  else enforce_leq u v c

let enforce_leq_level u v c =
  if Level.equal u v then c else Constraint.add (u,Le,v) c

let check_constraint g (l,d,r) =
  match d with
  | Eq -> check_equal g l r
  | Le -> check_smaller g false l r
  | Lt -> check_smaller g true l r

let check_constraints c g =
  Constraint.for_all (check_constraint g) c

let enforce_univ_constraint (u,d,v) =
  match d with
  | Eq -> enforce_eq u v
  | Le -> enforce_leq u v
  | Lt -> enforce_leq (super u) v

(* Normalization *)

let lookup_level u g =
  try Some (UMap.find u g) with Not_found -> None

(** [normalize_universes g] returns a graph where all edges point
    directly to the canonical representent of their target. The output
    graph should be equivalent to the input graph from a logical point
    of view, but optimized. We maintain the invariant that the key of
    a [Canonical] element is its own name, by keeping [Equiv] edges
    (see the assertion)... I (Stéphane Glondu) am not sure if this
    plays a role in the rest of the module. *)
let normalize_universes g =
  let rec visit u arc cache = match lookup_level u cache with
    | Some x -> x, cache
    | None -> match Lazy.force arc with
    | None ->
      u, UMap.add u u cache
    | Some (Canonical {univ=v; lt=_; le=_}) ->
      v, UMap.add u v cache
    | Some (Equiv v) ->
      let v, cache = visit v (lazy (lookup_level v g)) cache in
      v, UMap.add u v cache
  in
  let cache = UMap.fold
    (fun u arc cache -> snd (visit u (Lazy.lazy_from_val (Some arc)) cache))
    g UMap.empty
  in
  let repr x = UMap.find x cache in
  let lrepr us = List.fold_left
    (fun e x -> LSet.add (repr x) e) LSet.empty us
  in
  let canonicalize u = function
    | Equiv _ -> Equiv (repr u)
    | Canonical {univ=v; lt=lt; le=le; rank=rank} ->
      assert (u == v);
      (* avoid duplicates and self-loops *)
      let lt = lrepr lt and le = lrepr le in
      let le = LSet.filter
        (fun x -> x != u && not (LSet.mem x lt)) le
      in
      LSet.iter (fun x -> assert (x != u)) lt;
      Canonical {
        univ = v;
        lt = LSet.elements lt;
        le = LSet.elements le;
	rank = rank;
	predicative = false;
	status = Unset;
      }
  in
  UMap.mapi canonicalize g

let constraints_of_universes g =
  let constraints_of u v acc =
    match v with
    | Canonical {univ=u; lt=lt; le=le} ->
      let acc = List.fold_left (fun acc v -> Constraint.add (u,Lt,v) acc) acc lt in
      let acc = List.fold_left (fun acc v -> Constraint.add (u,Le,v) acc) acc le in
	acc
    | Equiv v -> Constraint.add (u,Eq,v) acc
  in
  UMap.fold constraints_of g Constraint.empty

let constraints_of_universes g =
  constraints_of_universes (normalize_universes g)

(** Longest path algorithm. This is used to compute the minimal number of
    universes required if the only strict edge would be the Lt one. This
    algorithm assumes that the given universes constraints are a almost DAG, in
    the sense that there may be {Eq, Le}-cycles. This is OK for consistent
    universes, which is the only case where we use this algorithm. *)

(** Adjacency graph *)
type graph = constraint_type LMap.t LMap.t

exception Connected

(** Check connectedness *)
let connected x y (g : graph) =
  let rec connected x target seen g =
    if Level.equal x target then raise Connected
    else if not (LSet.mem x seen) then
      let seen = LSet.add x seen in
      let fold z _ seen = connected z target seen g in
      let neighbours = try LMap.find x g with Not_found -> LMap.empty in
      LMap.fold fold neighbours seen
    else seen
  in
  try ignore(connected x y LSet.empty g); false with Connected -> true

let add_edge x y v (g : graph) =
  try
    let neighbours = LMap.find x g in
    let neighbours = LMap.add y v neighbours in
    LMap.add x neighbours g
  with Not_found ->
    LMap.add x (LMap.singleton y v) g

(** We want to keep the graph DAG. If adding an edge would cause a cycle, that
    would necessarily be an {Eq, Le}-cycle, otherwise there would have been a
    universe inconsistency. Therefore we may omit adding such a cycling edge
    without changing the compacted graph. *)
let add_eq_edge x y v g = if connected y x g then g else add_edge x y v g

(** Construct the DAG and its inverse at the same time. *)
let make_graph g : (graph * graph) =
  let fold u arc accu = match arc with
  | Equiv v ->
    let (dir, rev) = accu in
    (add_eq_edge u v Eq dir, add_eq_edge v u Eq rev)
  | Canonical { univ; lt; le; } ->
    let () = assert (u == univ) in
    let fold_lt (dir, rev) v = (add_edge u v Lt dir, add_edge v u Lt rev) in
    let fold_le (dir, rev) v = (add_eq_edge u v Le dir, add_eq_edge v u Le rev) in
    (** Order is important : lt after le, because of the possible redundancy
        between [le] and [lt] in a canonical arc. This way, the [lt] constraint
        is the last one set, which is correct because it implies [le]. *)
    let accu = List.fold_left fold_le accu le in
    let accu = List.fold_left fold_lt accu lt in
    accu
  in
  UMap.fold fold g (LMap.empty, LMap.empty)

(** Construct a topological order out of a DAG. *)
let rec topological_fold u g rem seen accu =
  let is_seen =
    try
      let status = LMap.find u seen in
      assert status; (** If false, not a DAG! *)
      true
    with Not_found -> false
  in
  if not is_seen then
    let rem = LMap.remove u rem in
    let seen = LMap.add u false seen in
    let neighbours = try LMap.find u g with Not_found -> LMap.empty in
    let fold v _ (rem, seen, accu) = topological_fold v g rem seen accu in
    let (rem, seen, accu) = LMap.fold fold neighbours (rem, seen, accu) in
    (rem, LMap.add u true seen, u :: accu)
  else (rem, seen, accu)

let rec topological g rem seen accu =
  let node = try Some (LMap.choose rem) with Not_found -> None in
  match node with
  | None -> accu
  | Some (u, _) ->
    let rem, seen, accu = topological_fold u g rem seen accu in
    topological g rem seen accu

(** Compute the longest path from any vertex. *)
let constraint_cost = function
| Eq | Le -> 0
| Lt -> 1

(** This algorithm browses the graph in topological order, computing for each
    encountered node the length of the longest path leading to it. Should be
    O(|V|) or so (modulo map representation). *)
let rec flatten_graph rem (rev : graph) map mx = match rem with
| [] -> map, mx
| u :: rem ->
  let prev = try LMap.find u rev with Not_found -> LMap.empty in
  let fold v cstr accu =
    let v_cost = LMap.find v map in
    max (v_cost + constraint_cost cstr) accu
  in
  let u_cost = LMap.fold fold prev 0 in
  let map = LMap.add u u_cost map in
  flatten_graph rem rev map (max mx u_cost)

(** [sort_universes g] builds a map from universes in [g] to natural
    numbers. It outputs a graph containing equivalence edges from each
    level appearing in [g] to [Type.n], and [lt] edges between the
    [Type.n]s. The output graph should imply the input graph (and the
    [Type.n]s. The output graph should imply the input graph (and the
    implication will be strict most of the time), but is not
    necessarily minimal. Note: the result is unspecified if the input
    graph already contains [Type.n] nodes (calling a module Type is
    probably a bad idea anyway). *)
let sort_universes orig =
  let (dir, rev) = make_graph orig in
  let order = topological dir dir LMap.empty [] in
  let compact, max = flatten_graph order rev LMap.empty 0 in
  let mp = Names.DirPath.make [Names.Id.of_string "Type"] in
  let types = Array.init (max + 1) (fun n -> Level.make mp n) in
  (** Old universes are made equal to [Type.n] *)
  let fold u level accu = UMap.add u (Equiv types.(level)) accu in
  let sorted = LMap.fold fold compact UMap.empty in
  (** Add all [Type.n] nodes *)
  let fold i accu u =
    if 0 < i then
      let pred = types.(i - 1) in
      let arc = {univ = u; lt = [pred]; le = []; rank = 0; predicative = false; status = Unset; } in
      UMap.add u (Canonical arc) accu
    else accu
  in
  Array.fold_left_i fold sorted types

(* Miscellaneous functions to remove or test local univ assumed to
   occur in a universe *)

let univ_level_mem u v = Huniv.mem (Expr.make u) v

let univ_level_rem u v min = 
  match Universe.level v with
  | Some u' -> if Level.equal u u' then min else v
  | None -> Huniv.remove (Universe.Expr.make u) v

(* Is u mentionned in v (or equals to v) ? *)


(**********************************************************************)
(** Universe polymorphism                                             *)
(**********************************************************************)

(** A universe level substitution, note that no algebraic universes are
    involved *)

type universe_level_subst = universe_level universe_map

(** A full substitution might involve algebraic universes *)
type universe_subst = universe universe_map

let level_subst_of f = 
  fun l -> 
    try let u = f l in 
	  match Universe.level u with
	  | None -> l
	  | Some l -> l
    with Not_found -> l
     
module Instance : sig 
    type t = Level.t array

    val empty : t
    val is_empty : t -> bool
      
    val of_array : Level.t array -> t
    val to_array : t -> Level.t array

    val append : t -> t -> t
    val equal : t -> t -> bool
    val length : t -> int

    val hcons : t -> t
    val hash : t -> int

    val share : t -> t * int

    val subst_fn : universe_level_subst_fn -> t -> t
    
    val pr : (Level.t -> Pp.std_ppcmds) -> t -> Pp.std_ppcmds
    val levels : t -> LSet.t
    val check_eq : t check_function 
end = 
struct
  type t = Level.t array

  let empty : t = [||]

  module HInstancestruct =
  struct
    type _t = t
    type t = _t
    type u = Level.t -> Level.t

    let hashcons huniv a = 
      let len = Array.length a in
	if Int.equal len 0 then empty
	else begin
	  for i = 0 to len - 1 do
	    let x = Array.unsafe_get a i in
	    let x' = huniv x in
	      if x == x' then ()
	      else Array.unsafe_set a i x'
	  done;
	  a
	end

    let equal t1 t2 =
      t1 == t2 ||
	(Int.equal (Array.length t1) (Array.length t2) &&
	   let rec aux i =
	     (Int.equal i (Array.length t1)) || (t1.(i) == t2.(i) && aux (i + 1))
	   in aux 0)
	
    let hash a = 
      let accu = ref 0 in
	for i = 0 to Array.length a - 1 do
	  let l = Array.unsafe_get a i in
	  let h = Level.hash l in
	    accu := Hashset.Combine.combine !accu h;
	done;
	(* [h] must be positive. *)
	let h = !accu land 0x3FFFFFFF in
	  h
  end

  module HInstance = Hashcons.Make(HInstancestruct)

  let hcons = Hashcons.simple_hcons HInstance.generate HInstance.hcons Level.hcons
    
  let hash = HInstancestruct.hash
    
  let share a = (hcons a, hash a)
	      
  let empty = hcons [||]

  let is_empty x = Int.equal (Array.length x) 0

  let append x y =
    if Array.length x = 0 then y
    else if Array.length y = 0 then x 
    else Array.append x y

  let of_array a = a

  let to_array a = a

  let length a = Array.length a

  let subst_fn fn t = 
    let t' = CArray.smartmap fn t in
      if t' == t then t else t'

  let levels x = LSet.of_array x

  let pr =
    prvect_with_sep spc

  let equal t u = 
    t == u ||
      (Array.is_empty t && Array.is_empty u) ||
      (CArray.for_all2 Level.equal t u 
	 (* Necessary as universe instances might come from different modules and 
	    unmarshalling doesn't preserve sharing *))

  let check_eq g t1 t2 =
    t1 == t2 ||
      (Int.equal (Array.length t1) (Array.length t2) &&
	 let rec aux i =
	   (Int.equal i (Array.length t1)) || (check_eq_level g t1.(i) t2.(i) && aux (i + 1))
	 in aux 0)

end

let enforce_eq_instances x y = 
  let ax = Instance.to_array x and ay = Instance.to_array y in
    if Array.length ax != Array.length ay then
      anomaly (Pp.(++) (Pp.str "Invalid argument: enforce_eq_instances called with")
		 (Pp.str " instances of different lengths"));
    CArray.fold_right2 enforce_eq_level ax ay

type universe_instance = Instance.t

type 'a puniverses = 'a * Instance.t
let out_punivs (x, y) = x
let in_punivs x = (x, Instance.empty)
let eq_puniverses f (x, u) (y, u') =
  f x y && Instance.equal u u'

(** A context of universe levels with universe constraints,
    representiong local universe variables and constraints *)

module UContext =
struct
  type t = Instance.t constrained

  let make x = x

  (** Universe contexts (variables as a list) *)
  let empty = (Instance.empty, Constraint.empty)
  let is_empty (univs, cst) = Instance.is_empty univs && Constraint.is_empty cst

  let pr prl (univs, cst as ctx) =
    if is_empty ctx then mt() else
      Instance.pr prl univs ++ str " |= " ++ v 0 (Constraint.pr prl cst)

  let hcons (univs, cst) =
    (Instance.hcons univs, hcons_constraints cst)

  let instance (univs, cst) = univs
  let constraints (univs, cst) = cst

  let union (univs, cst) (univs', cst') =
    Instance.append univs univs', Constraint.union cst cst'
      
  let dest x = x
end

type universe_context = UContext.t
let hcons_universe_context = UContext.hcons

(** A set of universes with universe constraints.
    We linearize the set to a list after typechecking. 
    Beware, representation could change.
*)

module ContextSet =
struct
  type t = universe_set constrained

  let empty = (LSet.empty, Constraint.empty)
  let is_empty (univs, cst) = LSet.is_empty univs && Constraint.is_empty cst

  let of_set s = (s, Constraint.empty)
  let singleton l = of_set (LSet.singleton l)
  let of_instance i = of_set (Instance.levels i)

  let union (univs, cst as x) (univs', cst' as y) =
    if x == y then x
    else LSet.union univs univs', Constraint.union cst cst'

  let append (univs, cst) (univs', cst') =
    let univs = LSet.fold LSet.add univs univs' in
    let cst = Constraint.fold Constraint.add cst cst' in
    (univs, cst)

  let diff (univs, cst) (univs', cst') =
    LSet.diff univs univs', Constraint.diff cst cst'

  let add_universe u (univs, cst) =
    LSet.add u univs, cst

  let add_constraints cst' (univs, cst) =
    univs, Constraint.union cst cst'

  let add_instance inst (univs, cst) =
    let v = Instance.to_array inst in
    let fold accu u = LSet.add u accu in
    let univs = Array.fold_left fold univs v in
    (univs, cst)

  let sort_levels a = 
    Array.sort Level.natural_compare a; a

  let to_context (ctx, cst) =
    (Instance.of_array (sort_levels (Array.of_list (LSet.elements ctx))), cst)

  let of_context (ctx, cst) =
    (Instance.levels ctx, cst)

  let pr prl (univs, cst as ctx) =
    if is_empty ctx then mt() else
      LSet.pr prl univs ++ str " |= " ++ v 0 (Constraint.pr prl cst)

  let constraints (univs, cst) = cst
  let levels (univs, cst) = univs

end

type universe_context_set = ContextSet.t

(** A value in a universe context (resp. context set). *)
type 'a in_universe_context = 'a * universe_context
type 'a in_universe_context_set = 'a * universe_context_set

(** Substitutions. *)

let empty_subst = LMap.empty
let is_empty_subst = LMap.is_empty

let empty_level_subst = LMap.empty
let is_empty_level_subst = LMap.is_empty

(** Substitution functions *)

(** With level to level substitutions. *)
let subst_univs_level_level subst l =
  try LMap.find l subst
  with Not_found -> l

let subst_univs_level_universe subst u =
  let f x = Universe.Expr.map (fun u -> subst_univs_level_level subst u) x in
  let u' = Universe.smartmap f u in
    if u == u' then u
    else Universe.sort u'

let subst_univs_level_instance subst i =
  let i' = Instance.subst_fn (subst_univs_level_level subst) i in
    if i == i' then i
    else i'
	
let subst_univs_level_constraint subst (u,d,v) =
  let u' = subst_univs_level_level subst u 
  and v' = subst_univs_level_level subst v in
    if d != Lt && Level.equal u' v' then None
    else Some (u',d,v')

let subst_univs_level_constraints subst csts =
  Constraint.fold 
    (fun c -> Option.fold_right Constraint.add (subst_univs_level_constraint subst c))
    csts Constraint.empty 

(** With level to universe substitutions. *)
type universe_subst_fn = universe_level -> universe

let make_subst subst = fun l -> LMap.find l subst

let subst_univs_expr_opt fn (l,n) =
  Universe.addn n (fn l)

let subst_univs_universe fn ul =
  let subst, nosubst = 
    Universe.Huniv.fold (fun u (subst,nosubst) -> 
      try let a' = subst_univs_expr_opt fn u in
	    (a' :: subst, nosubst)
      with Not_found -> (subst, u :: nosubst))
      ul ([], [])
  in 
    if CList.is_empty subst then ul
    else 
      let substs = 
	List.fold_left Universe.merge_univs Universe.empty subst
      in
	List.fold_left (fun acc u -> Universe.merge_univs acc (Universe.Huniv.tip u))
	  substs nosubst

let subst_univs_level fn l = 
  try Some (fn l)
  with Not_found -> None

let subst_univs_constraint fn (u,d,v as c) cstrs =
  let u' = subst_univs_level fn u in
  let v' = subst_univs_level fn v in
  match u', v' with
  | None, None -> Constraint.add c cstrs
  | Some u, None -> enforce_univ_constraint (u,d,make v) cstrs
  | None, Some v -> enforce_univ_constraint (make u,d,v) cstrs
  | Some u, Some v -> enforce_univ_constraint (u,d,v) cstrs

let subst_univs_constraints subst csts =
  Constraint.fold 
    (fun c cstrs -> subst_univs_constraint subst c cstrs)
    csts Constraint.empty 

let subst_instance_level s l =
  match l.Level.data with
  | Level.Var n -> s.(n) 
  | _ -> l

let subst_instance_instance s i = 
  Array.smartmap (fun l -> subst_instance_level s l) i

let subst_instance_universe s u =
  let f x = Universe.Expr.map (fun u -> subst_instance_level s u) x in
  let u' = Universe.smartmap f u in
    if u == u' then u
    else Universe.sort u'

let subst_instance_constraint s (u,d,v as c) =
  let u' = subst_instance_level s u in
  let v' = subst_instance_level s v in
    if u' == u && v' == v then c
    else (u',d,v')

let subst_instance_constraints s csts =
  Constraint.fold 
    (fun c csts -> Constraint.add (subst_instance_constraint s c) csts)
    csts Constraint.empty 

(** Substitute instance inst for ctx in csts *)
let instantiate_univ_context (ctx, csts) = 
  (ctx, subst_instance_constraints ctx csts)

let instantiate_univ_constraints u (_, csts) = 
  subst_instance_constraints u csts

let make_instance_subst i = 
  let arr = Instance.to_array i in
    Array.fold_left_i (fun i acc l ->
      LMap.add l (Level.var i) acc)
      LMap.empty arr

let make_inverse_instance_subst i = 
  let arr = Instance.to_array i in
    Array.fold_left_i (fun i acc l ->
      LMap.add (Level.var i) l acc)
      LMap.empty arr

let abstract_universes poly ctx =
  let instance = UContext.instance ctx in
    if poly then
      let subst = make_instance_subst instance in
      let cstrs = subst_univs_level_constraints subst 
	(UContext.constraints ctx)
      in
      let ctx = UContext.make (instance, cstrs) in
	subst, ctx
    else empty_level_subst, ctx

(** Pretty-printing *)

let pr_arc prl = function
  | _, Canonical {univ=u; lt=[]; le=[]} ->
      mt ()
  | _, Canonical {univ=u; lt=lt; le=le} ->
      let opt_sep = match lt, le with
      | [], _ | _, [] -> mt ()
      | _ -> spc ()
      in
      prl u ++ str " " ++
      v 0
        (pr_sequence (fun v -> str "< " ++ prl v) lt ++
	 opt_sep ++
         pr_sequence (fun v -> str "<= " ++ prl v) le) ++
      fnl ()
  | u, Equiv v ->
      prl u  ++ str " = " ++ prl v ++ fnl ()

let pr_universes prl g =
  let graph = UMap.fold (fun u a l -> (u,a)::l) g [] in
  prlist (pr_arc prl) graph

let pr_constraints prl = Constraint.pr prl

let pr_universe_context = UContext.pr

let pr_universe_context_set = ContextSet.pr

let pr_universe_subst = 
  LMap.pr (fun u -> str" := " ++ Universe.pr u ++ spc ())

let pr_universe_level_subst = 
  LMap.pr (fun u -> str" := " ++ Level.pr u ++ spc ())

(* Dumping constraints to a file *)

let dump_universes output g =
  let dump_arc u = function
    | Canonical {univ=u; lt=lt; le=le} ->
	let u_str = Level.to_string u in
	List.iter (fun v -> output Lt (Level.to_string v) u_str) lt;
	List.iter (fun v -> output Le (Level.to_string v) u_str) le
    | Equiv v ->
      output Eq (Level.to_string u) (Level.to_string v)
  in
  UMap.iter dump_arc g

module Huniverse_set = 
  Hashcons.Make(
    struct
      type t = universe_set
      type u = universe_level -> universe_level
      let hashcons huc s =
	LSet.fold (fun x -> LSet.add (huc x)) s LSet.empty
      let equal s s' =
	LSet.equal s s'
      let hash = Hashtbl.hash
    end)

let hcons_universe_set = 
  Hashcons.simple_hcons Huniverse_set.generate Huniverse_set.hcons Level.hcons

let hcons_universe_context_set (v, c) = 
  (hcons_universe_set v, hcons_constraints c)

let hcons_univ x = Universe.hcons x

let explain_universe_inconsistency prl (o,u,v,p) =
  let pr_uni = Universe.pr_with prl in
  let pr_rel = function
    | Eq -> str"=" | Lt -> str"<" | Le -> str"<=" 
  in
  let reason = match p with
    | None | Some [] -> mt()
    | Some p ->
      str " because" ++ spc() ++ pr_uni v ++
	prlist (fun (r,v) -> spc() ++ pr_rel r ++ str" " ++ pr_uni v)
	p ++
	(if Universe.equal (snd (List.last p)) u then mt() else
	    (spc() ++ str "= " ++ pr_uni u)) 
  in
    str "Cannot enforce" ++ spc() ++ pr_uni u ++ spc() ++
      pr_rel o ++ spc() ++ pr_uni v ++ reason ++ str")"

let compare_levels = Level.compare
let eq_levels = Level.equal
let equal_universes = Universe.equal


let subst_instance_constraints = 
  if Flags.profile then 
    let key = Profile.declare_profile "subst_instance_constraints" in
      Profile.profile2 key subst_instance_constraints
  else subst_instance_constraints

let merge_constraints = 
  if Flags.profile then 
    let key = Profile.declare_profile "merge_constraints" in
      Profile.profile2 key merge_constraints
  else merge_constraints
let check_constraints =
  if Flags.profile then
    let key = Profile.declare_profile "check_constraints" in
      Profile.profile2 key check_constraints
  else check_constraints

let check_eq = 
  if Flags.profile then
    let check_eq_key = Profile.declare_profile "check_eq" in
      Profile.profile3 check_eq_key check_eq
  else check_eq

let check_leq = 
  if Flags.profile then 
    let check_leq_key = Profile.declare_profile "check_leq" in
      Profile.profile3 check_leq_key check_leq
  else check_leq
