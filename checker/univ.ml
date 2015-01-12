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

(* Revisions by Bruno Barras, Hugo Herbelin, Pierre Letouzey *)

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
    val remove : elt -> t -> t
    val to_list : t -> elt list
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
	    
  let to_string x = 
    match data x with
    | Prop -> "Prop"
    | Set -> "Set"
    | Level (n,d) -> Names.DirPath.to_string d^"."^string_of_int n
    | Var i -> "Var("^string_of_int i^")"

  let pr u = str (to_string u)

  let make m n = make (Level (n, Names.DirPath.hcons m))

end

(** Level sets and maps *)
module LSet = Set.Make (Level)
module LMap = Map.Make (Level)

type 'a universe_map = 'a LMap.t

type universe_level = Level.t

type universe_level_subst_fn = universe_level -> universe_level

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

    let prop = make Level.prop
    let set = make Level.set
    let type1 = hcons (Level.set, 1)

    let is_prop = function
      | (l,0) -> Level.is_prop l
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

    let level = function
      | (v,0) -> Some v
      | _ -> None

    let map f (v, n as x) = 
      let v' = f v in 
	if v' == v then x
	else if Level.is_prop v' && n != 0 then
	  hcons (Level.set, n)
	else hcons (v', n)

  end
    
  module Huniv = HList.Make(Expr.HExpr)
  type t = Huniv.t
  open Huniv
    
  let equal x y = x == y || 
    (Huniv.hash x == Huniv.hash y && 
       Huniv.for_all2 Expr.equal x y)

  let make l = Huniv.tip (Expr.make l)
  let tip x = Huniv.tip x
    
  let pr l = match l with
    | Cons (u, _, Nil) -> Expr.pr u
    | _ -> 
      str "max(" ++ hov 0
	(prlist_with_sep pr_comma Expr.pr (to_list l)) ++
        str ")"

  let level l = match l with
    | Cons (l, _, Nil) -> Expr.level l
    | _ -> None

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
let pr_uni = Universe.pr

let sup = Universe.sup
let super = Universe.super

open Universe

(* Comparison on this type is pointer equality *)
type canonical_arc =
    { univ: Level.t;
      lt: Level.t list;
      le: Level.t list;
      rank : int;
      predicative : bool}

let terminal u = {univ=u; lt=[]; le=[]; rank=0; predicative=false}

module UMap :
sig
  type key = Level.t
  type +'a t
  val empty : 'a t
  val add : key -> 'a -> 'a t -> 'a t
  val find : key -> 'a t -> 'a
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
end = HMap.Make(Level)

(* A Level.t is either an alias for another one, or a canonical one,
   for which we know the universes that are above *)

type univ_entry =
    Canonical of canonical_arc
  | Equiv of Level.t

type universes = univ_entry UMap.t

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

let constraint_type_ord c1 c2 = match c1, c2 with
| Lt, Lt -> 0
| Lt, _ -> -1
| Le, Lt -> 1
| Le, Le -> 0
| Le, Eq -> -1
| Eq, Eq -> 0
| Eq, _ -> 1

(** [compare_neq] : is [arcv] in the transitive upward closure of [arcu] ?

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
*)

type fast_order = FastEQ | FastLT | FastLE | FastNLE

let fast_compare_neq strict g arcu arcv =
  (* [c] characterizes whether arcv has already been related
     to arcu among the lt_done,le_done universe *)
  let rec cmp c lt_done le_done lt_todo le_todo = match lt_todo, le_todo with
  | [],[] -> c
  | arc::lt_todo, le_todo ->
    if List.memq arc lt_done then
      cmp c lt_done le_done lt_todo le_todo
    else
      let rec find lt_todo lt le = match le with
      | [] ->
        begin match lt with
        | [] -> cmp c (arc :: lt_done) le_done lt_todo le_todo
        | u :: lt ->
          let arc = repr g u in
          if arc == arcv then
            if strict then FastLT else FastLE
          else find (arc :: lt_todo) lt le
        end
      | u :: le ->
        let arc = repr g u in
        if arc == arcv then
          if strict then FastLT else FastLE
        else find (arc :: lt_todo) lt le
      in
      find lt_todo arc.lt arc.le
  | [], arc::le_todo ->
    if arc == arcv then
      (* No need to continue inspecting universes above arc:
	 if arcv is strictly above arc, then we would have a cycle.
         But we cannot answer LE yet, a stronger constraint may
	 come later from [le_todo]. *)
      if strict then cmp FastLE lt_done le_done [] le_todo else FastLE
    else
      if (List.memq arc lt_done) || (List.memq arc le_done) then
        cmp c lt_done le_done [] le_todo
      else
        let rec find lt_todo lt = match lt with
        | [] ->
          let fold accu u =
            let node = repr g u in
            node :: accu
          in
          let le_new = List.fold_left fold le_todo arc.le in
          cmp c lt_done (arc :: le_done) lt_todo le_new
        | u :: lt ->
          let arc = repr g u in
          if arc == arcv then
            if strict then FastLT else FastLE
          else find (arc :: lt_todo) lt
        in
        find [] arc.lt
  in
  cmp FastNLE [] [] [] [arcu]

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

type univ_inconsistency = constraint_type * universe * universe

exception UniverseInconsistency of univ_inconsistency

let error_inconsistency o u v =
  raise (UniverseInconsistency (o,make u,make v))

(* enforc_univ_eq : Level.t -> Level.t -> unit *)
(* enforc_univ_eq u v will force u=v if possible, will fail otherwise *)

let enforce_univ_eq u v g =
  let g,arcu = safe_repr g u in
  let g,arcv = safe_repr g v in
    match fast_compare g arcu arcv with
    | FastEQ -> g
    | FastLT -> error_inconsistency Eq v u
    | FastLE -> merge g arcu arcv
    | FastNLE ->
      (match fast_compare g arcv arcu with
      | FastLT -> error_inconsistency Eq u v
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
    | FastLT -> error_inconsistency Le u v
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
    | FastEQ -> error_inconsistency Lt u v
    | FastNLE ->
      match fast_compare_neq false g arcv arcu with
	FastNLE -> fst (setlt g arcu arcv)
      | FastEQ -> anomaly (Pp.str "Univ.compare")
      | FastLE | FastLT -> error_inconsistency Lt u v

(* Prop = Set is forbidden here. *)
let initial_universes = enforce_univ_lt Level.prop Level.set UMap.empty

(* Constraints and sets of constraints. *)    

type univ_constraint = Level.t * constraint_type * Level.t

let enforce_constraint cst g =
  match cst with
    | (u,Lt,v) -> enforce_univ_lt u v g
    | (u,Le,v) -> enforce_univ_leq u v g
    | (u,Eq,v) -> enforce_univ_eq u v g

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

module Constraint = Set.Make(UConstraintOrd)

let empty_constraint = Constraint.empty
let merge_constraints c g =
  Constraint.fold enforce_constraint c g

type constraints = Constraint.t

(** A value with universe constraints. *)
type 'a constrained = 'a * constraints

(** Constraint functions. *)

type 'a constraint_function = 'a -> 'a -> constraints -> constraints

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
	  raise (UniverseInconsistency (Le, Universe.tip v, Universe.tip u))
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
  match v with
  | Universe.Huniv.Cons (v, _, Universe.Huniv.Nil) ->
    Universe.Huniv.fold (fun u -> constraint_add_leq u v) u c
  | _ -> anomaly (Pp.str"A universe bound can only be a variable")

let enforce_leq u v c =
  if check_univ_leq u v then c
  else enforce_leq u v c

let check_constraint g (l,d,r) =
  match d with
  | Eq -> check_equal g l r
  | Le -> check_smaller g false l r
  | Lt -> check_smaller g true l r

let check_constraints c g =
  Constraint.for_all (check_constraint g) c

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
    val equal : t -> t -> bool
    val subst_fn : universe_level_subst_fn -> t -> t
    val subst : universe_level_subst -> t -> t
    val pr : t -> Pp.std_ppcmds
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
    
  let empty = hcons [||]

  let is_empty x = Int.equal (Array.length x) 0

  let subst_fn fn t = 
    let t' = CArray.smartmap fn t in
      if t' == t then t else hcons t'

  let subst s t =
    let t' = 
      CArray.smartmap (fun x -> try LMap.find x s with Not_found -> x) t
    in if t' == t then t else hcons t'

  let pr =
    prvect_with_sep spc Level.pr

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

type universe_instance = Instance.t

type 'a puniverses = 'a * Instance.t
(** A context of universe levels with universe constraints,
    representiong local universe variables and constraints *)

module UContext =
struct
  type t = Instance.t constrained

  (** Universe contexts (variables as a list) *)
  let empty = (Instance.empty, Constraint.empty)

  let instance (univs, cst) = univs
  let constraints (univs, cst) = cst
end

type universe_context = UContext.t

module ContextSet =
struct
  type t = LSet.t constrained
  let empty = LSet.empty, Constraint.empty
  let constraints (_, cst) = cst
end
type universe_context_set = ContextSet.t

(** Substitutions. *)

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

(** Substitute instance inst for ctx in csts *)

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

(** Pretty-printing *)

let pr_arc = function
  | _, Canonical {univ=u; lt=[]; le=[]} ->
      mt ()
  | _, Canonical {univ=u; lt=lt; le=le} ->
      let opt_sep = match lt, le with
      | [], _ | _, [] -> mt ()
      | _ -> spc ()
      in
      Level.pr u ++ str " " ++
      v 0
        (pr_sequence (fun v -> str "< " ++ Level.pr v) lt ++
	 opt_sep ++
         pr_sequence (fun v -> str "<= " ++ Level.pr v) le) ++
      fnl ()
  | u, Equiv v ->
      Level.pr u  ++ str " = " ++ Level.pr v ++ fnl ()

let pr_universes g =
  let graph = UMap.fold (fun u a l -> (u,a)::l) g [] in
  prlist pr_arc graph
