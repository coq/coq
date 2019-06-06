(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created in Caml by Gérard Huet for CoC 4.8 [Dec 1988] *)
(* Functional code by Jean-Christophe Filliâtre for Coq V7.0 [1999] *)
(* Extension with algebraic universes by HH for Coq V7.0 [Sep 2001] *)
(* Additional support for sort-polymorphic inductive types by HH [Mar 2006] *)
(* Support for universe polymorphism by MS [2014] *)

(* Revisions by Bruno Barras, Hugo Herbelin, Pierre Letouzey, Matthieu
   Sozeau, Pierre-Marie Pédrot *)

open Pp
open CErrors
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

module RawLevel =
struct
  open Names

  module UGlobal = struct
    type t = DirPath.t * int

    let make dp i = (DirPath.hcons dp,i)

    let equal (d, i) (d', i') = DirPath.equal d d' && Int.equal i i'

    let hash (d,i) = Hashset.Combine.combine i (DirPath.hash d)

    let compare (d, i) (d', i') =
      let c = Int.compare i i' in
      if Int.equal c 0 then DirPath.compare d d'
      else c
  end

  type t =
    | SProp
    | Prop
    | Set
    | Level of UGlobal.t
    | Var of int

  (* Hash-consing *)

  let equal x y =
    x == y ||
      match x, y with
      | SProp, SProp -> true
      | Prop, Prop -> true
      | Set, Set -> true
      | Level l, Level l' -> UGlobal.equal l l'
      | Var n, Var n' -> Int.equal n n'
      | _ -> false

  let compare u v =
    match u, v with
    | SProp, SProp -> 0
    | SProp, _ -> -1
    | _, SProp -> 1
    | Prop,Prop -> 0
    | Prop, _ -> -1
    | _, Prop -> 1
    | Set, Set -> 0
    | Set, _ -> -1
    | _, Set -> 1
    | Level (dp1, i1), Level (dp2, i2) ->
      if i1 < i2 then -1
      else if i1 > i2 then 1
      else DirPath.compare dp1 dp2
    | Level _, _ -> -1
    | _, Level _ -> 1
    | Var n, Var m -> Int.compare n m

  let hequal x y =
    x == y ||
      match x, y with
      | SProp, SProp -> true
      | Prop, Prop -> true
      | Set, Set -> true
      | Level (n,d), Level (n',d') ->
        n == n' && d == d'
      | Var n, Var n' -> n == n'
      | _ -> false

  let hcons = function
    | SProp as x -> x
    | Prop as x -> x
    | Set as x -> x
    | Level (d,n) as x ->
      let d' = Names.DirPath.hcons d in
        if d' == d then x else Level (d',n)
    | Var _n as x -> x

  open Hashset.Combine

  let hash = function
    | SProp -> combinesmall 1 0
    | Prop -> combinesmall 1 1
    | Set -> combinesmall 1 2
    | Var n -> combinesmall 2 n
    | Level (d, n) -> combinesmall 3 (combine n (Names.DirPath.hash d))

end

module Level = struct

  module UGlobal = RawLevel.UGlobal

  type raw_level = RawLevel.t =
  | SProp
  | Prop
  | Set
  | Level of UGlobal.t
  | Var of int

  (** Embed levels with their hash value *)
  type t = { 
    hash : int;
    data : RawLevel.t }

  let equal x y = 
    x == y || Int.equal x.hash y.hash && RawLevel.equal x.data y.data

  let hash x = x.hash

  let data x = x.data

  (** Hashcons on levels + their hash *)

  module Self = struct
    type nonrec t = t
    type u = unit
    let eq x y = x.hash == y.hash && RawLevel.hequal x.data y.data
    let hash x = x.hash
    let hashcons () x =
      let data' = RawLevel.hcons x.data in
      if x.data == data' then x else { x with data = data' }
  end

  let hcons =
    let module H = Hashcons.Make(Self) in
    Hashcons.simple_hcons H.generate H.hcons ()

  let make l = hcons { hash = RawLevel.hash l; data = l }

  let set = make Set
  let prop = make Prop
  let sprop = make SProp

  let is_small x = 
    match data x with
    | Level _ -> false
    | Var _ -> false
    | SProp -> true
    | Prop -> true
    | Set -> true
 
  let is_prop x =
    match data x with
    | Prop -> true
    | _ -> false

  let is_set x =
    match data x with
    | Set -> true
    | _ -> false

  let is_sprop x =
    match data x with
    | SProp -> true
    | _ -> false

  let compare u v =
    if u == v then 0
    else RawLevel.compare (data u) (data v)
	    
  let to_string x = 
    match data x with
    | SProp -> "SProp"
    | Prop -> "Prop"
    | Set -> "Set"
    | Level (d,n) -> Names.DirPath.to_string d^"."^string_of_int n
    | Var n -> "Var(" ^ string_of_int n ^ ")"

  let pr u = str (to_string u)

  let apart u v =
    match data u, data v with
    | SProp, _ | _, SProp
    | Prop, Set | Set, Prop -> true
    | _ -> false

  let vars = Array.init 20 (fun i -> make (Var i))

  let var n = 
    if n < 20 then vars.(n) else make (Var n)

  let var_index u =
    match data u with
    | Var n -> Some n | _ -> None

  let make qid = make (Level qid)

  let name u =
    match data u with
    | Level (d, n) -> Some (d, n)
    | _ -> None
end

(** Level maps *)
module LMap = struct 
  module M = HMap.Make (Level)
  include M

  let lunion l r =
    union (fun _k l _r -> Some l) l r

  let subst_union l r =
    union (fun _k l r ->
      match l, r with
      | Some _, _ -> Some l
      | None, None -> Some l
      | _, _ -> Some r) l r

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

    (* Hashing of expressions *)
    module ExprHash = 
    struct
      type t = Level.t * int
      type u = Level.t -> Level.t
      let hashcons hdir (b,n as x) = 
	let b' = hdir b in 
	  if b' == b then x else (b',n)
      let eq l1 l2 =
        l1 == l2 || 
        match l1,l2 with
	| (b,n), (b',n') -> b == b' && n == n'

      let hash (x, n) = n + Level.hash x

    end

    module H = Hashcons.Make(ExprHash)

    let hcons =
      Hashcons.simple_hcons H.generate H.hcons Level.hcons

    let make l = (l, 0)

    let compare u v =
      if u == v then 0
      else 
	let (x, n) = u and (x', n') = v in
	  if Int.equal n n' then Level.compare x x'
	  else n - n'

    let sprop = hcons (Level.sprop, 0)
    let prop = hcons (Level.prop, 0)
    let set = hcons (Level.set, 0)
    let type1 = hcons (Level.set, 1)

    let is_small = function
      | (l,0) -> Level.is_small l
      | _ -> false

    let equal x y = x == y ||
      (let (u,n) = x and (v,n') = y in
	 Int.equal n n' && Level.equal u v)

    let hash = ExprHash.hash

    let leq (u,n) (v,n') =
      let cmp = Level.compare u v in
	if Int.equal cmp 0 then n <= n'
	else if n <= n' then 
          (Level.is_prop u && not (Level.is_sprop v))
	else false

    let successor (u,n) =
      if Level.is_small u then type1
      else (u, n + 1)

    let addn k (u,n as x) = 
      if k = 0 then x 
      else if Level.is_small u then
	(Level.set,n+k)
      else (u,n+k)

    type super_result =
	SuperSame of bool
        (* The level expressions are in cumulativity relation. boolean
           indicates if left is smaller than right?  *)
      | SuperDiff of int
        (* The level expressions are unrelated, the comparison result
           is canonical *)

    (** [super u v] compares two level expressions,
       returning [SuperSame] if they refer to the same level at potentially different
       increments or [SuperDiff] if they are different. The booleans indicate if the
       left expression is "smaller" than the right one in both cases. *)
    let super (u,n) (v,n') =
      let cmp = Level.compare u v in
        if Int.equal cmp 0 then SuperSame (n < n')
	else
          let open RawLevel in
          match Level.data u, n, Level.data v, n' with
          | SProp, _, SProp, _ | Prop, _, Prop, _ -> SuperSame (n < n')
          | SProp, 0, Prop, 0 -> SuperSame true
          | Prop, 0, SProp, 0 -> SuperSame false
          | (SProp | Prop), 0, _, _ -> SuperSame true
          | _, _, (SProp | Prop), 0 -> SuperSame false

          | _, _, _, _ -> SuperDiff cmp

    let to_string (v, n) =
      if Int.equal n 0 then Level.to_string v
      else Level.to_string v ^ "+" ^ string_of_int n

    let pr x = str(to_string x)

    let pr_with f (v, n) = 
      if Int.equal n 0 then f v
      else f v ++ str"+" ++ int n

    let is_level = function
      | (_v, 0) -> true
      | _ -> false

    let level = function
      | (v,0) -> Some v
      | _ -> None
	
    let get_level (v,_n) = v

    let map f (v, n as x) = 
      let v' = f v in 
	if v' == v then x
	else if Level.is_prop v' && n != 0 then
	  (Level.set, n)
	else (v', n)

  end

  type t = Expr.t list

  let tip l = [l]
  let cons x l = x :: l

  let rec hash = function
  | [] -> 0
  | e :: l -> Hashset.Combine.combinesmall (Expr.ExprHash.hash e) (hash l)

  let equal x y = x == y || List.equal Expr.equal x y

  let compare x y = if x == y then 0 else List.compare Expr.compare x y

  module Huniv = Hashcons.Hlist(Expr)

  let hcons = Hashcons.recursive_hcons Huniv.generate Huniv.hcons Expr.hcons

  let make l = tip (Expr.make l)
  let tip x = tip x

  let pr l = match l with
    | [u] -> Expr.pr u
    | _ -> 
      str "max(" ++ hov 0
	(prlist_with_sep pr_comma Expr.pr l) ++
        str ")"

  let pr_with f l = match l with
    | [u] -> Expr.pr_with f u
    | _ -> 
      str "max(" ++ hov 0
	(prlist_with_sep pr_comma (Expr.pr_with f) l) ++
        str ")"

  let is_level l = match l with
    | [l] -> Expr.is_level l
    | _ -> false

  let rec is_levels l = match l with
    | l :: r -> Expr.is_level l && is_levels r
    | [] -> true

  let level l = match l with
    | [l] -> Expr.level l
    | _ -> None

  let levels l = 
    List.fold_left (fun acc x -> LSet.add (Expr.get_level x) acc) LSet.empty l

  let is_small u = 
    match u with
    | [l] -> Expr.is_small l
    | _ -> false

  let sprop = tip Expr.sprop

  (* The lower predicative level of the hierarchy that contains (impredicative)
     Prop and singleton inductive types *)
  let type0m = tip Expr.prop

  (* The level of sets *)
  let type0 = tip Expr.set

  (* When typing [Prop] and [Set], there is no constraint on the level,
     hence the definition of [type1_univ], the type of [Prop] *)    
  let type1 = tip Expr.type1

  let is_sprop x = equal sprop x
  let is_type0m x = equal type0m x
  let is_type0 x = equal type0 x

  (* Returns the formal universe that lies just above the universe variable u.
     Used to type the sort u. *)
  let super l = 
    if is_small l then type1
    else
      List.Smart.map (fun x -> Expr.successor x) l

  let addn n l =
    List.Smart.map (fun x -> Expr.addn n x) l

  let rec merge_univs l1 l2 =
    match l1, l2 with
    | [], _ -> l2
    | _, [] -> l1
    | h1 :: t1, h2 :: t2 ->
       let open Expr in
       (match super h1 h2 with
	| SuperSame true (* h1 < h2 *) -> merge_univs t1 l2
	| SuperSame false -> merge_univs l1 t2
	| SuperDiff c ->
           if c <= 0 (* h1 < h2 is name order *)
	   then cons h1 (merge_univs t1 l2)
	   else cons h2 (merge_univs l1 t2))

  let sort u =
    let rec aux a l = 
      match l with
      | b :: l' ->
	let open Expr in
        (match super a b with
	 | SuperSame false -> aux a l'
	 | SuperSame true -> l
	 | SuperDiff c ->
	    if c <= 0 then cons a l
	    else cons b (aux a l'))
      | [] -> cons a l
    in 
      List.fold_right (fun a acc -> aux a acc) u []

  (* Returns the formal universe that is greater than the universes u and v.
     Used to type the products. *)
  let sup x y = merge_univs x y

  let empty = []

  let exists = List.exists

  let for_all = List.for_all

  let smart_map = List.Smart.map

  let map = List.map
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


type constraint_type = AcyclicGraph.constraint_type = Lt | Le | Eq

type explanation = (constraint_type * Level.t) list

let constraint_type_ord c1 c2 = match c1, c2 with
| Lt, Lt -> 0
| Lt, _ -> -1
| Le, Lt -> 1
| Le, Le -> 0
| Le, Eq -> -1
| Eq, Eq -> 0
| Eq, _ -> 1

(* Universe inconsistency: error raised when trying to enforce a relation
   that would create a cycle in the graph of universes. *)

type univ_inconsistency = constraint_type * universe * universe * explanation Lazy.t option

exception UniverseInconsistency of univ_inconsistency

let error_inconsistency o u v p =
  raise (UniverseInconsistency (o,make u,make v,p))

(* Constraints and sets of constraints. *)    

type univ_constraint = Level.t * constraint_type * Level.t

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
    v 0 (prlist_with_sep spc (fun (u1,op,u2) ->
      hov 0 (prl u1 ++ pr_constraint_type op ++ prl u2))
       (elements c))

end

let empty_constraint = Constraint.empty
let union_constraint = Constraint.union
let eq_constraint = Constraint.equal

type constraints = Constraint.t

module Hconstraint =
  Hashcons.Make(
    struct
      type t = univ_constraint
      type u = universe_level -> universe_level
      let hashcons hul (l1,k,l2) = (hul l1, k, hul l2)
      let eq (l1,k,l2) (l1',k',l2') =
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
      let eq s s' =
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
    | _ -> anomaly (Pp.str "A universe comparison can only happen between variables.")

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
	else anomaly (Pp.str"Unable to handle arbitrary u+k <= v constraints.")
      else if j = 0 then
	Constraint.add (x,Le,y) c
      else (* j >= 1 *) (* m = n + k, u <= v+k *)
	if Level.equal x y then c (* u <= u+k, trivial *)
	else if Level.is_small x then c (* Prop,Set <= u+S k, trivial *)
        else Constraint.add (x,Le,y) c (* u <= v implies u <= v+k *)
	  
let check_univ_leq_one u v = Universe.exists (Expr.leq u) v

let check_univ_leq u v = 
  Universe.for_all (fun u -> check_univ_leq_one u v) u

let enforce_leq u v c =
  match is_sprop u, is_sprop v with
  | true, true -> c
  | true, false | false, true ->
    raise (UniverseInconsistency (Le, u, v, None))
  | false, false ->
    List.fold_left (fun c v -> (List.fold_left (fun c u -> constraint_add_leq u v c) c u)) c v

let enforce_leq u v c =
  if check_univ_leq u v then c
  else enforce_leq u v c

let enforce_leq_level u v c =
  if Level.equal u v then c else Constraint.add (u,Le,v) c

(* Miscellaneous functions to remove or test local univ assumed to
   occur in a universe *)

let univ_level_mem u v =
  List.exists (fun (l, n) -> Int.equal n 0 && Level.equal u l) v

let univ_level_rem u v min = 
  match Universe.level v with
  | Some u' -> if Level.equal u u' then min else v
  | None -> List.filter (fun (l, n) -> not (Int.equal n 0 && Level.equal u l)) v

(* Is u mentioned in v (or equals to v) ? *)


(**********************************************************************)
(** Universe polymorphism                                             *)
(**********************************************************************)

(** A universe level substitution, note that no algebraic universes are
    involved *)

type universe_level_subst = universe_level universe_map

(** A full substitution might involve algebraic universes *)
type universe_subst = universe universe_map

module Variance =
struct
  (** A universe position in the instance given to a cumulative
     inductive can be the following. Note there is no Contravariant
     case because [forall x : A, B <= forall x : A', B'] requires [A =
     A'] as opposed to [A' <= A]. *)
  type t = Irrelevant | Covariant | Invariant

  let sup x y =
    match x, y with
    | Irrelevant, s | s, Irrelevant -> s
    | Invariant, _ | _, Invariant -> Invariant
    | Covariant, Covariant -> Covariant

  let check_subtype x y = match x, y with
  | (Irrelevant | Covariant | Invariant), Irrelevant -> true
  | Irrelevant, Covariant -> false
  | (Covariant | Invariant), Covariant -> true
  | (Irrelevant | Covariant), Invariant -> false
  | Invariant, Invariant -> true

  let pr = function
    | Irrelevant -> str "*"
    | Covariant -> str "+"
    | Invariant -> str "="

  let leq_constraint csts variance u u' =
    match variance with
    | Irrelevant -> csts
    | Covariant -> enforce_leq_level u u' csts
    | Invariant -> enforce_eq_level u u' csts

  let eq_constraint csts variance u u' =
    match variance with
    | Irrelevant -> csts
    | Covariant | Invariant -> enforce_eq_level u u' csts

  let leq_constraints variance u u' csts =
    let len = Array.length u in
    assert (len = Array.length u' && len = Array.length variance);
    Array.fold_left3 leq_constraint csts variance u u'

  let eq_constraints variance u u' csts =
    let len = Array.length u in
    assert (len = Array.length u' && len = Array.length variance);
    Array.fold_left3 eq_constraint csts variance u u'
end

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
    
    val pr : (Level.t -> Pp.t) -> ?variance:Variance.t array -> t -> Pp.t
    val levels : t -> LSet.t
end = 
struct
  type t = Level.t array

  let empty : t = [||]

  module HInstancestruct =
  struct
    type nonrec t = t
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

    let eq t1 t2 =
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

  let of_array a =
    assert(Array.for_all (fun x -> not (Level.is_prop x || Level.is_sprop x)) a);
    a

  let to_array a = a

  let length a = Array.length a

  let subst_fn fn t = 
    let t' = CArray.Smart.map fn t in
      if t' == t then t else of_array t'

  let levels x = LSet.of_array x

  let pr prl ?variance =
    let ppu i u =
      let v = Option.map (fun v -> v.(i)) variance in
      pr_opt_no_spc Variance.pr v ++ prl u
    in
    prvecti_with_sep spc ppu

  let equal t u = 
    t == u ||
      (Array.is_empty t && Array.is_empty u) ||
      (CArray.for_all2 Level.equal t u 
	 (* Necessary as universe instances might come from different modules and 
	    unmarshalling doesn't preserve sharing *))

end

let enforce_eq_instances x y = 
  let ax = Instance.to_array x and ay = Instance.to_array y in
    if Array.length ax != Array.length ay then
      anomaly (Pp.(++) (Pp.str "Invalid argument: enforce_eq_instances called with")
		 (Pp.str " instances of different lengths."));
    CArray.fold_right2 enforce_eq_level ax ay

let enforce_eq_variance_instances = Variance.eq_constraints
let enforce_leq_variance_instances = Variance.leq_constraints

let subst_instance_level s l =
  match l.Level.data with
  | Level.Var n -> s.(n) 
  | _ -> l

let subst_instance_instance s i = 
  Array.Smart.map (fun l -> subst_instance_level s l) i

let subst_instance_universe s u =
  let f x = Universe.Expr.map (fun u -> subst_instance_level s u) x in
  let u' = Universe.smart_map f u in
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

type 'a puniverses = 'a * Instance.t
let out_punivs (x, _y) = x
let in_punivs x = (x, Instance.empty)
let eq_puniverses f (x, u) (y, u') =
  f x y && Instance.equal u u'

(** A context of universe levels with universe constraints,
    representing local universe variables and constraints *)

module UContext =
struct
  type t = Instance.t constrained

  let make x = x

  (** Universe contexts (variables as a list) *)
  let empty = (Instance.empty, Constraint.empty)
  let is_empty (univs, cst) = Instance.is_empty univs && Constraint.is_empty cst

  let pr prl ?variance (univs, cst as ctx) =
    if is_empty ctx then mt() else
      h 0 (Instance.pr prl ?variance univs ++ str " |= ") ++ h 0 (v 0 (Constraint.pr prl cst))

  let hcons (univs, cst) =
    (Instance.hcons univs, hcons_constraints cst)

  let instance (univs, _cst) = univs
  let constraints (_univs, cst) = cst

  let union (univs, cst) (univs', cst') =
    Instance.append univs univs', Constraint.union cst cst'

  let dest x = x

  let size (x,_) = Instance.length x

end

type universe_context = UContext.t
let hcons_universe_context = UContext.hcons

module AUContext =
struct
  type t = Names.Name.t array constrained

  let repr (inst, cst) =
    (Array.init (Array.length inst) (fun i -> Level.var i), cst)

  let pr f ?variance ctx = UContext.pr f ?variance (repr ctx)

  let instantiate inst (u, cst) =
    assert (Array.length u = Array.length inst);
    subst_instance_constraints inst cst

  let names (nas, _) = nas

  let hcons (univs, cst) =
    (Array.map Names.Name.hcons univs, hcons_constraints cst)

  let empty = ([||], Constraint.empty)

  let is_empty (nas, cst) = Array.is_empty nas && Constraint.is_empty cst

  let union (nas, cst) (nas', cst') = (Array.append nas nas', Constraint.union cst cst')

  let size (nas, _) = Array.length nas

end

type 'a univ_abstracted = {
  univ_abstracted_value : 'a;
  univ_abstracted_binder : AUContext.t;
}

let map_univ_abstracted f {univ_abstracted_value;univ_abstracted_binder} =
  let univ_abstracted_value = f univ_abstracted_value in
  {univ_abstracted_value;univ_abstracted_binder}

let hcons_abstract_universe_context = AUContext.hcons

(** A set of universes with universe constraints.
    We linearize the set to a list after typechecking. 
    Beware, representation could change.
*)

module ContextSet =
struct
  type t = universe_set constrained

  let empty = (LSet.empty, Constraint.empty)
  let is_empty (univs, cst) = LSet.is_empty univs && Constraint.is_empty cst

  let equal (univs, cst as x) (univs', cst' as y) =
    x == y || (LSet.equal univs univs' && Constraint.equal cst cst')
									
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
    Array.sort Level.compare a; a

  let to_context (ctx, cst) =
    (Instance.of_array (sort_levels (Array.of_list (LSet.elements ctx))), cst)

  let of_context (ctx, cst) =
    (Instance.levels ctx, cst)

  let pr prl (univs, cst as ctx) =
    if is_empty ctx then mt() else
      h 0 (LSet.pr prl univs ++ str " |= ") ++ h 0 (v 0 (Constraint.pr prl cst))

  let constraints (_univs, cst) = cst
  let levels (univs, _cst) = univs

  let size (univs,_) = LSet.cardinal univs
end

type universe_context_set = ContextSet.t

(** A value in a universe context (resp. context set). *)
type 'a in_universe_context = 'a * universe_context
type 'a in_universe_context_set = 'a * universe_context_set

let extend_in_context_set (a, ctx) ctx' =
  (a, ContextSet.union ctx ctx')

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
  let u' = Universe.smart_map f u in
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

let subst_univs_level_abstract_universe_context subst (inst, csts) =
  inst, subst_univs_level_constraints subst csts

(** With level to universe substitutions. *)
type universe_subst_fn = universe_level -> universe

let make_subst subst = fun l -> LMap.find l subst

let subst_univs_expr_opt fn (l,n) =
  Universe.addn n (fn l)

let subst_univs_universe fn ul =
  let subst, nosubst = 
    List.fold_right (fun u (subst,nosubst) -> 
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
	List.fold_left (fun acc u -> Universe.merge_univs acc (Universe.tip u))
	  substs nosubst

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

let make_abstract_instance (ctx, _) = 
  Array.init (Array.length ctx) (fun i -> Level.var i)

let abstract_universes nas ctx =
  let instance = UContext.instance ctx in
  let () = assert (Int.equal (Array.length nas) (Instance.length instance)) in
  let subst = make_instance_subst instance in
  let cstrs = subst_univs_level_constraints subst 
      (UContext.constraints ctx)
  in
  let ctx = (nas, cstrs) in
  instance, ctx

let rec compact_univ s vars i u =
  match u with
  | [] -> (s, List.rev vars)
  | (lvl, _) :: u ->
    match Level.var_index lvl with
    | Some k when not (LMap.mem lvl s) ->
      let lvl' = Level.var i in
      compact_univ (LMap.add lvl lvl' s) (k :: vars) (i+1) u
    | _ -> compact_univ s vars i u

let compact_univ u =
  let (s, s') = compact_univ LMap.empty [] 0 u in
  (subst_univs_level_universe s u, s')

(** Pretty-printing *)

let pr_constraints prl = Constraint.pr prl

let pr_universe_context = UContext.pr

let pr_abstract_universe_context = AUContext.pr

let pr_universe_context_set = ContextSet.pr

let pr_universe_subst = 
  LMap.pr (fun u -> str" := " ++ Universe.pr u ++ spc ())

let pr_universe_level_subst = 
  LMap.pr (fun u -> str" := " ++ Level.pr u ++ spc ())

module Huniverse_set = 
  Hashcons.Make(
    struct
      type t = universe_set
      type u = universe_level -> universe_level
      let hashcons huc s =
	LSet.fold (fun x -> LSet.add (huc x)) s LSet.empty
      let eq s s' =
	LSet.equal s s'
      let hash = Hashtbl.hash
    end)

let hcons_universe_set = 
  Hashcons.simple_hcons Huniverse_set.generate Huniverse_set.hcons Level.hcons

let hcons_universe_context_set (v, c) = 
  (hcons_universe_set v, hcons_constraints c)

let hcons_univ x = Universe.hcons x

let explain_universe_inconsistency prl (o,u,v,p : univ_inconsistency) =
  let pr_uni = Universe.pr_with prl in
  let pr_rel = function
    | Eq -> str"=" | Lt -> str"<" | Le -> str"<=" 
  in
  let reason = match p with
    | None -> mt()
    | Some p ->
      let p = Lazy.force p in
      if p = [] then mt ()
      else
        str " because" ++ spc() ++ pr_uni v ++
        prlist (fun (r,v) -> spc() ++ pr_rel r ++ str" " ++ prl v)
          p ++
        (if Universe.equal (Universe.make (snd (List.last p))) u then mt() else
           (spc() ++ str "= " ++ pr_uni u))
  in
    str "Cannot enforce" ++ spc() ++ pr_uni u ++ spc() ++
      pr_rel o ++ spc() ++ pr_uni v ++ reason
