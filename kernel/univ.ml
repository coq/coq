(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

module UGlobal = struct
  open Names

  type t = {
    library : DirPath.t;
    process : string;
    uid : int;
  }

  let make library process uid = { library; process; uid }

  let repr x = (x.library, x.process, x.uid)

  let equal u1 u2 =
    Int.equal u1.uid u2.uid &&
    DirPath.equal u1.library u2.library &&
    String.equal u1.process u2.process

  let hash u = Hashset.Combine.combine3 u.uid (String.hash u.process) (DirPath.hash u.library)

  let compare u1 u2 =
    let c = Int.compare u1.uid u2.uid in
    if c <> 0 then c
    else
      let c = DirPath.compare u1.library u2.library in
      if c <> 0 then c
      else String.compare u1.process u2.process

  let to_string { library = d; process = s; uid = n } =
    DirPath.to_string d ^
    (if CString.is_empty s then "" else "." ^ s) ^
    "." ^ string_of_int n

end

module RawLevel =
struct

  type t =
    | Set
    | Level of UGlobal.t
    | Var of int

  (* Hash-consing *)

  let equal x y =
    x == y ||
      match x, y with
      | Set, Set -> true
      | Level l, Level l' -> UGlobal.equal l l'
      | Var n, Var n' -> Int.equal n n'
      | _ -> false

  let compare u v =
    match u, v with
    | Set, Set -> 0
    | Set, _ -> -1
    | _, Set -> 1
    | Level l1, Level l2 -> UGlobal.compare l1 l2
    | Level _, _ -> -1
    | _, Level _ -> 1
    | Var n, Var m -> Int.compare n m

  let hequal x y =
    x == y ||
      match x, y with
      | Set, Set -> true
      | UGlobal.(Level { library = d; process = s; uid = n }, Level  { library = d'; process = s'; uid = n' }) ->
        n == n' && s==s' && d == d'
      | Var n, Var n' -> n == n'
      | _ -> false

  let hcons = function
    | Set as x -> x
    | UGlobal.(Level { library = d; process = s; uid = n }) as x ->
      let s' = CString.hcons s in
      let d' = Names.DirPath.hcons d in
        if s' == s && d' == d then x else Level (UGlobal.make d' s' n)
    | Var _n as x -> x

  open Hashset.Combine

  let hash = function
    | Set -> combinesmall 1 2
    | Var n -> combinesmall 2 n
    | Level l -> combinesmall 3 (UGlobal.hash l)

end

module Level = struct

  type raw_level = RawLevel.t =
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

  let is_small x =
    match data x with
    | Level _ -> false
    | Var _ -> false
    | Set -> true

  let is_set x =
    match data x with
    | Set -> true
    | _ -> false

  let compare u v =
    if u == v then 0
    else RawLevel.compare (data u) (data v)

  let to_string x =
    match data x with
    | Set -> "Set"
    | Level l -> UGlobal.to_string l
    | Var n -> "Var(" ^ string_of_int n ^ ")"

  let raw_pr u = str (to_string u)

  let pr = raw_pr

  let vars = Array.init 20 (fun i -> make (Var i))

  let var n =
    if n < 20 then vars.(n) else make (Var n)

  let var_index u =
    match data u with
    | Var n -> Some n | _ -> None

  let make qid = make (Level qid)

  let name u =
    match data u with
    | Level l -> Some l
    | _ -> None

  (** Level maps *)

  module Map = struct

    module Self = struct type nonrec t = t let hash = hash let compare = compare end
    module M = HMap.Make (Self)
    include M

    let lunion l r =
      union (fun _k l _r -> Some l) l r

    let diff ext orig =
      fold (fun u v acc ->
        if mem u orig then acc
        else add u v acc)
        ext empty

    let pr prl f m =
      h (prlist_with_sep fnl (fun (u, v) ->
        prl u ++ f v) (bindings m))

  end

  module Set = struct
    include Map.Set

    let pr prl s =
      hov 1 (str"{" ++ prlist_with_sep spc prl (elements s) ++ str"}")

  end

end

type universe_level = Level.t

type universe_set = Level.Set.t

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
        let c = Int.compare n n' in
        if Int.equal 0 c then  Level.compare x x'
        else c

    let set = hcons (Level.set, 0)
    let type1 = hcons (Level.set, 1)

    let is_small = function
      | (l,0) -> Level.is_small l
      | _ -> false

    let equal x y = x == y ||
      (let (u,n) = x and (v,n') = y in
         Int.equal n n' && Level.equal u v)

    let hash = ExprHash.hash

    let successor (u,n as e) =
      if is_small e then type1
      else (u, n + 1)

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
        else (v', n)

  end

  type t = Expr.t list

  let tip l = [l]

  let rec hash = function
  | [] -> 0
  | e :: l -> Hashset.Combine.combinesmall (Expr.ExprHash.hash e) (hash l)

  let equal x y = x == y || List.equal Expr.equal x y

  let compare x y = if x == y then 0 else List.compare Expr.compare x y

  module Huniv = Hashcons.Hlist(Expr)

  let hcons = Hashcons.simple_hcons Huniv.generate Huniv.hcons Expr.hcons

  module Self = struct type nonrec t = t let compare = compare end
  module Map = CMap.Make(Self)
  module Set = CSet.Make(Self)

  let make l = tip (Expr.make l)
  let maken l n = tip (l, n)
  let tip x = tip x

  let pr f l = match l with
    | [u] -> Expr.pr_with f u
    | _ ->
      str "max(" ++ hov 0
        (prlist_with_sep pr_comma (Expr.pr_with f) l) ++
        str ")"

  let raw_pr l = pr Level.raw_pr l

  let is_level l = match l with
    | [l] -> Expr.is_level l
    | _ -> false

  let rec is_levels l = match l with
    | l :: r -> Expr.is_level l && is_levels r
    | [] -> true

  let level l = match l with
    | [l] -> Expr.level l
    | _ -> None

  let levels ?(init=Level.Set.empty) l =
    let fold acc x =
      let l = Expr.get_level x in
      Level.Set.add l acc
    in
    List.fold_left fold init l

  let is_small u =
    match u with
    | [l] -> Expr.is_small l
    | _ -> false

  (* The level of sets *)
  let type0 = tip Expr.set

  (* When typing [Prop] and [Set], there is no constraint on the level,
     hence the definition of [type1_univ], the type of [Prop] *)
  let type1 = tip Expr.type1

  let is_type0 x = equal type0 x

  (* Returns the formal universe that lies just above the universe variable u.
     Used to type the sort u. *)
  let super l =
    if is_small l then type1
    else
      List.Smart.map (fun x -> Expr.successor x) l

  (* Returns the formal universe that is greater than the universes u and v.
     Used to type the products. *)
  let rec sup (l1:t) (l2:t) : t =
    match l1, l2 with
    | [], _ -> l2
    | _, [] -> l1
    | h1 :: t1, h2 :: t2 ->
      let cmp = Level.compare (fst h1) (fst h2) in
      if Int.equal cmp 0 then
        if (snd h1 : int) < snd h2
        then sup t1 l2
        else sup l1 t2
      else if cmp <= 0
      then h1 :: (sup t1 l2)
      else h2 :: (sup l1 t2)

  let exists = List.exists

  let for_all = List.for_all
  let repr x : t = x
  let unrepr l =
    assert (not (List.is_empty l));
    List.fold_right (fun a acc -> sup [a] acc) l []
end

type constraint_type = AcyclicGraph.constraint_type = Lt | Le | Eq

let constraint_type_ord c1 c2 = match c1, c2 with
| Lt, Lt -> 0
| Lt, _ -> -1
| Le, Lt -> 1
| Le, Le -> 0
| Le, Eq -> -1
| Eq, Eq -> 0
| Eq, _ -> 1

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

module Constraints =
struct
  module S = Set.Make(UConstraintOrd)
  include S

  let pr prl c =
    v 0 (prlist_with_sep spc (fun (u1,op,u2) ->
      hov 0 (prl u1 ++ pr_constraint_type op ++ prl u2))
       (elements c))

end

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
      type t = Constraints.t
      type u = univ_constraint -> univ_constraint
      let hashcons huc s =
        Constraints.fold (fun x -> Constraints.add (huc x)) s Constraints.empty
      let eq s s' =
        List.for_all2eq (==)
          (Constraints.elements s)
          (Constraints.elements s')
      let hash = Hashtbl.hash
    end)

let hcons_constraint = Hashcons.simple_hcons Hconstraint.generate Hconstraint.hcons Level.hcons
let hcons_constraints = Hashcons.simple_hcons Hconstraints.generate Hconstraints.hcons hcons_constraint


(** A value with universe constraints. *)
type 'a constrained = 'a * Constraints.t

let constraints_of (_, cst) = cst

(** Constraints functions. *)

type 'a constraint_function = 'a -> 'a -> Constraints.t -> Constraints.t

let enforce_eq_level u v c =
  (* We discard trivial constraints like u=u *)
  if Level.equal u v then c
  else Constraints.add (u,Eq,v) c

let enforce_leq_level u v c =
  if Level.equal u v then c else Constraints.add (u,Le,v) c

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

type universe_level_subst = universe_level Level.Map.t

(** A set of universes with universe constraints.
    We linearize the set to a list after typechecking.
    Beware, representation could change.
*)

module ContextSet =
struct
  type t = universe_set constrained

  let empty = (Level.Set.empty, Constraints.empty)
  let is_empty (univs, cst) = Level.Set.is_empty univs && Constraints.is_empty cst

  let equal (univs, cst as x) (univs', cst' as y) =
    x == y || (Level.Set.equal univs univs' && Constraints.equal cst cst')

  let of_set s = (s, Constraints.empty)
  let singleton l = of_set (Level.Set.singleton l)

  let union (univs, cst as x) (univs', cst' as y) =
    if x == y then x
    else Level.Set.union univs univs', Constraints.union cst cst'

  let append (univs, cst) (univs', cst') =
    let univs = Level.Set.fold Level.Set.add univs univs' in
    let cst = Constraints.fold Constraints.add cst cst' in
    (univs, cst)

  let diff (univs, cst) (univs', cst') =
    Level.Set.diff univs univs', Constraints.diff cst cst'

  let add_universe u (univs, cst) =
    Level.Set.add u univs, cst

  let add_constraints cst' (univs, cst) =
    univs, Constraints.union cst cst'

  let pr prl (univs, cst as ctx) =
    if is_empty ctx then mt() else
      hov 0 (h (Level.Set.pr prl univs ++ str " |=") ++ brk(1,2) ++ h (Constraints.pr prl cst))

  let constraints (_univs, cst) = cst
  let levels (univs, _cst) = univs

  let size (univs,_) = Level.Set.cardinal univs
end

type universe_context_set = ContextSet.t

(** A value in a universe context (resp. context set). *)
type 'a in_universe_context_set = 'a * universe_context_set

(** Substitutions. *)

let empty_level_subst = Level.Map.empty
let is_empty_level_subst = Level.Map.is_empty

(** Substitution functions *)

(** With level to level substitutions. *)
let subst_univs_level_level subst l =
  try Level.Map.find l subst
  with Not_found -> l

let subst_univs_level_universe subst u =
  let f x = Universe.Expr.map (fun u -> subst_univs_level_level subst u) x in
  let u' = List.Smart.map f u in
    if u == u' then u
    else Universe.unrepr u'

let subst_univs_level_constraint subst (u,d,v) =
  let u' = subst_univs_level_level subst u
  and v' = subst_univs_level_level subst v in
    if d != Lt && Level.equal u' v' then None
    else Some (u',d,v')

let subst_univs_level_constraints subst csts =
  Constraints.fold
    (fun c -> Option.fold_right Constraints.add (subst_univs_level_constraint subst c))
    csts Constraints.empty

(** Pretty-printing *)

let pr_universe_context_set = ContextSet.pr

let pr_universe_level_subst prl =
  Level.Map.pr prl (fun u -> str" := " ++ prl u ++ spc ())

module Huniverse_set =
  Hashcons.Make(
    struct
      type t = universe_set
      type u = universe_level -> universe_level
      let hashcons huc s =
        Level.Set.fold (fun x -> Level.Set.add (huc x)) s Level.Set.empty
      let eq s s' =
        Level.Set.equal s s'
      let hash = Hashtbl.hash
    end)

let hcons_universe_set =
  Hashcons.simple_hcons Huniverse_set.generate Huniverse_set.hcons Level.hcons

let hcons_universe_context_set (v, c) =
  (hcons_universe_set v, hcons_constraints c)

let hcons_univ x = Universe.hcons x
