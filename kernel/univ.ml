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
    | Zero
    | Level of UGlobal.t
    | Var of int

  (* Hash-consing *)

  let equal x y =
    x == y ||
      match x, y with
      | Zero, Zero -> true
      | Level l, Level l' -> UGlobal.equal l l'
      | Var n, Var n' -> Int.equal n n'
      | _ -> false

  let compare u v =
    match u, v with
    | Zero, Zero -> 0
    | Zero, _ -> -1
    | _, Zero -> 1
    | Level l1, Level l2 -> UGlobal.compare l1 l2
    | Level _, _ -> -1
    | _, Level _ -> 1
    | Var n, Var m -> Int.compare n m

  let hequal x y =
    x == y ||
      match x, y with
      | Zero, Zero -> true
      | UGlobal.(Level { library = d; process = s; uid = n }, Level  { library = d'; process = s'; uid = n' }) ->
        n == n' && s==s' && d == d'
      | Var n, Var n' -> n == n'
      | _ -> false

  open Hashset.Combine

  let hcons = function
    | Zero as x -> combinesmall 1 2, x
    | UGlobal.(Level { library = d; process = s; uid = n }) as x ->
      let hs, s' = CString.hcons s in
      let hd, d' = Names.DirPath.hcons d in
      let x = if s' == s && d' == d then x else Level (UGlobal.make d' s' n) in
      combinesmall 3 (combine3 n hs hd), x
    | Var n as x -> combinesmall 2 n, x

  let hash = function
    | Zero -> combinesmall 1 2
    | Var n -> combinesmall 2 n
    | Level l -> combinesmall 3 (UGlobal.hash l)

end

module Level = struct

  type raw_level = RawLevel.t =
  | Zero
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
    let eq x y = x.hash == y.hash && RawLevel.hequal x.data y.data
    let hashcons x =
      let _, data' = RawLevel.hcons x.data in
      x.hash, if x.data == data' then x else { x with data = data' }
  end

  let hcons =
    let module H = Hashcons.Make(Self) in
    Hashcons.simple_hcons H.generate H.hcons ()

  let make l = snd @@ hcons { hash = RawLevel.hash l; data = l }

  let zero = make Zero
  let set = zero

  let is_small x =
    match data x with
    | Level _ -> false
    | Var _ -> false
    | Zero -> true

  let is_zero x =
    match data x with
    | Zero -> true
    | _ -> false
  let is_set = is_zero

  let compare u v =
    if u == v then 0
    else RawLevel.compare (data u) (data v)

  let to_string x =
    match data x with
    | Zero -> "0"
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


    module Huniverse_set =
      Hashcons.Make(
      struct
        type nonrec t = t
        let hashcons s =
          fold (fun x (h,acc) ->
              let hx, x = hcons x in
              Hashset.Combine.combine h hx, add x acc)
            s
            (0,empty)
        let eq s s' = Map.Set.equal s s'
      end)

    let hcons = Hashcons.simple_hcons Huniverse_set.generate Huniverse_set.hcons ()
  end

end

(* An algebraic universe [universe] is either a level expression
   [LevelExpr.t] or a formal max() universe known to be greater than some
   level expressions.  *)

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
      let hashcons (b,n as x) =
        let hb, b' = Level.hcons b in
        n + hb, if b' == b then x else (b',n)
      let eq l1 l2 =
        l1 == l2 ||
        match l1,l2 with
        | (b,n), (b',n') -> b == b' && n == n'

      let hash (x, n) = n + Level.hash x

    end

    module H = Hashcons.Make(ExprHash)

    let hcons =
      Hashcons.simple_hcons H.generate H.hcons ()

    let make l = (l, 0)

    let compare u v =
      if u == v then 0
      else
        let (x, n) = u and (x', n') = v in
        let c = Int.compare n n' in
        if Int.equal 0 c then  Level.compare x x'
        else c

    let _, set = hcons (Level.set, 0)
    let _, type1 = hcons (Level.set, 1)

    let is_small = function
      | (l,0) -> Level.is_small l
      | _ -> false

    let equal x y = x == y ||
      (let (u,n) = x and (v,n') = y in
         Int.equal n n' && Level.equal u v)

    let successor (u,n as e) =
      if is_small e then type1
      else (u, n + 1)

    let addn (u, n as e) k =
      if Int.equal k 0 then e
      else (u, k + n)

    let pr f (l, n) =
      if Int.equal n 0 then f l
      else match Level.data l with
      | RawLevel.Zero -> int n
      | _ -> f l ++ str"+" ++ int n

    let is_level = function
      | (_v, 0) -> true
      | _ -> false

    let level = function
      | (v,0) -> Some v
      | _ -> None

    let get_level (v,_n) = v

    let hash = ExprHash.hash

    module Self = struct type nonrec t = t let compare = compare end
    module Map = CMap.Make(Self)
    module Set = CSet.Make(Self)
  end

  type t = Expr.t list

  let tip l = [l]

  let rec hash = function
  | [] -> 0
  | e :: l  -> Hashset.Combine.combinesmall (Expr.ExprHash.hash e) (hash l)

  let equal x y = x == y || List.equal Expr.equal x y

  let compare x y = if x == y then 0 else List.compare Expr.compare x y

  module Huniv = Hashcons.Hlist(Expr)

  let hcons = Hashcons.simple_hcons Huniv.generate Huniv.hcons ()

  module Self = struct type nonrec t = t let compare = compare end
  module Map = CMap.Make(Self)
  module Set = CSet.Make(Self)

  let make l = tip (Expr.make l)
  let maken l n = tip (l, n)

  let of_expr l = tip l

  let of_list x = x

  let pr f l = match l with
    | [u] -> Expr.pr f u
    | _ ->
      str "max(" ++ hov 0
        (prlist_with_sep pr_comma (Expr.pr f) l) ++
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

  let mem l u =
    List.exists (fun (l', _) -> Level.equal l l') u

  let is_small u =
    match u with
    | [l] -> Expr.is_small l
    | _ -> false

  (* The level of sets *)
  let type0 = tip Expr.set

  (* When typing [Prop] and [Set], there is no constraint on the level,
     hence the definition of [type1_univ], the type of [Prop] *)
  let type1 = tip Expr.type1

  let var x = tip (Level.var x, 0)

  let is_type0 x = equal type0 x

  let is_typen n = function
    [(l, k)] -> Level.is_zero l && Int.equal k n
    | _ -> false

  (* Returns the formal universe that lies just above the universe variable u.
     Used to type the sort u. *)
  let super l =
    if is_small l then type1
    else
      List.Smart.map (fun x -> Expr.successor x) l

  let addn l k =
    assert (k >= 0);
    if Int.equal k 0 then l
    else List.Smart.map (fun x -> Expr.addn x k) l

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

  let all_above n u =
    List.for_all (fun (_l, k) -> k >= n) u

  let canonize u =
    match u with
    | [] | [_] -> u
    | (l, n) :: u' ->
      if Level.is_zero l then
        if Int.equal n 0 then u'
        else if all_above n u' then u'
        else u
      else u

  let sort u =
    canonize (List.fold_right (fun a acc -> sup [a] acc) u [])

  let exists = List.exists

  let for_all = List.for_all
  let repr x : t = x
  let unrepr l =
    assert (not (List.is_empty l));
    sort l

  let decompose_succ (x : t) : t option =
    if List.for_all (fun (_, k) -> k > 0) x then
      Some (List.map (fun (l, k) -> (l, pred k)) x)
    else None

  let make_subst_fn (m : t Level.Map.t) =
    fun l ->
      match Level.Map.find_opt l m with
      | None -> make l
      | Some u -> u

  let subst_fn fn u =
    let modified = ref false in
    let rec aux u' = function
      | [] -> u'
      | (l, k as x) :: u ->
        let univ = fn l in
        if Option.equal Level.equal (level univ) (Some l) then aux (x :: u') u
        else begin
          modified := true;
          aux (List.append (addn univ k) u') u
        end
    in
    let u' = aux [] u in
    if not !modified then u
    else unrepr u'

end

module LevelExpr = Universe.Expr

module UnivConstraint = struct
  type kind = Le | Eq

  let eq_kind c1 c2 =
    match c1, c2 with
    | Le, Le | Eq, Eq -> true
    | _ -> false

  let compare_kind c1 c2 =
    match c1, c2 with
    | Le, Le -> 0
    | Le, Eq -> -1
    | Eq, Eq -> 0
    | Eq, _ -> 1

  let pr_kind op =
    let op_str = match op with
      | Le -> " <= "
      | Eq -> " = "
    in str op_str

  let hash_kind = function
    | Le -> 0
    | Eq -> 1

  type t = Universe.t * kind * Universe.t

  let compare (u, c, v) (u', c', v') =
    let i = compare_kind c c' in
    if not (Int.equal i 0) then i
    else
      let i' = Universe.compare u u' in
      if not (Int.equal i' 0) then i'
      else Universe.compare v v'

  module Hstruct = struct
    type nonrec t = t

    let hashcons (l1,k,l2) =
      let hl1, l1 = Universe.hcons l1 in
      let hl2, l2 = Universe.hcons l2 in
      Hashset.Combine.(combinesmall (hash_kind k) (combine hl1 hl2)), (l1,k,l2)

    let eq (l1,k,l2) (l1',k',l2') =
      eq_kind k k' && l1 == l1' && l2 == l2'
  end

  module Hasher = Hashcons.Make(Hstruct)

  let hcons = Hashcons.simple_hcons Hasher.generate Hasher.hcons ()
end

module UnivConstraints =
struct
  module S = Set.Make(UnivConstraint)
  include S

  let pr prl c =
    v 0 (prlist_with_sep spc (fun (u1,op,u2) ->
      hov 0 (Universe.pr prl u1 ++ UnivConstraint.pr_kind op ++ Universe.pr prl u2))
        (elements c))

  module Hconstraints = CSet.Hashcons(UnivConstraint)(struct
      type t = UnivConstraint.t
      let hcons = UnivConstraint.hcons
    end)

  let hcons = Hashcons.simple_hcons Hconstraints.generate Hconstraints.hcons ()
end

(** UnivConstraints functions. *)

type 'a constraint_function = 'a -> 'a -> UnivConstraints.t -> UnivConstraints.t

let enforce_eq_level u v c =
  (* We discard trivial constraints like u=u *)
  if Level.equal u v then c
  else UnivConstraints.add (Universe.make u,UnivConstraint.Eq,Universe.make v) c

let enforce_leq_level u v c =
  if Level.equal u v then c else UnivConstraints.add (Universe.make u,UnivConstraint.Le,Universe.make v) c

let enforce u k v c =
  if Universe.equal u v then c else UnivConstraints.add (u,k,v) c

let enforce_eq u v c = enforce u UnivConstraint.Eq v c
let enforce_leq u v c = enforce u UnivConstraint.Le v c

(* Miscellaneous functions to remove or test local univ assumed to
   occur in a universe *)

let univ_level_mem u v =
  List.exists (fun (l, n) -> Int.equal n 0 && Level.equal u l) v

let univ_level_rem u v min =
  match Universe.level v with
  | Some u' -> if Level.equal u u' then min else v
  | None -> List.filter (fun (l, n) -> not (Int.equal n 0 && Level.equal u l)) v

(* Is u mentioned in v (or equals to v) ? *)

module ContextSet =
struct
  type t = Level.Set.t * UnivConstraints.t

  let empty = (Level.Set.empty, UnivConstraints.empty)
  let is_empty (univs, cst) = Level.Set.is_empty univs && UnivConstraints.is_empty cst

  let equal (univs, cst as x) (univs', cst' as y) =
    x == y || (Level.Set.equal univs univs' && UnivConstraints.equal cst cst')

  let of_set s = (s, UnivConstraints.empty)
  let singleton l = of_set (Level.Set.singleton l)

  let union (univs, cst as x) (univs', cst' as y) =
    if x == y then x
    else Level.Set.union univs univs', UnivConstraints.union cst cst'

  let append (univs, cst) (univs', cst') =
    let univs = Level.Set.fold Level.Set.add univs univs' in
    let cst = UnivConstraints.fold UnivConstraints.add cst cst' in
    (univs, cst)

  let diff (univs, cst) (univs', cst') =
    Level.Set.diff univs univs', UnivConstraints.diff cst cst'

  let add_universe u (univs, cst) =
    Level.Set.add u univs, cst

  let add_constraints cst' (univs, cst) =
    univs, UnivConstraints.union cst cst'

  let pr prl (univs, cst as ctx) =
    if is_empty ctx then mt() else
      hov 0 (h (Level.Set.pr prl univs ++ str " |") ++ brk(1,2) ++ h (UnivConstraints.pr prl cst))

  let constraints (_univs, cst) = cst
  let levels (univs, _cst) = univs

  let size (univs,_) = Level.Set.cardinal univs

  let hcons (v,c) =
    let hv, v = Level.Set.hcons v in
    let hc, c = UnivConstraints.hcons c in
    Hashset.Combine.combine hv hc, (v, c)

end
