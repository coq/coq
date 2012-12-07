(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
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

module UniverseLevel = struct

  type t =
    | Set
    | Level of int * Names.dir_path

  (* A specialized comparison function: we compare the [int] part first.
     This way, most of the time, the [dir_path] part is not considered.

     Normally, placing the [int] first in the pair above in enough in Ocaml,
     but to be sure, we write below our own comparison function.

     Note: this property is used by the [check_sorted] function below. *)

  let compare u v =
    if u == v then 0
    else
    (match u,v with
    | Set, Set -> 0
    | Set, _ -> -1
    | _, Set -> 1
    | Level (i1, dp1), Level (i2, dp2) ->
      if i1 < i2 then -1
      else if i1 > i2 then 1
      else Names.dir_path_ord dp1 dp2)

  let equal u v = match u,v with
    | Set, Set -> true
    | Level (i1, dp1), Level (i2, dp2) ->
      Int.equal i1 i2 && Int.equal (Names.dir_path_ord dp1 dp2) 0
    | _ -> false

  let make m n = Level (n, m)

  let to_string = function
    | Set -> "Set"
    | Level (n,d) -> Names.string_of_dirpath d^"."^string_of_int n
end

module UniverseLMap = Map.Make (UniverseLevel)
module UniverseLSet = Set.Make (UniverseLevel)

type universe_level = UniverseLevel.t

let compare_levels = UniverseLevel.compare

(* An algebraic universe [universe] is either a universe variable
   [UniverseLevel.t] or a formal universe known to be greater than some
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
  type t =
  | Atom of UniverseLevel.t
  | Max of UniverseLevel.t list * UniverseLevel.t list

  let compare u1 u2 =
    if u1 == u2 then 0 else
    match u1, u2 with
    | Atom l1, Atom l2 -> UniverseLevel.compare l1 l2
    | Max (lt1, le1), Max (lt2, le2) ->
      let c = List.compare UniverseLevel.compare lt1 lt2 in
      if Int.equal c 0 then
        List.compare UniverseLevel.compare le1 le2
      else c
    | Atom _, Max _ -> -1
    | Max _, Atom _ -> 1

  let equal u1 u2 = Int.equal (compare u1 u2) 0

  let make l = Atom l

end

open Universe

type universe = Universe.t

let universe_level = function
  | Atom l -> Some l
  | Max _ -> None

let pr_uni_level u = str (UniverseLevel.to_string u)

let pr_uni = function
  | Atom u ->
      pr_uni_level u
  | Max ([],[u]) ->
      str "(" ++ pr_uni_level u ++ str ")+1"
  | Max (gel,gtl) ->
      let opt_sep = match gel, gtl with
      | [], _ | _, [] -> mt ()
      | _ -> pr_comma ()
      in
      str "max(" ++ hov 0
       (prlist_with_sep pr_comma pr_uni_level gel ++ opt_sep ++
	prlist_with_sep pr_comma
	  (fun x -> str "(" ++ pr_uni_level x ++ str ")+1") gtl) ++
      str ")"

(* Returns the formal universe that lies juste above the universe variable u.
   Used to type the sort u. *)
let super = function
  | Atom u ->
      Max ([],[u])
  | Max _ ->
      anomaly ("Cannot take the successor of a non variable universe:\n"^
               "(maybe a bugged tactic)")

(* Returns the formal universe that is greater than the universes u and v.
   Used to type the products. *)
let sup u v =
  match u,v with
    | Atom u, Atom v ->
	if UniverseLevel.equal u v then Atom u else Max ([u;v],[])
    | u, Max ([],[]) -> u
    | Max ([],[]), v -> v
    | Atom u, Max (gel,gtl) -> Max (List.add_set u gel,gtl)
    | Max (gel,gtl), Atom v -> Max (List.add_set v gel,gtl)
    | Max (gel,gtl), Max (gel',gtl') ->
	let gel'' = List.union gel gel' in
	let gtl'' = List.union gtl gtl' in
	Max (List.subtract gel'' gtl'',gtl'')

(* Comparison on this type is pointer equality *)
type canonical_arc =
    { univ: UniverseLevel.t;
      lt: UniverseLevel.t list;
      le: UniverseLevel.t list;
      rank: int }

let terminal u = {univ=u; lt=[]; le=[]; rank=0}

(* A UniverseLevel.t is either an alias for another one, or a canonical one,
   for which we know the universes that are above *)

type univ_entry =
    Canonical of canonical_arc
  | Equiv of UniverseLevel.t


type universes = univ_entry UniverseLMap.t

let enter_equiv_arc u v g =
  UniverseLMap.add u (Equiv v) g

let enter_arc ca g =
  UniverseLMap.add ca.univ (Canonical ca) g

(* The lower predicative level of the hierarchy that contains (impredicative)
   Prop and singleton inductive types *)
let type0m_univ = Max ([],[])

let is_type0m_univ = function
  | Max ([],[]) -> true
  | _ -> false

(* The level of predicative Set *)
let type0_univ = Atom UniverseLevel.Set

let is_type0_univ = function
  | Atom UniverseLevel.Set -> true
  | Max ([UniverseLevel.Set], []) -> msg_warning (str "Non canonical Set"); true
  | u -> false

let is_univ_variable = function
  | Atom UniverseLevel.Set -> false
  | Atom _ -> true
  | _ -> false

(* When typing [Prop] and [Set], there is no constraint on the level,
   hence the definition of [type1_univ], the type of [Prop] *)

let type1_univ = Max ([], [UniverseLevel.Set])

let initial_universes = UniverseLMap.empty
let is_initial_universes = UniverseLMap.is_empty

(* Every UniverseLevel.t has a unique canonical arc representative *)

(* repr : universes -> UniverseLevel.t -> canonical_arc *)
(* canonical representative : we follow the Equiv links *)

let repr g u =
  let rec repr_rec u =
    let a =
      try UniverseLMap.find u g
      with Not_found -> anomalylabstrm "Univ.repr"
	  (str"Universe " ++ pr_uni_level u ++ str" undefined")
    in
    match a with
      | Equiv v -> repr_rec v
      | Canonical arc -> arc
  in
  repr_rec u

let can g = List.map (repr g)

(* [safe_repr] also search for the canonical representative, but
   if the graph doesn't contain the searched universe, we add it. *)

let safe_repr g u =
  let rec safe_repr_rec u =
    match UniverseLMap.find u g with
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


(* between : UniverseLevel.t -> canonical_arc -> canonical_arc list *)
(* between u v = {w|u<=w<=v, w canonical}          *)
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

(* Assuming the current universe has been reached by [p] and [l]
   correspond to the universes in (direct) relation [rel] with it,
   make a list of canonical universe, updating the relation with
   the starting point (path stored in reverse order). *)
let canp g (p:explanation) rel l : (canonical_arc * explanation) list =
  List.map (fun u -> (repr g u, (rel,Atom u)::p)) l

type order = EQ | LT of explanation | LE of explanation | NLE

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

let compare_neq strict g arcu arcv =
  (* [c] characterizes whether (and how) arcv has already been related
     to arcu among the lt_done,le_done universe *)
  let rec cmp c lt_done le_done = function
  | [],[] -> c
  | (arc,p)::lt_todo, le_todo ->
    if List.memq arc lt_done then
      cmp c lt_done le_done (lt_todo,le_todo)
    else
      let lt_new = canp g p Lt arc.lt@ canp g p Le arc.le in
      (try
	 let p = List.assq arcv lt_new in
	 if strict then LT p else LE p
       with Not_found ->
	 cmp c (arc::lt_done) le_done (lt_new@lt_todo,le_todo))
  | [], (arc,p)::le_todo ->
    if arc == arcv then
      (* No need to continue inspecting universes above arc:
	 if arcv is strictly above arc, then we would have a cycle.
         But we cannot answer LE yet, a stronger constraint may
	 come later from [le_todo]. *)
      if strict then cmp (LE p) lt_done le_done ([],le_todo) else LE p
    else
      if (List.memq arc lt_done) || (List.memq arc le_done) then
	cmp c lt_done le_done ([],le_todo)
      else
	let lt_new = canp g p Lt arc.lt in
	(try
	  let p = List.assq arcv lt_new in
	  if strict then LT p else LE p
	 with Not_found ->
	   let le_new = canp g p Le arc.le in
	   cmp c lt_done (arc::le_done) (lt_new, le_new@le_todo))
  in
  cmp NLE [] [] ([],[arcu,[]])

let compare g arcu arcv =
  if arcu == arcv then EQ else compare_neq true g arcu arcv

let is_leq g arcu arcv =
  arcu == arcv ||
 (match compare_neq false g arcu arcv with
     NLE -> false
   | (EQ|LE _|LT _) -> true)

let is_lt g arcu arcv =
  match compare g arcu arcv with
      LT _ -> true
    | (EQ|LE _|NLE) -> false

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

let check_smaller g strict u v =
  let g, arcu = safe_repr g u in
  let g, arcv = safe_repr g v in
  if strict then
    is_lt g arcu arcv
  else
    arcu == snd (safe_repr g UniverseLevel.Set) || is_leq g arcu arcv

(** Then, checks on universes *)

type check_function = universes -> universe -> universe -> bool

let incl_list cmp l1 l2 =
  List.for_all (fun x1 -> List.exists (fun x2 -> cmp x1 x2) l2) l1

let compare_list cmp l1 l2 =
  (l1 == l2)
  || (incl_list cmp l1 l2 && incl_list cmp l2 l1)

let check_eq g u v =
  match u,v with
    | Atom ul, Atom vl -> check_equal g ul vl
    | Max(ule,ult), Max(vle,vlt) ->
        (* TODO: remove elements of lt in le! *)
        compare_list (check_equal g) ule vle &&
        compare_list (check_equal g) ult vlt
    | _ -> anomaly "check_eq" (* not complete! (Atom(u) = Max([u],[]) *)

let check_leq g u v =
  match u,v with
    | Atom ul, Atom vl -> check_smaller g false ul vl
    | Max(le,lt), Atom vl ->
        List.for_all (fun ul -> check_smaller g false ul vl) le &&
        List.for_all (fun ul -> check_smaller g true ul vl) lt
    | _ -> anomaly "check_leq"

(** Enforcing new constraints : [setlt], [setleq], [merge], [merge_disc] *)

(* setlt : UniverseLevel.t -> UniverseLevel.t -> reason -> unit *)
(* forces u > v *)
(* this is normally an update of u in g rather than a creation. *)
let setlt g arcu arcv =
  let arcu' = {arcu with lt=arcv.univ::arcu.lt} in
  enter_arc arcu' g, arcu'

(* checks that non-redundant *)
let setlt_if (g,arcu) v =
  let arcv = repr g v in
  if is_lt g arcu arcv then g, arcu
  else setlt g arcu arcv

(* setleq : UniverseLevel.t -> UniverseLevel.t -> unit *)
(* forces u >= v *)
(* this is normally an update of u in g rather than a creation. *)
let setleq g arcu arcv =
  let arcu' = {arcu with le=arcv.univ::arcu.le} in
  enter_arc arcu' g, arcu'


(* checks that non-redundant *)
let setleq_if (g,arcu) v =
  let arcv = repr g v in
  if is_leq g arcu arcv then g, arcu
  else setleq g arcu arcv

(* merge : UniverseLevel.t -> UniverseLevel.t -> unit *)
(* we assume  compare(u,v) = LE *)
(* merge u v  forces u ~ v with repr u as canonical repr *)
let merge g arcu arcv =
  let bet = between g arcu arcv in
  (* we find the arc with the biggest rank, and we redirect all others to it *)
  let max, posmax, only = CList.fold_left_i (fun pos (max, posmax, only) arc -> 
    if arc.rank > max then (arc.rank, pos, true) else 
      if arc.rank = max then (arc.rank, pos, false) else
	(max, posmax, only))
    0 (-1, -1, true) bet
  in
  if posmax = -1 then anomaly "Univ.between";
  let arcu = List.nth bet posmax in
  let v = CList.filteri (fun i _ -> posmax <> i) bet in
  let arcu, g =
    if only then arcu, g
    else
      let arcu = {arcu with rank = succ arcu.rank} in
      arcu, enter_arc arcu g
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

(* merge_disc : UniverseLevel.t -> UniverseLevel.t -> unit *)
(* we assume  compare(u,v) = compare(v,u) = NLE *)
(* merge_disc u v  forces u ~ v with repr u as canonical repr *)
let merge_disc g arc1 arc2 =
  let arcu, arcv = if arc1.rank < arc2.rank then arc2, arc1 else arc1, arc2 in
  let arcu, g = 
    if arc1.rank <> arc2.rank then arcu, g
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

exception UniverseInconsistency of
  constraint_type * universe * universe * explanation

let error_inconsistency o u v (p:explanation) =
  raise (UniverseInconsistency (o,Atom u,Atom v,p))

(* enforce_univ_leq : UniverseLevel.t -> UniverseLevel.t -> unit *)
(* enforce_univ_leq u v will force u<=v if possible, will fail otherwise *)
let enforce_univ_leq u v g =
  let g,arcu = safe_repr g u in
  let g,arcv = safe_repr g v in
  if is_leq g arcu arcv then g
  else match compare g arcv arcu with
    | LT p -> error_inconsistency Le u v (List.rev p)
    | LE _ -> merge g arcv arcu
    | NLE -> fst (setleq g arcu arcv)
    | EQ -> anomaly "Univ.compare"

(* enforc_univ_eq : UniverseLevel.t -> UniverseLevel.t -> unit *)
(* enforc_univ_eq u v will force u=v if possible, will fail otherwise *)
let enforce_univ_eq u v g =
  let g,arcu = safe_repr g u in
  let g,arcv = safe_repr g v in
  match compare g arcu arcv with
    | EQ -> g
    | LT p -> error_inconsistency Eq u v (List.rev p)
    | LE _ -> merge g arcu arcv
    | NLE ->
	(match compare g arcv arcu with
           | LT p -> error_inconsistency Eq u v (List.rev p)
           | LE _ -> merge g arcv arcu
           | NLE -> merge_disc g arcu arcv
           | EQ -> anomaly "Univ.compare")

(* enforce_univ_lt u v will force u<v if possible, will fail otherwise *)
let enforce_univ_lt u v g =
  let g,arcu = safe_repr g u in
  let g,arcv = safe_repr g v in
  match compare g arcu arcv with
    | LT _ -> g
    | LE _ -> fst (setlt g arcu arcv)
    | EQ -> error_inconsistency Lt u v [(Eq,Atom v)]
    | NLE ->
      (match compare_neq false g arcv arcu with
	  NLE -> fst (setlt g arcu arcv)
	| EQ -> anomaly "Univ.compare"
	| (LE p|LT p) -> error_inconsistency Lt u v (List.rev p))

(* Constraints and sets of consrtaints. *)

type univ_constraint = UniverseLevel.t * constraint_type * UniverseLevel.t

let enforce_constraint cst g =
  match cst with
    | (u,Lt,v) -> enforce_univ_lt u v g
    | (u,Le,v) -> enforce_univ_leq u v g
    | (u,Eq,v) -> enforce_univ_eq u v g

module Constraint = Set.Make(
  struct
    type t = univ_constraint
    let compare (u,c,v) (u',c',v') =
      let i = constraint_type_ord c c' in
      if not (Int.equal i 0) then i
      else
	let i' = UniverseLevel.compare u u' in
	if not (Int.equal i' 0) then i'
	else UniverseLevel.compare v v'
  end)

type constraints = Constraint.t

let empty_constraint = Constraint.empty
let is_empty_constraint = Constraint.is_empty

let union_constraints = Constraint.union

type constraint_function =
    universe -> universe -> constraints -> constraints

let constraint_add_leq v u c =
  (* We just discard trivial constraints like Set<=u or u<=u *)
  if UniverseLevel.equal v UniverseLevel.Set || UniverseLevel.equal v u then c
  else Constraint.add (v,Le,u) c

let enforce_leq u v c =
  match u, v with
  | Atom u, Atom v -> constraint_add_leq u v c
  | Max (gel,gtl), Atom v ->
      let d = List.fold_right (fun u -> constraint_add_leq u v) gel c in
      List.fold_right (fun u -> Constraint.add (u,Lt,v)) gtl d
  | _ -> anomaly "A universe bound can only be a variable"

let enforce_eq u v c =
  match (u,v) with
    | Atom u, Atom v ->
      (* We discard trivial constraints like u=u *)
      if UniverseLevel.equal u v then c else Constraint.add (u,Eq,v) c
    | _ -> anomaly "A universe comparison can only happen between variables"

let merge_constraints c g =
  Constraint.fold enforce_constraint c g

(* Normalization *)

let lookup_level u g =
  try Some (UniverseLMap.find u g) with Not_found -> None

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
      u, UniverseLMap.add u u cache
    | Some (Canonical {univ=v; lt=_; le=_}) ->
      v, UniverseLMap.add u v cache
    | Some (Equiv v) ->
      let v, cache = visit v (lazy (lookup_level v g)) cache in
      v, UniverseLMap.add u v cache
  in
  let cache = UniverseLMap.fold
    (fun u arc cache -> snd (visit u (Lazy.lazy_from_val (Some arc)) cache))
    g UniverseLMap.empty
  in
  let repr x = UniverseLMap.find x cache in
  let lrepr us = List.fold_left
    (fun e x -> UniverseLSet.add (repr x) e) UniverseLSet.empty us
  in
  let canonicalize u = function
    | Equiv _ -> Equiv (repr u)
    | Canonical {univ=v; lt=lt; le=le; rank=rank} ->
      assert (u == v);
      (* avoid duplicates and self-loops *)
      let lt = lrepr lt and le = lrepr le in
      let le = UniverseLSet.filter
        (fun x -> x != u && not (UniverseLSet.mem x lt)) le
      in
      UniverseLSet.iter (fun x -> assert (x != u)) lt;
      Canonical {
        univ = v;
        lt = UniverseLSet.elements lt;
        le = UniverseLSet.elements le;
	rank = rank
      }
  in
  UniverseLMap.mapi canonicalize g

(** [check_sorted g sorted]: [g] being a universe graph, [sorted]
    being a map to levels, checks that all constraints in [g] are
    satisfied in [sorted]. *)
let check_sorted g sorted =
  let get u = try UniverseLMap.find u sorted with
    | Not_found -> assert false
  in
  let iter u arc =
    let lu = get u in match arc with
    | Equiv v -> assert (Int.equal lu (get v))
    | Canonical {univ = u'; lt = lt; le = le} ->
      assert (u == u');
      List.iter (fun v -> assert (lu <= get v)) le;
      List.iter (fun v -> assert (lu < get v)) lt
  in
  UniverseLMap.iter iter g

(**
  Bellman-Ford algorithm with a few customizations:
    - [weight(eq|le) = 0], [weight(lt) = -1]
    - a [le] edge is initially added from [bottom] to all other
      vertices, and [bottom] is used as the source vertex
*)
let bellman_ford bottom g =
  let () = match lookup_level bottom g with
  | None -> ()
  | Some _ -> assert false
  in
  let ( << ) a b = match a, b with
    | _, None -> true
    | None, _ -> false
    | Some x, Some y -> x < y
  and ( ++ ) a y = match a with
    | None -> None
    | Some x -> Some (x-y)
  and push u x m = match x with
    | None -> m
    | Some y -> UniverseLMap.add u y m
  in
  let relax u v uv distances =
    let x = lookup_level u distances ++ uv in
    if x << lookup_level v distances then push v x distances
    else distances
  in
  let init = UniverseLMap.add bottom 0 UniverseLMap.empty in
  let vertices = UniverseLMap.fold (fun u arc res ->
    let res = UniverseLSet.add u res in
    match arc with
      | Equiv e -> UniverseLSet.add e res
      | Canonical {univ=univ; lt=lt; le=le} ->
        assert (u == univ);
        let add res v = UniverseLSet.add v res in
        let res = List.fold_left add res le in
        let res = List.fold_left add res lt in
        res) g UniverseLSet.empty
  in
  let g =
    let node = Canonical {
      univ = bottom;
      lt = [];
      le = UniverseLSet.elements vertices;
      rank = 0
    } in UniverseLMap.add bottom node g
  in
  let rec iter count accu =
    if count <= 0 then
      accu
    else
      let accu = UniverseLMap.fold (fun u arc res -> match arc with
        | Equiv e -> relax e u 0 (relax u e 0 res)
        | Canonical {univ=univ; lt=lt; le=le} ->
          assert (u == univ);
          let res = List.fold_left (fun res v -> relax u v 0 res) res le in
          let res = List.fold_left (fun res v -> relax u v 1 res) res lt in
          res) g accu
      in iter (count-1) accu
  in
  let distances = iter (UniverseLSet.cardinal vertices) init in
  let () = UniverseLMap.iter (fun u arc ->
    let lu = lookup_level u distances in match arc with
      | Equiv v ->
        let lv = lookup_level v distances in
        assert (not (lu << lv) && not (lv << lu))
      | Canonical {univ=univ; lt=lt; le=le} ->
        assert (u == univ);
        List.iter (fun v -> assert (not (lu ++ 0 << lookup_level v distances))) le;
        List.iter (fun v -> assert (not (lu ++ 1 << lookup_level v distances))) lt) g
  in distances

(** [sort_universes g] builds a map from universes in [g] to natural
    numbers. It outputs a graph containing equivalence edges from each
    level appearing in [g] to [Type.n], and [lt] edges between the
    [Type.n]s. The output graph should imply the input graph (and the
    implication will be strict most of the time), but is not
    necessarily minimal. Note: the result is unspecified if the input
    graph already contains [Type.n] nodes (calling a module Type is
    probably a bad idea anyway). *)
let sort_universes orig =
  let mp = Names.make_dirpath [Names.id_of_string "Type"] in
  let rec make_level accu g i =
    let type0 = UniverseLevel.Level (i, mp) in
    let distances = bellman_ford type0 g in
    let accu, continue = UniverseLMap.fold (fun u x (accu, continue) ->
      let continue = continue || x < 0 in
      let accu =
        if Int.equal x 0 && u != type0 then UniverseLMap.add u i accu
        else accu
      in accu, continue) distances (accu, false)
    in
    let filter x = not (UniverseLMap.mem x accu) in
    let push g u =
      if UniverseLMap.mem u g then g else UniverseLMap.add u (Equiv u) g
    in
    let g = UniverseLMap.fold (fun u arc res -> match arc with
      | Equiv v as x ->
        begin match filter u, filter v with
          | true, true -> UniverseLMap.add u x res
          | true, false -> push res u
          | false, true -> push res v
          | false, false -> res
        end
      | Canonical {univ=v; lt=lt; le=le; rank=r} ->
        assert (u == v);
        if filter u then
          let lt = List.filter filter lt in
          let le = List.filter filter le in
          UniverseLMap.add u (Canonical {univ=u; lt=lt; le=le; rank=r}) res
        else
          let res = List.fold_left (fun g u -> if filter u then push g u else g) res lt in
          let res = List.fold_left (fun g u -> if filter u then push g u else g) res le in
          res) g UniverseLMap.empty
    in
    if continue then make_level accu g (i+1) else i, accu
  in
  let max, levels = make_level UniverseLMap.empty orig 0 in
  (* defensively check that the result makes sense *)
  check_sorted orig levels;
  let types = Array.init (max+1) (fun x -> UniverseLevel.Level (x, mp)) in
  let g = UniverseLMap.map (fun x -> Equiv types.(x)) levels in
  let g =
    let rec aux i g =
      if i < max then
        let u = types.(i) in
        let g = UniverseLMap.add u (Canonical {
          univ = u;
          le = [];
          lt = [types.(i+1)];
	  rank = 1
        }) g in aux (i+1) g
      else g
    in aux 0 g
  in g

(**********************************************************************)
(* Tools for sort-polymorphic inductive types                         *)

(* Temporary inductive type levels *)

let fresh_level =
  let n = ref 0 in fun () -> incr n; UniverseLevel.Level (!n, Names.make_dirpath [])

let fresh_local_univ () = Atom (fresh_level ())

(* Miscellaneous functions to remove or test local univ assumed to
   occur only in the le constraints *)

let make_max = function
  | ([u],[]) -> Atom u
  | (le,lt) -> Max (le,lt)

let remove_large_constraint u = function
  | Atom u' as x -> if UniverseLevel.equal u u' then Max ([],[]) else x
  | Max (le,lt) -> make_max (List.remove u le,lt)

let is_direct_constraint u = function
  | Atom u' -> UniverseLevel.equal u u'
  | Max (le,lt) -> List.mem u le

(*
   Solve a system of universe constraint of the form

   u_s11, ..., u_s1p1, w1 <= u1
   ...
   u_sn1, ..., u_snpn, wn <= un

where

  - the ui (1 <= i <= n) are universe variables,
  - the sjk select subsets of the ui for each equations,
  - the wi are arbitrary complex universes that do not mention the ui.
*)

let is_direct_sort_constraint s v = match s with
  | Some u -> is_direct_constraint u v
  | None -> false

let solve_constraints_system levels level_bounds =
  let levels =
    Array.map (Option.map (function Atom u -> u | _ -> anomaly "expects Atom"))
      levels in
  let v = Array.copy level_bounds in
  let nind = Array.length v in
  for i=0 to nind-1 do
    for j=0 to nind-1 do
      if not (Int.equal i j) && is_direct_sort_constraint levels.(j) v.(i) then
	v.(i) <- sup v.(i) level_bounds.(j)
    done;
    for j=0 to nind-1 do
      match levels.(j) with
      | Some u -> v.(i) <- remove_large_constraint u v.(i)
      | None -> ()
    done
  done;
  v

let subst_large_constraint u u' v =
  match u with
  | Atom u ->
      if is_direct_constraint u v then sup u' (remove_large_constraint u v)
      else v
  | _ ->
      anomaly "expect a universe level"

let subst_large_constraints =
  List.fold_right (fun (u,u') -> subst_large_constraint u u')

let no_upper_constraints u cst =
  match u with
  | Atom u ->
    let test (u1, _, _) =
      not (Int.equal (UniverseLevel.compare u1 u) 0) in
    Constraint.for_all test cst
  | Max _ -> anomaly "no_upper_constraints"

(* Is u mentionned in v (or equals to v) ? *)

let univ_depends u v =
  match u, v with
    | Atom u, Atom v -> UniverseLevel.equal u v
    | Atom u, Max (gel,gtl) -> List.mem u gel || List.mem u gtl
    | _ -> anomaly "univ_depends given a non-atomic 1st arg"

(* Pretty-printing *)

let pr_arc = function
  | _, Canonical {univ=u; lt=[]; le=[]} ->
      mt ()
  | _, Canonical {univ=u; lt=lt; le=le} ->
      let opt_sep = match lt, le with
      | [], _ | _, [] -> mt ()
      | _ -> spc ()
      in
      pr_uni_level u ++ str " " ++
      v 0
        (pr_sequence (fun v -> str "< " ++ pr_uni_level v) lt ++
	 opt_sep ++
         pr_sequence (fun v -> str "<= " ++ pr_uni_level v) le) ++
      fnl ()
  | u, Equiv v ->
      pr_uni_level u  ++ str " = " ++ pr_uni_level v ++ fnl ()

let pr_universes g =
  let graph = UniverseLMap.fold (fun u a l -> (u,a)::l) g [] in
  prlist pr_arc graph

let pr_constraints c =
  Constraint.fold (fun (u1,op,u2) pp_std ->
		     let op_str = match op with
		       | Lt -> " < "
		       | Le -> " <= "
		       | Eq -> " = "
		     in pp_std ++  pr_uni_level u1 ++ str op_str ++
			  pr_uni_level u2 ++ fnl () )  c (str "")

(* Dumping constraints to a file *)

let dump_universes output g =
  let dump_arc u = function
    | Canonical {univ=u; lt=lt; le=le} ->
	let u_str = UniverseLevel.to_string u in
	List.iter (fun v -> output Lt u_str (UniverseLevel.to_string v)) lt;
	List.iter (fun v -> output Le u_str (UniverseLevel.to_string v)) le
    | Equiv v ->
      output Eq (UniverseLevel.to_string u) (UniverseLevel.to_string v)
  in
    UniverseLMap.iter dump_arc g

(* Hash-consing *)

module Hunivlevel =
  Hashcons.Make(
    struct
      type t = universe_level
      type u = Names.dir_path -> Names.dir_path
      let hashcons hdir = function
	| UniverseLevel.Set -> UniverseLevel.Set
	| UniverseLevel.Level (n,d) -> UniverseLevel.Level (n,hdir d)
      let equal l1 l2 =
        l1 == l2 ||
        match l1,l2 with
	| UniverseLevel.Set, UniverseLevel.Set -> true
	| UniverseLevel.Level (n,d), UniverseLevel.Level (n',d') ->
	  n == n' && d == d'
	| _ -> false
      let hash = Hashtbl.hash
    end)

module Huniv =
  Hashcons.Make(
    struct
      type t = universe
      type u = universe_level -> universe_level
      let hashcons hdir = function
	| Atom u -> Atom (hdir u)
	| Max (gel,gtl) -> Max (List.map hdir gel, List.map hdir gtl)
      let equal u v =
        u == v ||
	match u, v with
	  | Atom u, Atom v -> u == v
	  | Max (gel,gtl), Max (gel',gtl') ->
	      (List.for_all2eq (==) gel gel') &&
              (List.for_all2eq (==) gtl gtl')
	  | _ -> false
      let hash = Hashtbl.hash
    end)

let hcons_univlevel = Hashcons.simple_hcons Hunivlevel.generate Names.hcons_dirpath
let hcons_univ = Hashcons.simple_hcons Huniv.generate hcons_univlevel

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

let hcons_constraint = Hashcons.simple_hcons Hconstraint.generate hcons_univlevel
let hcons_constraints = Hashcons.simple_hcons Hconstraints.generate hcons_constraint
