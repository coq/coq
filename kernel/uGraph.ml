(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Univ

(* Created in Caml by Gérard Huet for CoC 4.8 [Dec 1988] *)
(* Functional code by Jean-Christophe Filliâtre for Coq V7.0 [1999] *)
(* Extension with algebraic universes by HH for Coq V7.0 [Sep 2001] *)
(* Additional support for sort-polymorphic inductive types by HH [Mar 2006] *)
(* Support for universe polymorphism by MS [2014] *)

(* Revisions by Bruno Barras, Hugo Herbelin, Pierre Letouzey, Matthieu Sozeau, 
   Pierre-Marie Pédrot *)

let error_inconsistency o u v (p:explanation option) =
  raise (UniverseInconsistency (o,Universe.make u,Universe.make v,p))

type status = Unset | SetLe | SetLt

(* Comparison on this type is pointer equality *)
type canonical_arc =
    { univ: Level.t;
      lt: Level.t list;
      le: Level.t list;
      rank : int;
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

let terminal u = {univ=u; lt=[]; le=[]; rank=0; status = Unset}

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

type t = universes

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

(** The graph always contains nodes for Prop and Set. *)

let terminal_lt u v =
  {(terminal u) with lt=[v]}
    
let empty_universes =
  let g = enter_arc (terminal Level.set) UMap.empty in
  let g = enter_arc (terminal_lt Level.prop Level.set) g in
    g

(* repr : universes -> Level.t -> canonical_arc *)
(* canonical representative : we follow the Equiv links *)

let rec repr g u =
  let a =
    try UMap.find u g
    with Not_found -> anomaly ~label:"Univ.repr"
        (str"Universe " ++ Level.pr u ++ str" undefined")
  in
  match a with
    | Equiv v -> repr g v
    | Canonical arc -> arc

let get_prop_arc g = repr g Level.prop
let get_set_arc g = repr g Level.set
let is_set_arc u = Level.is_set u.univ
let is_prop_arc u = Level.is_prop u.univ

exception AlreadyDeclared
            
let add_universe vlev strict g =
  try
    let _arcv = UMap.find vlev g in
      raise AlreadyDeclared
  with Not_found -> 
    let v = terminal vlev in
    let arc =
      let arc = get_set_arc g in
        if strict then
          { arc with lt=vlev::arc.lt}
        else 
          { arc with le=vlev::arc.le}
    in
    let g = enter_arc arc g in
      enter_arc v g

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
          let p = (Lt, Universe.make u) :: p in
          if arc == arcv then
            if strict then (to_revert, p) else (to_revert, p)
          else find ((arc, p) :: lt_todo) lt le
        end
      | u :: le ->
        let arc = repr g u in
        let p = (Le, Universe.make u) :: p in
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
            let p = (Le, Universe.make u) :: p in
            let node = (repr g u, p) in
            node :: accu
          in
          let le_new = List.fold_left fold le_todo arc.le in
          let () = arc.status <- SetLe in
          cmp c (arc :: to_revert) lt_todo le_new
        | u :: lt ->
          let arc = repr g u in
          let p = (Lt, Universe.make u) :: p in
          if arc == arcv then
            if strict then (to_revert, p) else (to_revert, p)
          else find ((arc, p) :: lt_todo) lt
        in
        find [] arc.lt
  in
  let start = (* if is_prop_arc arcu then [Le, make arcv.univ] else *) [] in
  try
    let (to_revert, c) = cmp start [] [] [(arcu, [])] in
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
      let () = arc.status <- SetLt in
      process_lt c (arc :: to_revert) lt_todo le_todo arc.lt arc.le
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
        let () = arc.status <- SetLe in
        process_le c (arc :: to_revert) [] le_todo arc.lt arc.le

  and process_lt c to_revert lt_todo le_todo lt le = match le with
  | [] ->
    begin match lt with
    | [] -> cmp c to_revert lt_todo le_todo
    | u :: lt ->
      let arc = repr g u in
      if arc == arcv then
        if strict then (to_revert, FastLT) else (to_revert, FastLE)
      else process_lt c to_revert (arc :: lt_todo) le_todo lt le
    end
  | u :: le ->
    let arc = repr g u in
    if arc == arcv then
      if strict then (to_revert, FastLT) else (to_revert, FastLE)
    else process_lt c to_revert (arc :: lt_todo) le_todo lt le

  and process_le c to_revert lt_todo le_todo lt le = match lt with
  | [] ->
    let fold accu u =
      let node = repr g u in
      node :: accu
    in
    let le_new = List.fold_left fold le_todo le in
    cmp c to_revert lt_todo le_new
  | u :: lt ->
    let arc = repr g u in
    if arc == arcv then
      if strict then (to_revert, FastLT) else (to_revert, FastLE)
    else process_le c to_revert (arc :: lt_todo) le_todo lt le

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
  let arcu = repr g u and arcv = repr g v in
    arcu == arcv

let check_eq_level g u v = u == v || check_equal g u v

let check_smaller g strict u v =
  let arcu = repr g u and arcv = repr g v in
  if strict then
    is_lt g arcu arcv
  else
    is_prop_arc arcu 
    || (is_set_arc arcu && not (is_prop_arc arcv))
    || is_leq g arcu arcv

(** Then, checks on universes *)

type 'a check_function = universes -> 'a -> 'a -> bool

let check_equal_expr g x y =
  x == y || (let (u, n) = x and (v, m) = y in 
               Int.equal n m && check_equal g u v)

let check_eq_univs g l1 l2 =
  let f x1 x2 = check_equal_expr g x1 x2 in
  let exists x1 l = Universe.exists (fun x2 -> f x1 x2) l in
    Universe.for_all (fun x1 -> exists x1 l2) l1
    && Universe.for_all (fun x2 -> exists x2 l1) l2

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
  Universe.exists (fun ul' -> 
    check_smaller_expr g ul ul') l

let real_check_leq g u v =
  Universe.for_all (fun ul -> exists_bigger g ul v) u
    
let check_leq g u v =
  Universe.equal u v ||
    is_type0m_univ u ||
    check_eq_univs g u v || real_check_leq g u v

(** Enforcing new constraints : [setlt], [setleq], [merge], [merge_disc] *)

(* setlt : Level.t -> Level.t -> reason -> unit *)
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

(* setleq : Level.t -> Level.t -> unit *)
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

(* merge : Level.t -> Level.t -> unit *)
(* we assume  compare(u,v) = LE *)
(* merge u v  forces u ~ v with repr u as canonical repr *)
let merge g arcu arcv =
  (* we find the arc with the biggest rank, and we redirect all others to it *)
  let arcu, g, v =
    let best_ranked (max_rank, old_max_rank, best_arc, rest) arc =
      if Level.is_small arc.univ ||
           (arc.rank >= max_rank && not (Level.is_small best_arc.univ))
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
  let arcu, arcv = if Level.is_small arc2.univ || arc1.rank < arc2.rank then arc2, arc1 else arc1, arc2 in
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

(* enforce_univ_eq : Level.t -> Level.t -> unit *)
(* enforce_univ_eq u v will force u=v if possible, will fail otherwise *)

let enforce_univ_eq u v g =
  let arcu = repr g u and arcv = repr g v in
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
  let arcu = repr g u and arcv = repr g v in
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
  let arcu = repr g u and arcv = repr g v in
    match fast_compare g arcu arcv with
    | FastLT -> g
    | FastLE -> fst (setlt g arcu arcv)
    | FastEQ -> error_inconsistency Lt u v (Some [(Eq,Universe.make v)])
    | FastNLE ->
      match fast_compare_neq false g arcv arcu with
        FastNLE -> fst (setlt g arcu arcv)
      | FastEQ -> anomaly (Pp.str "Univ.compare")
      | (FastLE|FastLT) ->
        let p = get_explanation false g arcv arcu  in
        error_inconsistency Lt u v p

(* Prop = Set is forbidden here. *)
let initial_universes = empty_universes

let is_initial_universes g = UMap.equal (==) g initial_universes
      
let enforce_constraint cst g =
  match cst with
    | (u,Lt,v) -> enforce_univ_lt u v g
    | (u,Le,v) -> enforce_univ_leq u v g
    | (u,Eq,v) -> enforce_univ_eq u v g
      
let merge_constraints c g =
  Constraint.fold enforce_constraint c g

let check_constraint g (l,d,r) =
  match d with
  | Eq -> check_equal g l r
  | Le -> check_smaller g false l r
  | Lt -> check_smaller g true l r

let check_constraints c g =
  Constraint.for_all (check_constraint g) c

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
    if i < max then
      let pred = types.(i + 1) in
      let arc = {univ = u; lt = [pred]; le = []; rank = 0; status = Unset; } in
      UMap.add u (Canonical arc) accu
    else accu
  in
  Array.fold_left_i fold sorted types

(** Instances *)

let check_eq_instances g t1 t2 =
  let t1 = Instance.to_array t1 in
  let t2 = Instance.to_array t2 in
  t1 == t2 ||
    (Int.equal (Array.length t1) (Array.length t2) &&
        let rec aux i =
          (Int.equal i (Array.length t1)) || (check_eq_level g t1.(i) t2.(i) && aux (i + 1))
        in aux 0)

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

(* Dumping constraints to a file *)

let dump_universes output g =
  let dump_arc u = function
    | Canonical {univ=u; lt=lt; le=le} ->
        let u_str = Level.to_string u in
        List.iter (fun v -> output Lt u_str (Level.to_string v)) lt;
        List.iter (fun v -> output Le u_str (Level.to_string v)) le
    | Equiv v ->
      output Eq (Level.to_string u) (Level.to_string v)
  in
  UMap.iter dump_arc g

(** Profiling *)

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
