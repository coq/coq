(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* Initial Caml version originates from CoC 4.8 [Dec 1988] *)
(* Extension with algebraic universes by HH [Sep 2001] *)
(* Additional support for sort-polymorphic inductive types by HH [Mar 2006] *)

(* Universes are stratified by a partial ordering $\le$.
   Let $\~{}$ be the associated equivalence. We also have a strict ordering
   $<$ between equivalence classes, and we maintain that $<$ is acyclic,
   and contained in $\le$ in the sense that $[U]<[V]$ implies $U\le V$.

   At every moment, we have a finite number of universes, and we
   maintain the ordering in the presence of assertions $U<V$ and $U\le V$.

   The equivalence $\~{}$ is represented by a tree structure, as in the
   union-find algorithm. The assertions $<$ and $\le$ are represented by
   adjacency lists *)

open Pp
open Util

(* An algebraic universe [universe] is either a universe variable
   [universe_level] or a formal universe known to be greater than some
   universe variables and strictly greater than some (other) universe
   variables

   Universes variables denote universes initially present in the term
   to type-check and non variable algebraic universes denote the
   universes inferred while type-checking: it is either the successor
   of a universe present in the initial term to type-check or the
   maximum of two algebraic universes
 *)

type universe_level =
  | Base
  | Level of Names.dir_path * int

type universe =
  | Atom of universe_level
  | Max of universe_level list * universe_level list
  
module UniverseOrdered = struct
  type t = universe_level
  let compare = Pervasives.compare
end

let string_of_univ_level = function
  | Base -> "0"
  | Level (d,n) -> Names.string_of_dirpath d^"."^string_of_int n

let make_univ (m,n) = Atom (Level (m,n))

let pr_uni_level u = str (string_of_univ_level u)

let pr_uni = function
  | Atom u -> 
      pr_uni_level u
  | Max ([],[u]) ->
      str "(" ++ pr_uni_level u ++ str ")+1"
  | Max (gel,gtl) ->
      str "max(" ++ hov 0
       (prlist_with_sep pr_coma pr_uni_level gel ++
	  (if gel <> [] & gtl <> [] then pr_coma () else mt ()) ++
	prlist_with_sep pr_coma
	  (fun x -> str "(" ++ pr_uni_level x ++ str ")+1") gtl) ++
      str ")"

(* Returns the formal universe that lies juste above the universe variable u.
   Used to type the sort u. *)
let super = function
  | Atom u -> 
      Max ([],[u])
  | Max _ ->
      anomaly ("Cannot take the successor of a non variable universes:\n"^
               "(maybe a bugged tactic)")

(* Returns the formal universe that is greater than the universes u and v.
   Used to type the products. *)
let sup u v =
  match u,v with
    | Atom u, Atom v -> if u = v then Atom u else Max ([u;v],[])
    | u, Max ([],[]) -> u
    | Max ([],[]), v -> v
    | Atom u, Max (gel,gtl) -> Max (list_add_set u gel,gtl)
    | Max (gel,gtl), Atom v -> Max (list_add_set v gel,gtl)
    | Max (gel,gtl), Max (gel',gtl') ->
	let gel'' = list_union gel gel' in
	let gtl'' = list_union gtl gtl' in
	Max (list_subtract gel'' gtl'',gtl'')

let neutral_univ = Max ([],[])

(* Comparison on this type is pointer equality *)
type canonical_arc =
    { univ: universe_level; lt: universe_level list; le: universe_level list }

let terminal u = {univ=u; lt=[]; le=[]}

(* A universe_level is either an alias for another one, or a canonical one,
   for which we know the universes that are above *)
type univ_entry =
    Canonical of canonical_arc
  | Equiv of universe_level * universe_level

module UniverseMap = Map.Make(UniverseOrdered)

type universes = univ_entry UniverseMap.t
		   
let enter_equiv_arc u v g =
  UniverseMap.add u (Equiv(u,v)) g

let enter_arc ca g =
  UniverseMap.add ca.univ (Canonical ca) g

let declare_univ u g =
  if not (UniverseMap.mem u g) then
    enter_arc (terminal u) g
  else
    g

(* The level of Set *)
let base_univ = Atom Base

let is_base_univ = function
  | Atom Base -> true
  | Max ([Base],[]) -> warning "Non canonical Set"; true
  | u -> false

let is_univ_variable = function
  | Atom a when a<>Base -> true
  | _ -> false

(* When typing [Prop] and [Set], there is no constraint on the level,
   hence the definition of [prop_univ], the type of [Prop] *)

let initial_universes = UniverseMap.empty
let prop_univ = Max ([],[Base])

(* Every universe_level has a unique canonical arc representative *)

(* repr : universes -> universe_level -> canonical_arc *)
(* canonical representative : we follow the Equiv links *)
let repr g u = 
  let rec repr_rec u =
    let a =
      try UniverseMap.find u g
      with Not_found -> anomalylabstrm "Univ.repr"
	  (str"Universe " ++ pr_uni_level u ++ str" undefined") 
    in
    match a with 
      | Equiv(_,v) -> repr_rec v
      | Canonical arc -> arc
  in
  repr_rec u

let can g = List.map (repr g)

(* transitive closure : we follow the Less links *)

(* collect : canonical_arc -> canonical_arc list * canonical_arc list *)
(* collect u = (V,W) iff V={v canonical | u<v} W={w canonical | u<=w}-V *)
(* i.e. collect does the transitive upward closure of what is known about u *)
let collect g arcu =
  let rec coll_rec lt le = function
    | [],[] -> (lt, list_subtractq le lt)
    | arcv::lt', le' ->
	if List.memq arcv lt then 
	  coll_rec lt le (lt',le')
	else
          coll_rec (arcv::lt) le ((can g (arcv.lt@arcv.le))@lt',le')
    | [], arcw::le' -> 
	if (List.memq arcw lt) or (List.memq arcw le) then 
	  coll_rec lt le ([],le')
	else
          coll_rec lt (arcw::le) (can g arcw.lt, (can g arcw.le)@le')
  in 
  coll_rec [] [] ([],[arcu])

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


(* between : universe_level -> canonical_arc -> canonical_arc list *)
(* between u v = {w|u<=w<=v, w canonical}          *)     
(* between is the most costly operation *)

let between g u arcv = 
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
  let good,_,_ = explore ([arcv],[],false) (repr g u) in
    good
      
(* We assume  compare(u,v) = LE with v canonical (see compare below).
   In this case List.hd(between g u v) = repr u
   Otherwise, between g u v = [] 
 *)


type order = EQ | LT | LE | NLE

(* compare : universe_level -> universe_level -> order *)
let compare g u v = 
  let arcu = repr g u 
  and arcv = repr g v in
  if arcu==arcv then 
    EQ
  else 
    let (lt,leq) = collect g arcu in
    if List.memq arcv lt then 
      LT
    else if List.memq arcv leq then 
      LE
    else 
      NLE

(* Invariants : compare(u,v) = EQ <=> compare(v,u) = EQ
                compare(u,v) = LT or LE => compare(v,u) = NLE
                compare(u,v) = NLE => compare(v,u) = NLE or LE or LT

   Adding u>=v is consistent iff compare(v,u) # LT 
    and then it is redundant iff compare(u,v) # NLE
   Adding u>v is consistent iff compare(v,u) = NLE 
    and then it is redundant iff compare(u,v) = LT *)


(* setlt : universe_level -> universe_level -> unit *)
(* forces u > v *)
let setlt g u v =
  let arcu = repr g u in
  enter_arc {arcu with lt=v::arcu.lt} g

(* checks that non-redundant *)
let setlt_if g u v = match compare g u v with
  | LT -> g
  | _ -> setlt g u v

(* setleq : universe_level -> universe_level -> unit *)
(* forces u >= v *)
let setleq g u v =
  let arcu = repr g u in
  enter_arc {arcu with le=v::arcu.le} g


(* checks that non-redundant *)
let setleq_if g u v = match compare g u v with
  | NLE -> setleq g u v
  | _ -> g

(* merge : universe_level -> universe_level -> unit *)
(* we assume  compare(u,v) = LE *)
(* merge u v  forces u ~ v with repr u as canonical repr *)
let merge g u v =
  match between g u (repr g v) with
    | arcu::v -> (* arcu is chosen as canonical and all others (v) are *)
                 (* redirected to it *)
	let redirect (g,w,w') arcv =
 	  let g' = enter_equiv_arc arcv.univ arcu.univ g in
 	  (g',list_unionq arcv.lt w,arcv.le@w') 
	in
	let (g',w,w') = List.fold_left redirect (g,[],[]) v in
	let g'' = List.fold_left (fun g -> setlt_if g arcu.univ) g' w in
	let g''' = List.fold_left (fun g -> setleq_if g arcu.univ) g'' w' in
	g'''
    | [] -> anomaly "Univ.between"

(* merge_disc : universe_level -> universe_level -> unit *)
(* we assume  compare(u,v) = compare(v,u) = NLE *)
(* merge_disc u v  forces u ~ v with repr u as canonical repr *)
let merge_disc g u v =
  let arcu = repr g u in
  let arcv = repr g v in
  let g' = enter_equiv_arc arcv.univ arcu.univ g in
  let g'' = List.fold_left (fun g -> setlt_if g arcu.univ) g' arcv.lt in
  let g''' = List.fold_left (fun g -> setleq_if g arcu.univ) g'' arcv.le in
  g'''

(* Universe inconsistency: error raised when trying to enforce a relation
   that would create a cycle in the graph of universes. *)

type order_request = Lt | Le | Eq

exception UniverseInconsistency of order_request * universe * universe

let error_inconsistency o u v = raise (UniverseInconsistency (o,Atom u,Atom v))

(* enforce_univ_leq : universe_level -> universe_level -> unit *)
(* enforce_univ_leq u v will force u<=v if possible, will fail otherwise *)
let enforce_univ_leq u v g =
  let g = declare_univ u g in
  let g = declare_univ v g in
  match compare g u v with
    | NLE -> 
	(match compare g v u with
           | LT -> error_inconsistency Le u v
           | LE -> merge g v u
           | NLE -> setleq g u v
           | EQ -> anomaly "Univ.compare")
    | _ -> g

(* enforc_univ_eq : universe_level -> universe_level -> unit *)
(* enforc_univ_eq u v will force u=v if possible, will fail otherwise *)
let enforce_univ_eq u v g =
  let g = declare_univ u g in
  let g = declare_univ v g in
  match compare g u v with
    | EQ -> g
    | LT -> error_inconsistency Eq u v
    | LE -> merge g u v
    | NLE -> 
	(match compare g v u with
           | LT -> error_inconsistency Eq u v
           | LE -> merge g v u
           | NLE -> merge_disc g u v
           | EQ -> anomaly "Univ.compare")

(* enforce_univ_lt u v will force u<v if possible, will fail otherwise *)
let enforce_univ_lt u v g =
  let g = declare_univ u g in
  let g = declare_univ v g in
  match compare g u v with
    | LT -> g
    | LE -> setlt g u v
    | EQ -> error_inconsistency Lt u v
    | NLE -> 
	(match compare g v u with
           | NLE -> setlt g u v
           | _ -> error_inconsistency Lt u v)

(*
let enforce_univ_relation g = function 
  | Equiv (u,v) -> enforce_univ_eq u v g
  | Canonical {univ=u; lt=lt; le=le} ->
      let g' = List.fold_right (enforce_univ_lt u) lt g in
      List.fold_right (enforce_univ_leq u) le g'
*)

(* Merging 2 universe graphs *)
(*
let merge_universes sp u1 u2 =
  UniverseMap.fold (fun _ a g -> enforce_univ_relation g a) u1 u2
*)


(* Constraints and sets of consrtaints. *)

type constraint_type = Lt | Leq | Eq

type univ_constraint = universe_level * constraint_type * universe_level

let enforce_constraint cst g =
  match cst with
    | (u,Lt,v) -> enforce_univ_lt u v g
    | (u,Leq,v) -> enforce_univ_leq u v g
    | (u,Eq,v) -> enforce_univ_eq u v g


module Constraint = Set.Make(
  struct 
    type t = univ_constraint 
    let compare = Pervasives.compare 
  end)
		      
type constraints = Constraint.t

type constraint_function = 
    universe -> universe -> constraints -> constraints

let constraint_add_leq v u c =
  if v = Base then c else Constraint.add (v,Leq,u) c

let enforce_geq u v c =
  match u, v with
  | Atom u, Atom v -> constraint_add_leq v u c
  | Atom u, Max (gel,gtl) ->
      let d = List.fold_right (fun v -> constraint_add_leq v u) gel c in
      List.fold_right (fun v -> Constraint.add (v,Lt,u)) gtl d
  | _ -> anomaly "A universe bound can only be a variable"

let enforce_eq u v c =
  match (u,v) with
    | Atom u, Atom v -> Constraint.add (u,Eq,v) c
    | _ -> anomaly "A universe comparison can only happen between variables"

let merge_constraints c g =
  Constraint.fold enforce_constraint c g

(**********************************************************************)
(* Tools for sort-polymorphic inductive types                         *)

(* Temporary inductive type levels *)

let fresh_level =
  let n = ref 0 in fun () -> incr n; Level (Names.make_dirpath [],!n)

let fresh_local_univ () = Atom (fresh_level ())

(* Miscellaneous functions to remove or test local univ assumed to
   occur only in the le constraints *)

let make_max = function
  | ([u],[]) -> Atom u
  | (le,lt) -> Max (le,lt)

let remove_large_constraint u = function
  | Atom u' as x -> if u = u' then Max ([],[]) else x
  | Max (le,lt) -> make_max (list_remove u le,lt)

let is_empty_univ = function
  | Max ([],[]) -> true
  | _ -> false

let is_direct_constraint u = function
  | Atom u' -> u = u'
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
      if i<>j & is_direct_sort_constraint levels.(j) v.(i) then
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

(* Pretty-printing *)

let num_universes g =
  UniverseMap.fold (fun _ _ -> succ) g 0

let num_edges g =
  let reln_len = function
    | Equiv _ -> 1
    | Canonical {lt=lt;le=le} -> List.length lt + List.length le
  in
  UniverseMap.fold (fun _ a n -> n + (reln_len a)) g 0
    
let pr_arc = function 
  | Canonical {univ=u; lt=[]; le=[]} ->
      mt ()
  | Canonical {univ=u; lt=lt; le=le} ->
      pr_uni_level u ++ str " " ++
      v 0
        (prlist_with_sep pr_spc (fun v -> str "< " ++ pr_uni_level v) lt ++
	 (if lt <> [] & le <> [] then spc () else mt()) ++
         prlist_with_sep pr_spc (fun v -> str "<= " ++ pr_uni_level v) le) ++
      fnl ()
  | Equiv (u,v) -> 
      pr_uni_level u  ++ str " = " ++ pr_uni_level v ++ fnl ()

let pr_universes g =
  let graph = UniverseMap.fold (fun k a l -> (k,a)::l) g [] in
  prlist (function (_,a) -> pr_arc a) graph
    

(* Dumping constrains to a file *)

let dump_universes output g = 
  let dump_arc _ = function
    | Canonical {univ=u; lt=lt; le=le} -> 
	let u_str = string_of_univ_level u in
	  List.iter 
	    (fun v -> 
	       Printf.fprintf output "%s > %s ;\n" u_str
		 (string_of_univ_level v)) 
	    lt;
	  List.iter 
	    (fun v -> 
	       Printf.fprintf output "%s >= %s ;\n" u_str
		 (string_of_univ_level v)) 
	    le
    | Equiv (u,v) ->
	Printf.fprintf output "%s = %s ;\n"
	  (string_of_univ_level u) (string_of_univ_level v)
  in
    UniverseMap.iter dump_arc g 

(* Hash-consing *)

module Huniv =
  Hashcons.Make(
    struct
      type t = universe
      type u = Names.dir_path -> Names.dir_path
      let hash_aux hdir = function
	| Base -> Base
	| Level (d,n) -> Level (hdir d,n)
      let hash_sub hdir = function
	| Atom u -> Atom (hash_aux hdir u)
	| Max (gel,gtl) ->
	    Max (List.map (hash_aux hdir) gel, List.map (hash_aux hdir) gtl)
      let equal u v =
	match u, v with
	  | Atom u, Atom v -> u == v
	  | Max (gel,gtl), Max (gel',gtl') ->
	      (list_for_all2eq (==) gel gel') &&
              (list_for_all2eq (==) gtl gtl')
	  | _ -> false
      let hash = Hashtbl.hash
    end)

let hcons1_univ u =
  let _,_,hdir,_,_,_ = Names.hcons_names() in
  Hashcons.simple_hcons Huniv.f hdir u

