(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

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
    { u_mod : Names.dir_path;
      u_num : int }

type universe =
  | Variable of universe_level
  | Max of universe_level list * universe_level list
  
module UniverseOrdered = struct
  type t = universe_level
  let compare = Pervasives.compare
end

let string_of_univ_level u =
  Names.string_of_dirpath u.u_mod^"."^string_of_int u.u_num

let make_univ (m,n) = Variable { u_mod=m; u_num=n }

let pr_uni_level u = str (string_of_univ_level u)

let pr_uni = function
  | Variable u -> 
      pr_uni_level u
  | Max ([],[]) ->
      int 1
  | Max (gel,gtl) ->
      str "max(" ++ 
      prlist_with_sep pr_coma pr_uni_level gel ++
      if gel <> [] & gtl <> [] then pr_coma () else mt () ++
      prlist_with_sep pr_coma
	(fun x -> str "(" ++ pr_uni_level x ++ str ")+1") gtl ++
      str ")"

(* Returns the formal universe that lies juste above the universe variable u.
   Used to type the sort u. *)
let super = function
  | Variable u -> 
      Max ([],[u])
  | Max _ ->
      anomaly ("Cannot take the successor of a non variable universes:\n"^
       "you are probably typing a type already known to be the type\n"^
       "of a user-provided term; if you really need this, please report")

(* Returns the formal universe that is greater than the universes u and v.
   Used to type the products. *)
let sup u v = 
  match u,v with
    | Variable u, Variable v -> Max ((if u = v then [u] else [u;v]),[])
    | Variable u, Max (gel,gtl) -> Max (list_add_set u gel,gtl)
    | Max (gel,gtl), Variable v -> Max (list_add_set v gel,gtl)
    | Max (gel,gtl), Max (gel',gtl') ->
	Max (list_union gel gel',list_union gtl gtl')

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

(* When typing Prop and Set, there is no constraint on the level,
   hence the definition of prop_univ *)

let initial_universes = UniverseMap.empty
let prop_univ = Max ([],[])

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

exception UniverseInconsistency

let error_inconsistency () = raise UniverseInconsistency

(* enforce_univ_leq : universe_level -> universe_level -> unit *)
(* enforce_univ_leq u v will force u<=v if possible, will fail otherwise *)
let enforce_univ_leq u v g =
  let g = declare_univ u g in
  let g = declare_univ v g in
  match compare g u v with
    | NLE -> 
	(match compare g v u with
           | LT -> error_inconsistency()
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
    | LT -> error_inconsistency()
    | LE -> merge g u v
    | NLE -> 
	(match compare g v u with
           | LT -> error_inconsistency()
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
    | EQ -> error_inconsistency()
    | NLE -> 
	(match compare g v u with
           | NLE -> setlt g u v
           | _ -> error_inconsistency())

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

let enforce_geq u v c =
  match u with
    | Variable u -> (match v with
	| Variable v -> Constraint.add (v,Leq,u) c
	| Max (l1, l2) ->
	    let d = List.fold_right (fun v -> Constraint.add (v,Leq,u)) l1 c in
	    List.fold_right (fun v -> Constraint.add (v,Lt,u)) l2 d) 
    | Max _ -> anomaly "A universe bound can only be a variable"

let enforce_eq u v c =
  match (u,v) with
    | Variable u, Variable v -> Constraint.add (u,Eq,v) c
    | _ -> anomaly "A universe comparison can only happen between variables"

let merge_constraints c g =
  Constraint.fold enforce_constraint c g

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

module Huniv =
  Hashcons.Make(
    struct
      type t = universe
      type u = Names.dir_path -> Names.dir_path
      let hash_aux hdir u = { u with u_mod=hdir u.u_mod }
      let hash_sub hdir = function
	| Variable u -> Variable (hash_aux hdir u)
	| Max (gel,gtl) ->
	    Max (List.map (hash_aux hdir) gel, List.map (hash_aux hdir) gtl)
      let equal u v =
	match u, v with
	  | Variable u, Variable v -> u == v
	  | Max (gel,gtl), Max (gel',gtl') ->
	      (list_for_all2eq (==) gel gel') &&
              (list_for_all2eq (==) gtl gtl')
	  | _ -> false
      let hash = Hashtbl.hash
    end)

let hcons1_univ u =
  let _,_,hdir,_,_,_ = Names.hcons_names() in
  Hashcons.simple_hcons Huniv.f hdir u

