(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* Universes are stratified by a partial ordering $\ge$.
   Let $\~{}$ be the associated equivalence. We also have a strict ordering
   $>$ between equivalence classes, and we maintain that $>$ is acyclic,
   and contained in $\ge$ in the sense that $[U]>[V]$ implies $U\ge V$.

   At every moment, we have a finite number of universes, and we
   maintain the ordering in the presence of assertions $U>V$ and $U\ge V$.

   The equivalence $\~{}$ is represented by a tree structure, as in the
   union-find algorithm. The assertions $>$ and $\ge$ are represented by
   adjacency lists *)

open Pp
open Util

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

let string_of_univ = function
  | Variable u -> string_of_univ_level u
  | Max (gel,gtl) -> 
      "max("^
      (String.concat ","
	 ((List.map string_of_univ_level gel)@
	  (List.map (fun u -> "("^(string_of_univ_level u)^")+1") gtl)))^")"

let pr_uni_level u = str (string_of_univ_level u)

let pr_uni = function
  | Variable u -> 
      pr_uni_level u
  | Max (gel,gtl) ->
      str "max(" ++ 
      prlist_with_sep pr_coma pr_uni_level gel ++
      if gel <> [] & gtl <> [] then pr_coma () else mt () ++
      prlist_with_sep pr_coma
	(fun x -> str "(" ++ pr_uni_level x ++ str ")+1") gtl ++
      str ")"

(* Returns a fresh universe, juste above u. Does not create new universes
   for Type_0 (the sort of Prop and Set).
   Used to type the sort u. *)
let super = function
  | Variable u -> 
      Max ([],[u])
  | Max _ ->
      anomaly ("Cannot take the successor of a non variable universes:\n"^
       "you are probably typing a type already known to be the type\n"^
       "of a user-provided term; if you really need this, please report")

(* returns the least upper bound of universes u and v. If they are not
   constrained, then a new universe is created.
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
    { univ: universe_level; gt: universe_level list; ge: universe_level list }

let terminal u = {univ=u; gt=[]; ge=[]}

(* A universe is either an alias for another one, or a canonical one,
   for which we know the universes that are smaller *)
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

(* Every universe has a unique canonical arc representative *)

(* repr : universes -> universe -> canonical_arc *)
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

(* transitive closure : we follow the Greater links *)

(* collect : canonical_arc -> canonical_arc list * canonical_arc list *)
(* collect u = (V,W) iff V={v canonical | u>v} W={w canonical | u>=w}-V *)
(* i.e. collect does the transitive closure of what is known about u *)
let collect g arcu = 
  let rec coll_rec gt ge = function
    | [],[] -> (gt, list_subtractq ge gt)
    | arcv::gt', ge' ->
	if List.memq arcv gt then 
	  coll_rec gt ge (gt',ge')
	else
          coll_rec (arcv::gt) ge ((can g (arcv.gt@arcv.ge))@gt',ge')
    | [], arcw::ge' -> 
	if (List.memq arcw gt) or (List.memq arcw ge) then 
	  coll_rec gt ge ([],ge')
	else
          coll_rec gt (arcw::ge) (can g arcw.gt, (can g arcw.ge)@ge')
  in 
  coll_rec [] [] ([],[arcu])

(* reprgeq : canonical_arc -> canonical_arc list *)
(* All canonical arcv such that arcu>=arcc with arcv#arcu *)
let reprgeq g arcu =
  let rec searchrec w = function
    | [] -> w
    | v :: vl ->
	let arcv = repr g v in
        if List.memq arcv w || arcu==arcv then 
	  searchrec w vl
        else 
	  searchrec (arcv :: w) vl
  in 
  searchrec [] arcu.ge


(* between : universe -> canonical_arc -> canonical_arc list *)
(* between u v = {w|u>=w>=v, w canonical}          *)     
(* between is the most costly operation *)

let between g u arcv = 
  (* good are all w | u >= w >= v  *)
  (* bad are all w | u >= w ~>= v *)
    (* find good and bad nodes in {w | u >= w} *)
    (* explore b u = (b or "u is good") *)
  let rec explore ((good, bad, b) as input) arcu =
    if List.memq arcu good then
      (good, bad, true) (* b or true *)
    else if List.memq arcu bad then
      input    (* (good, bad, b or false) *)
    else 
      let childs = reprgeq g arcu in 
	(* are any children of u good ? *)
      let good, bad, b_childs = 
	List.fold_left explore (good, bad, false) childs 
      in
	if b_childs then
	  arcu::good, bad, true (* b or true *)
	else 
	  good, arcu::bad, b    (* b or false *)
  in
  let good,_,_ = explore ([arcv],[],false) (repr g u) in
    good
      
(* We assume  compare(u,v) = GE with v canonical (see compare below).
   In this case List.hd(between g u v) = repr u
   Otherwise, between g u v = [] 
 *)


type order = EQ | GT | GE | NGE

(* compare : universe -> universe -> order *)
let compare g u v = 
  let arcu = repr g u 
  and arcv = repr g v in
  if arcu==arcv then 
    EQ
  else 
    let (gt,geq) = collect g arcu in
    if List.memq arcv gt then 
      GT
    else if List.memq arcv geq then 
      GE
    else 
      NGE

(* Invariants : compare(u,v) = EQ <=> compare(v,u) = EQ
                compare(u,v) = GT or GE => compare(v,u) = NGE
                compare(u,v) = NGE => compare(v,u) = NGE or GE or GT

   Adding u>=v is consistent iff compare(v,u) # GT 
    and then it is redundant iff compare(u,v) # NGE
   Adding u>v is consistent iff compare(v,u) = NGE 
    and then it is redundant iff compare(u,v) = GT *)


(* setgt : universe -> universe -> unit *)
(* forces u > v *)
let setgt g u v =
  let arcu = repr g u in
  enter_arc {arcu with gt=v::arcu.gt} g

(* checks that non-redondant *)
let setgt_if g u v = match compare g u v with
  | GT -> g
  | _ -> setgt g u v

(* setgeq : universe -> universe -> unit *)
(* forces u >= v *)
let setgeq g u v =
  let arcu = repr g u in
  enter_arc {arcu with ge=v::arcu.ge} g


(* checks that non-redondant *)
let setgeq_if g u v = match compare g u v with
  | NGE -> setgeq g u v
  | _ -> g

(* merge : universe -> universe -> unit *)
(* we assume  compare(u,v) = GE *)
(* merge u v  forces u ~ v with repr u as canonical repr *)
let merge g u v =
  match between g u (repr g v) with
    | arcu::v -> (* arcu is chosen as canonical and all others (v) are *)
                 (* redirected to it *)
	let redirect (g,w,w') arcv =
 	  let g' = enter_equiv_arc arcv.univ arcu.univ g in
 	  (g',list_unionq arcv.gt w,arcv.ge@w') 
	in
	let (g',w,w') = List.fold_left redirect (g,[],[]) v in
	let g'' = List.fold_left (fun g -> setgt_if g arcu.univ) g' w in
	let g''' = List.fold_left (fun g -> setgeq_if g arcu.univ) g'' w' in
	g'''
    | [] -> anomaly "Univ.between"

(* merge_disc : universe -> universe -> unit *)
(* we assume  compare(u,v) = compare(v,u) = NGE *)
(* merge_disc u v  forces u ~ v with repr u as canonical repr *)
let merge_disc g u v =
  let arcu = repr g u in
  let arcv = repr g v in
  let g' = enter_equiv_arc arcv.univ arcu.univ g in
  let g'' = List.fold_left (fun g -> setgt_if g arcu.univ) g' arcv.gt in
  let g''' = List.fold_left (fun g -> setgeq_if g arcu.univ) g'' arcv.ge in
  g'''

(* Universe inconsistency: error raised when trying to enforce a relation
   that would create a cycle in the graph of universes. *)

exception UniverseInconsistency

let error_inconsistency () = raise UniverseInconsistency

(* enforcegeq : universe -> universe -> unit *)
(* enforcegeq u v will force u>=v if possible, will fail otherwise *)
let enforce_univ_geq u v g =
  let g = declare_univ u g in
  let g = declare_univ v g in
  match compare g u v with
    | NGE -> 
	(match compare g v u with
           | GT -> error_inconsistency()
           | GE -> merge g v u
           | NGE -> setgeq g u v
           | EQ -> anomaly "Univ.compare")
    | _ -> g

(* enforceq : universe -> universe -> unit *)
(* enforceq u v will force u=v if possible, will fail otherwise *)
let enforce_univ_eq u v g =
  let g = declare_univ u g in
  let g = declare_univ v g in
  match compare g u v with
    | EQ -> g
    | GT -> error_inconsistency()
    | GE -> merge g u v
    | NGE -> 
	(match compare g v u with
           | GT -> error_inconsistency()
           | GE -> merge g v u
           | NGE -> merge_disc g u v
           | EQ -> anomaly "Univ.compare")

(* enforcegt u v will force u>v if possible, will fail otherwise *)
let enforce_univ_gt u v g =
  let g = declare_univ u g in
  let g = declare_univ v g in
  match compare g u v with
    | GT -> g
    | GE -> setgt g u v
    | EQ -> error_inconsistency()
    | NGE -> 
	(match compare g v u with
           | NGE -> setgt g u v
           | _ -> error_inconsistency())

(*
let enforce_univ_relation g = function 
  | Equiv (u,v) -> enforce_univ_eq u v g
  | Canonical {univ=u; gt=gt; ge=ge} ->
      let g' = List.fold_right (enforce_univ_gt u) gt g in
      List.fold_right (enforce_univ_geq u) ge g'
*)

(* Merging 2 universe graphs *)
(*
let merge_universes sp u1 u2 =
  UniverseMap.fold (fun _ a g -> enforce_univ_relation g a) u1 u2
*)


(* Constraints and sets of consrtaints. *)

type constraint_type = Gt | Geq | Eq

type univ_constraint = universe_level * constraint_type * universe_level

let enforce_constraint cst g =
  match cst with
    | (u,Gt,v) -> enforce_univ_gt u v g
    | (u,Geq,v) -> enforce_univ_geq u v g
    | (u,Eq,v) -> enforce_univ_eq u v g


module Constraint = Set.Make(
  struct 
    type t = univ_constraint 
    let compare = Pervasives.compare 
  end)
		      
type constraints = Constraint.t

type constraint_function = 
    universe -> universe -> constraints -> constraints

let enforce_gt u v c = Constraint.add (u,Gt,v) c

let enforce_geq u v c =
  match u with
    | Variable u -> (match v with
	| Variable v -> Constraint.add (u,Geq,v) c
	| Max (l1, l2) ->
	    let d = List.fold_right (fun v -> Constraint.add (u,Geq,v)) l1 c in
	    List.fold_right (fun v -> Constraint.add (u,Gt,v)) l2 d) 
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
    | Canonical {gt=gt;ge=ge} -> List.length gt + List.length ge
  in
  UniverseMap.fold (fun _ a n -> n + (reln_len a)) g 0
    
let pr_arc = function 
  | Canonical {univ=u; gt=[]; ge=[]} ->
      mt ()
  | Canonical {univ=u; gt=gt; ge=ge} ->
      pr_uni_level u ++ str " " ++
      v 0
        (prlist_with_sep pr_spc (fun v -> str "> " ++ pr_uni_level v) gt ++
         prlist_with_sep pr_spc (fun v -> str ">= " ++ pr_uni_level v) ge) ++
      fnl ()
  | Equiv (u,v) -> 
      pr_uni_level u  ++ str " = " ++ pr_uni_level v ++ fnl ()

let pr_universes g =
  let graph = UniverseMap.fold (fun k a l -> (k,a)::l) g [] in
  prlist (function (_,a) -> pr_arc a) graph
    

(* Dumping constrains to a file *)

let dump_universes output g = 
  let dump_arc _ = function
    | Canonical {univ=u; gt=gt; ge=ge} -> 
	let u_str = string_of_univ_level u in
	  List.iter 
	    (fun v -> 
	       Printf.fprintf output "%s > %s ;\n" u_str
		 (string_of_univ_level v)) 
	    gt;
	  List.iter 
	    (fun v -> 
	       Printf.fprintf output "%s >= %s ;\n" u_str
		 (string_of_univ_level v)) 
	    ge
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
	      (List.for_all2 (==) gel gel') && (List.for_all2 (==) gtl gtl')
	  | _ -> false
      let hash = Hashtbl.hash
    end)

let hcons1_univ u =
  let _,hdir,_,_,_ = Names.hcons_names() in
  Hashcons.simple_hcons Huniv.f hdir u

