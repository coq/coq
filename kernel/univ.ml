(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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
open Names

type universe = { u_mod : module_path; u_num : int }

let universe_ord x y =
  let c = x.u_num - y.u_num in
  if c <> 0 then c else compare x.u_mod y.u_mod
  
module UniverseOrdered = struct
  type t = universe
  let compare = universe_ord
end

let string_of_univ u = 
  (string_of_modpath u.u_mod)^"."^(string_of_int u.u_num)

let pr_uni u =
  [< pr_modpath u.u_mod ; 'sTR"." ; 'iNT u.u_num >]

let dummy_univ = 
  { u_mod = MPsid (msid_of_string "dummy univ"); 
    u_num = 0 } (* for prover terms *)

let implicit_univ = 
  { u_mod = MPsid (msid_of_string "implicit univ"); 
    u_num = 0 }

let current_module = ref top_path

let set_module m = current_module := m

let with_module mp f x = 
  let old_module = !current_module in
    current_module := mp;
    try
      let result = f x in
	current_module := old_module;
	result
    with e ->
      current_module := old_module;
      raise e

let new_univ = 
  let univ_gen = ref 0 in
  (fun sp -> incr univ_gen; { u_mod = !current_module; u_num = !univ_gen })

(* Comparison on this type is pointer equality *)
type canonical_arc =
    { univ: universe; gt: universe list; ge: universe list }

let arc_ord {univ=u1} {univ=u2} = universe_ord u1 u2

let terminal u = {univ=u; gt=[]; ge=[]}

(* A universe is either an alias for another one, or a canonical one,
   for which we know the universes that are smaller *)
type univ_entry =
    Canonical of canonical_arc
  | Equiv of universe * universe

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

(* The universes of Prop and Set: Type_0, Type_1 and the
   resulting graph. *)
let (initial_universes,prop_univ,prop_univ_univ) =
  let prop_ln = MPsid (msid_of_string "prop_univ") in
  let u = { u_mod = prop_ln; u_num = 0 } in
  let su = { u_mod = prop_ln; u_num = 1 } in
  let g = enter_arc (terminal u) UniverseMap.empty in
  let g = enter_arc {univ=su; gt=[u]; ge=[]} g in
  (g,u,su)

(* Every universe has a unique canonical arc representative *)

(* repr : universes -> universe -> canonical_arc *)
(* canonical representative : we follow the Equiv links *)
let repr g u = 
  let rec repr_rec u =
    let a =
      try UniverseMap.find u g
      with Not_found -> anomalylabstrm "Univ.repr"
	  [< 'sTR"Universe "; pr_uni u; 'sTR" undefined" >] 
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

(* collect_eq : *)
let collect_eq g arcu = 
  let check_repr v _ l = if (repr g v)==arcu then v::l else l in
  UniverseMap.fold check_repr g []

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

type univ_constraint = universe * constraint_type * universe

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
let enforce_geq u v c = Constraint.add (u,Geq,v) c
let enforce_eq u v c = Constraint.add (u,Eq,v) c

let merge_constraints c g =
  Constraint.fold enforce_constraint c g


(* problem : 
   in oldg: u > v, v cannonical,
   in newg: v=w, w new
   v does not apprear on the > list of u any more
   implemented solution : 
   check if the new list is smaller (and not equal) than the old list
*)

(* TODO: sprawdzanie rownosci jest za drogie!
   trzeba zrobic jeden przejazd po oldg i newg, wyznaczajacy 
   rownoczesnie rownych dla kozdego z top_univ
   Map.S (univ -> univ list "jemu rowne")
   init = "old_univ -> []"
   i potem jeden fold g, ktory dla kazdego u w g sprawdza, czy 
   (repr u g) jest w mapie i jesli tak, to sie mu dodaje do listy

   a funkcje collect_eq wyrzucic
*)   

let merge_module_constraints mp c oldg = 
  let newg = merge_constraints c oldg 
  in

  let select c l = match c with
      (u,Gt,_) -> u::l
    | (u,Geq,_) -> u::l
    | (u,Eq,v) -> u::v::l
  in
  let old_only_univ u = u.u_mod <> mp in
  let top_univ = 
    List.filter old_only_univ (Constraint.fold select c []) 
  in  

  let old_only_arc {univ=u} = u.u_mod <> mp in
  let filter_old = List.filter old_only_arc in
  let collect_select g u filter_arc filter_univ = 
    let arcu = repr g u in
    let gtgeq = collect g arcu in
    let gt = List.sort arc_ord (filter_arc (fst gtgeq))
    and geq = List.sort arc_ord (filter_arc (snd gtgeq))
    and eq = List.sort universe_ord (filter_univ (collect_eq g arcu))
    in
      (gt, geq, eq)
  in
  let rec check_sorted_lists oldl newl = match oldl, newl with
      _, [] -> ()
    | [],_ -> error_inconsistency ()
    | oh::_, nh::_ when oh!=nh -> error_inconsistency ()
    | _::ol,_::nl -> check_sorted_lists ol nl
  in
  let check_univ u = 
    let oldgt,oldgeq,oldeq = 
      collect_select oldg u (fun l->l) (fun l->l)
    in
    let newgt,newgeq,neweq = 
      collect_select newg u 
	(List.filter old_only_arc) 
	(List.filter old_only_univ) 
    in
      check_sorted_lists oldgt newgt;
      check_sorted_lists oldgeq newgeq; 
      check_sorted_lists oldeq neweq
  in
    List.iter check_univ top_univ;
    newg
      
(* Returns a fresh universe, juste above u. Does not create new universes
   for Type_0 (the sort of Prop and Set).
   Used to type the sort u. *)
let super u = 
  if u == prop_univ then 
    prop_univ_univ, Constraint.empty
  else
    let v = new_univ () in
    let c = Constraint.singleton (v,Gt,u) in
    v,c

(* Returns the least upper bound of universes u and v. If they are not
   constrained, then a new universe is created.
   Used to type the products. *)
let sup u v g = 
  let g = declare_univ u g in
  let g = declare_univ v g in
  match compare g u v with
    | NGE -> 
	(match compare g v u with
           | NGE -> 
	       let w = new_univ () in
	       let c = Constraint.add (w,Geq,u) 
			 (Constraint.singleton (w,Geq,v)) in
	       w, c
           | _ -> v, Constraint.empty)
    | _ -> u, Constraint.empty


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
  | Canonical {univ=u; gt=gt; ge=ge} -> 
      hOV 2
        [< pr_uni u; 'sPC;
           prlist_with_sep pr_spc (fun v -> [< 'sTR">"; pr_uni v >]) gt;
           prlist_with_sep pr_spc (fun v -> [< 'sTR">="; pr_uni v >]) ge
        >]
  | Equiv (u,v) -> 
      [< pr_uni u ; 'sTR"=" ; pr_uni v >]

let pr_universes g =
  let graph = UniverseMap.fold (fun k a l -> (k,a)::l) g [] in
  prlist_with_sep pr_fnl (function (_,a) -> pr_arc a) graph
    

(* Dumping constrains to a file *)

let dump_universes output g = 
  let dump_arc _ = function
    | Canonical {univ=u; gt=gt; ge=ge} -> 
	let u_str = string_of_univ u in
	  List.iter 
	    (fun v -> 
	       Printf.fprintf output "%s > %s ;\n" u_str (string_of_univ v)) 
	    gt;
	  List.iter 
	    (fun v -> 
	       Printf.fprintf output "%s >= %s ;\n" u_str (string_of_univ v)) 
	    ge
    | Equiv (u,v) ->
	Printf.fprintf output "%s = %s ;\n" (string_of_univ u) (string_of_univ v)
  in
    UniverseMap.iter dump_arc g 

module Huniv =
  Hashcons.Make(
    struct
      type t = universe
      type u = string -> string
      let hash_sub hstr {u_mod=ln; u_num=n} = 
	{u_mod=(todo "Univ.Huniv"; ln); u_num=n}
      let equal {u_mod=ln1; u_num=n1} {u_mod=ln2; u_num=n2} =
	ln1==ln2 & n1=n2
      let hash = Hashtbl.hash
    end)


let hcons1_univ u = u (* todo *)
