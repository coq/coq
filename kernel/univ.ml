
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

type universe = { u_sp : section_path; u_num : int }

let universe_ord x y =
  let c = x.u_num - y.u_num in
  if c <> 0 then c else sp_ord x.u_sp y.u_sp
  
module UniverseOrdered = struct
  type t = universe
  let compare = universe_ord
end

let pr_uni u = [< 'sTR(string_of_path u.u_sp) ; 'sTR"." ; 'iNT u.u_num >]

let dummy_sp = make_path ["univ"] (id_of_string "dummy") OBJ
let dummy_univ = {u_sp = dummy_sp; u_num = 0} (* for prover terms *)

let new_univ = 
  let univ_gen = ref 0 in
  (fun sp -> incr univ_gen; { u_sp = sp; u_num = !univ_gen })

type relation = 
  | Greater of bool * universe * relation (* if bool then > else >= *)
  | Equiv of universe
  | Terminal

module UniverseMap = Map.Make(UniverseOrdered)

type arc = Arc of universe * relation

type universes = arc UniverseMap.t

exception UniverseInconsistency

type constraint_function = 
    universe -> universe -> universes -> universes

(* in Arc(u,Greater(b,v,r))::arcs, we have u>v if b, and u>=v if not b, 
   and r is the next relation pertaining to u; this relation may be
   Greater or Terminal. *)
		   
let enter_arc a g =
  let Arc(i,_) = a in
  UniverseMap.add i a g

let declare_univ u g =
  if not (UniverseMap.mem u g) then
    UniverseMap.add u (Arc(u,Terminal)) g
  else
    g

(* The universes of Prop and Set: Type_0, Type_1 and Type_2, and the
   resulting graph. *)
let (initial_universes,prop_univ,prop_univ_univ,prop_univ_univ_univ) =
  let prop_sp = make_path ["univ"] (id_of_string "prop_univ") OBJ in
  let u = { u_sp = prop_sp; u_num = 0 } in
  let su = { u_sp = prop_sp; u_num = 1 } in
  let ssu = { u_sp = prop_sp; u_num = 2 } in
  let g = enter_arc (Arc(u,Terminal)) UniverseMap.empty in
  let g = enter_arc (Arc(su,Terminal)) g in
  let g = enter_arc (Arc(ssu,Terminal)) g in
  let g = enter_arc (Arc(su,Greater(true,u,Terminal))) g in
  let g = enter_arc (Arc(ssu,Greater(true,su,Terminal))) g in
  (g,u,su,ssu)

(* Every universe has a unique canonical arc representative *)

(* repr : universes -> universe -> arc *)
(* canonical representative : we follow the Equiv links *)
let repr g u = 
  let rec repr_rec u =
    let arc =
      try UniverseMap.find u g
      with Not_found -> anomalylabstrm "Impuniv.repr"
	  [< 'sTR"Universe "; pr_uni u; 'sTR" undefined" >] 
    in
    match arc with 
      | Arc(_,Equiv(v)) -> repr_rec v
      | _ -> arc
  in
  repr_rec u

let can g = List.map (repr g)

(* transitive closure : we follow the Greater links *)
(* close : relation -> universe list * universe list *)
let close = 
  let rec closerec ((u,v) as pair) = function
    | Terminal -> pair
    | Greater(true,v_0,r)  -> closerec (v_0::u,v) r
    | Greater(false,v_0,r) -> closerec (u,v_0::v) r
    | _ -> anomaly "Wrong universe structure"
  in 
  closerec ([],[]) 

(* reprgeq : arc -> arc list *)
(* All canonical arcv such that arcu>=arcc with arcv#arcu *)
let reprgeq g (Arc(_,ru) as arcu) =
  let (_,v) = close ru in
  let rec searchrec w = function
    | [] -> w
    | v_0 :: v ->
	let arcv = repr g v_0 in
        if List.memq arcv w || arcu=arcv then 
	  searchrec w v
        else 
	  searchrec (arcv :: w) v
  in 
  searchrec [] v

(* collect : arc -> arc list * arc list *)
(* collect u = (V,W) iff V={v canonical | u>v} W={w canonical | u>=w}-V *)
(* i.e. collect does the transitive closure of what is known about u *)
let collect g u = 
  let rec coll_rec v w = function
    | [],[] -> (v,list_subtractq w v)
    | (Arc(_,rv) as arcv)::v',w' ->
	if List.memq arcv v then 
	  coll_rec v w (v',w')
	else
          let (gt,geq) = close rv in
          coll_rec (arcv::v) w ((can g (gt@geq))@v',w')
    | [],(Arc(_,rw) as arcw)::w' -> 
	if (List.memq arcw v) or (List.memq arcw w) then 
	  coll_rec v w ([],w')
	else
          let (gt,geq) = close rw in
          coll_rec v (arcw::w) (can g gt, (can g geq)@w')
  in 
  coll_rec [] [] ([],[u])

type order = EQ | GT | GE | NGE

(* compare : universe -> universe -> order *)
let compare g u v = 
  let arcu = repr g u 
  and arcv = repr g v in
  if arcu=arcv then 
    EQ
  else 
    let (v,w) = collect g arcu in
    if List.memq arcv v then 
      GT
    else if List.memq arcv w then 
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

(* between : universe -> arc -> arc list *)
(* we assume  compare(u,v) = GE with v canonical    *)
(* between u v = {w|u>=w>=v, w canonical}          *)     
let between g u arcv = 
  let rec explore (memo,l) arcu = 
    try 
      memo,list_unionq (List.assq arcu memo) l (* when memq arcu memo *)
    with Not_found ->
      let w = reprgeq g arcu in
      let (memo',sols) = List.fold_left explore (memo,[]) w in
      let sols' = if sols=[] then [] else arcu::sols in
      ((arcu,sols')::memo', list_unionq sols' l) 
  in
  snd (explore ([(arcv,[arcv])],[]) (repr g u))

(* Note: hd(between u v) = repr u  *)
(* between is the most costly operation *)

(* setgt : universe -> universe -> unit *)
(* forces u > v *)
let setgt g u v =
  let Arc(u',ru) = repr g u in
  enter_arc (Arc(u',Greater(true,v,ru))) g

(* checks that non-redondant *)
let setgt_if g u v = match compare g u v with
  | GT -> g
  | _ -> setgt g u v

(* setgeq : universe -> universe -> unit *)
(* forces u >= v *)
let setgeq g u v =
  let Arc(u',ru) = repr g u in
  enter_arc (Arc(u',Greater(false,v,ru))) g


(* checks that non-redondant *)
let setgeq_if g u v = match compare g u v with
  | NGE -> setgeq g u v
  | _ -> g

(* merge : universe -> universe -> unit *)
(* we assume  compare(u,v) = GE *)
(* merge u v  forces u ~ v with repr u as canonical repr *)
let merge g u v =
  match between g u (repr g v) with
    | Arc(u',_)::v ->
	let redirect (g,w,w') (Arc(v',rv)) =
       	  let v,v'_0 = close rv in
 	  let g' = enter_arc (Arc(v',Equiv(u'))) g in
 	  (g',list_unionq v w,v'_0@w') 
	in
	let (g',w,w') = List.fold_left redirect (g,[],[]) v in
	let g'' = List.fold_left (fun g -> setgt_if g u') g' w in
	let g''' = List.fold_left (fun g -> setgeq_if g u') g'' w' in
	g'''
    | [] -> anomaly "between"

(* merge_disc : universe -> universe -> unit *)
(* we assume  compare(u,v) = compare(v,u) = NGE *)
(* merge_disc u v  forces u ~ v with repr u as canonical repr *)
let merge_disc g u v =
  let (Arc(u',_), Arc(v',rv)) = (repr g u, repr g v) in
  let v,v'_0 = close rv in
  let g' = enter_arc (Arc(v',Equiv(u'))) g in
  let g'' = List.fold_left (fun g -> setgt_if g u') g' v in
  let g''' = List.fold_left (fun g -> setgeq_if g u') g'' v'_0 in
  g'''

(* Universe inconsistency: error raised when trying to enforce a relation
   that would create a cycle in the graph of universes. *)
let error_inconsistency () =
  raise UniverseInconsistency

(* enforcegeq : universe -> universe -> unit *)
(* enforcegeq u v will force u>=v if possible, will fail otherwise *)
let enforce_geq u v g =
  let g = declare_univ u g in
  let g = declare_univ v g in
  match compare g u v with
    | NGE -> 
	(match compare g v u with
           | GT -> error_inconsistency()
           | GE -> merge g v u
           | NGE -> setgeq g u v
           | EQ -> anomaly "compare")
    | _ -> g

(* enforceq : universe -> universe -> unit *)
(* enforceq u v will force u=v if possible, will fail otherwise *)
let enforce_eq u v g =
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
           | EQ -> anomaly "compare")

(* enforcegt u v will force u>v if possible, will fail otherwise *)
let enforce_gt u v g =
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

let enforce_relation g u = 
  let rec enfrec g = function
    | Terminal -> g
    | Equiv v -> enforce_eq u v g
    | Greater(false,v,r) -> enfrec (enforce_geq u v g) r
    | Greater(true,v,r) -> enfrec (enforce_gt u v g) r
  in 
  enfrec g
    

(* Merging 2 universe graphs *)
let merge_universes sp u1 u2 =
  UniverseMap.fold (fun _ (Arc(u,r)) g -> enforce_relation g u r) u1 u2


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
	       let w = new_univ u.u_sp in 
	       let g' = setgeq g w u in
	       w, setgeq g' w v
           | _ -> v, g)
    | _ -> u, g

(* Returns a fresh universe, juste above u. Does not create new universes
   for Type_0 (the sort of Prop and Set).
   Used to type the sort u. *)
let super u g = 
  if u == prop_univ then 
    prop_univ_univ, g
  else if u == prop_univ_univ then 
    prop_univ_univ_univ, g
  else
    let g = declare_univ u g in
    let v = new_univ u.u_sp in
    let g' = enter_arc (Arc(v,Greater(true,u,Terminal))) g in
    v,g'

(* Pretty-printing *)
let num_universes g =
  UniverseMap.fold (fun _ _ -> succ) g 0

let num_edges g =
  let reln_len = 
    let rec lenrec n = function
      | Terminal -> n
      | Equiv _ -> n+1
      | Greater(_,_,r) -> lenrec (n+1) r
    in 
    lenrec 0 
  in
  UniverseMap.fold (fun _ (Arc(_,r)) n -> n + (reln_len r)) g 0
    
let pr_reln u r = 
  let rec prec = function
    | Greater(true,v,r) -> 
	[< pr_uni u ; 'sTR">" ; pr_uni v ; 'fNL ; prec r >]
    | Greater(false,v,r) -> 
	[< pr_uni u ; 'sTR">=" ; pr_uni v ; 'fNL ; prec r >]
    | Equiv v -> 
	[< pr_uni u ; 'sTR"=" ; pr_uni v >]
    | Terminal -> [< >]
  in 
  prec r
    
let pr_universes g =
  let graph = UniverseMap.fold (fun k a l -> (k,a)::l) g [] in
  prlist_with_sep pr_fnl (function (_,Arc(u,r)) -> pr_reln u r) graph
    
