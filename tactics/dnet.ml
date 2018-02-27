(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Generic dnet implementation over non-recursive types *)

module type Datatype =
sig
  type 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val map2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
  val fold : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
  val fold2 : ('a -> 'b -> 'c -> 'a)  -> 'a -> 'b t -> 'c t -> 'a
  val compare : unit t -> unit t -> int
  val terminal : 'a t -> bool
  val choose : ('a -> 'b) -> 'a t -> 'b
end

module type S =
sig
  type t
  type ident
  type meta
  type 'a structure
  module Idset : Set.S with type elt=ident
  type term_pattern =
    | Term of term_pattern structure
    | Meta of meta
  val empty : t
  val add : t -> term_pattern -> ident -> t
  val find_all : t -> Idset.t
  val fold_pattern :
    ('a -> (Idset.t * meta * t) -> 'a) -> 'a -> term_pattern -> t -> Idset.t option * 'a
  val find_match : term_pattern -> t -> Idset.t
  val inter : t -> t -> t
  val union : t -> t -> t
  val map : (ident -> ident) -> (unit structure -> unit structure) -> t -> t
  val map_metas : (meta -> meta) -> t -> t
end

module Make =
  functor (T:Datatype) ->
  functor (Ident:Set.OrderedType) ->
  functor (Meta:Set.OrderedType) ->
struct

  type ident = Ident.t
  type meta = Meta.t

  type 'a structure = 'a T.t

  type term_pattern =
    | Term of term_pattern structure
    | Meta of meta

  module Idset = Set.Make(Ident)
  module Mmap = Map.Make(Meta)
  module Tmap = Map.Make(struct type t = unit structure
				let compare = T.compare end)

  type idset = Idset.t



  (* we store identifiers at the leaf of the dnet *)
  type node =
    | Node of t structure
    | Terminal of t structure * idset

  (* at each node, we have a bunch of nodes (actually a map between
     the bare node and a subnet) and a bunch of metavariables *)
  and t = Nodes of node Tmap.t * idset Mmap.t

  let empty : t = Nodes (Tmap.empty, Mmap.empty)

  (* the head of a data is of type unit structure *)
  let head w = T.map (fun c -> ()) w

  (* given a node of the net and a word, returns the subnet with the
     same head as the word (with the rest of the nodes) *)
  let split l (w:'a structure) : node * node Tmap.t =
    let elt : node = Tmap.find (head w) l in
    (elt, Tmap.remove (head w) l)

  let select l w = Tmap.find (head w) l

  let rec add (Nodes (t,m):t) (w:term_pattern) (id:ident) : t =
    match w with Term w ->
      ( try
	  let (n,tl) = split t w in
	  let new_node = match n with
	    | Terminal (e,is) -> Terminal (e,Idset.add id is)
	    | Node e -> Node (T.map2 (fun t p -> add t p id)  e w) in
	  Nodes ((Tmap.add (head w) new_node tl), m)
	with Not_found ->
	  let new_content = T.map (fun p -> add empty p id) w in
	  let new_node =
	    if T.terminal w then
	      Terminal (new_content, Idset.singleton id)
	    else Node new_content in
	  Nodes ((Tmap.add (head w) new_node t), m) )
      | Meta i ->
	  let m =
	    try Mmap.add i (Idset.add id (Mmap.find i m)) m
	    with Not_found -> Mmap.add i (Idset.singleton id) m in
	  Nodes (t, m)

  let add t w id = add t w id

  let rec find_all (Nodes (t,m)) : idset =
    Idset.union
      (Mmap.fold (fun _ -> Idset.union) m Idset.empty)
      (Tmap.fold
	 ( fun _ n acc ->
	     let s2 = match n with
	       | Terminal (_,is) -> is
	       | Node e -> T.choose find_all e in
	     Idset.union acc s2
	 ) t Idset.empty)

(*   (\* optimization hack: Not_found is caught in fold_pattern *\) *)
(*   let fast_inter s1 s2 = *)
(*     if Idset.is_empty s1 || Idset.is_empty s2 then raise Not_found *)
(*     else Idset.inter s1 s2 *)

(*   let option_any2 f s1 s2 = match s1,s2 with *)
(*     | Some s1, Some s2 -> f s1 s2 *)
(*     | (Some s, _ | _, Some s) -> s *)
(*     | _ -> raise Not_found *)

(*   let fold_pattern ?(complete=true) f acc pat dn = *)
(*     let deferred = ref [] in *)
(*     let leafs,metas = ref None, ref None in *)
(*     let leaf s = leafs := match !leafs with *)
(*       | None -> Some s *)
(*       | Some s' -> Some (fast_inter s s') in *)
(*     let meta s = metas := match !metas with *)
(*       | None -> Some s *)
(*       | Some s' -> Some (Idset.union s s') in *)
(*     let defer c = deferred := c::!deferred in *)
(*     let rec fp_rec (p:term_pattern) (Nodes(t,m) as dn:t) = *)
(*       Mmap.iter (fun _ -> meta) m; (\* TODO: gérer patterns nonlin ici *\) *)
(*       match p with *)
(* 	| Meta m -> defer (m,dn) *)
(* 	| Term w -> *)
(* 	    try match select t w with *)
(* 	      | Terminal (_,is) -> leaf is *)
(* 	      | Node e -> *)
(* 		  if complete then T.fold2 (fun _ -> fp_rec) () w e else *)
(* 		    if T.fold2 *)
(* 		      (fun b p dn -> match p with *)
(* 			 | Term _ -> fp_rec p dn; false *)
(* 			 | Meta _ -> b *)
(* 		      ) true w e *)
(* 		    then T.choose (T.choose fp_rec w) e *)
(* 	    with Not_found -> *)
(* 	      if Mmap.is_empty m then raise Not_found else () *)
(*     in try *)
(*       fp_rec pat dn; *)
(*       (try Some (option_any2 Idset.union !leafs !metas) with Not_found -> None), *)
(*       List.fold_left (fun acc (m,dn) -> f m dn acc) acc !deferred *)
(*     with Not_found -> None,acc *)

  (* Sets with a neutral element for inter *)
  module OSet (S:Set.S) = struct
    type t = S.t option
    let union s1 s2 : t = match s1,s2 with
      | (None, _ | _, None) -> None
      | Some a, Some b -> Some (S.union a b)
    let inter s1 s2 : t = match s1,s2 with
      | (None, a | a, None) -> a
      | Some a, Some b -> Some (S.inter a b)
    let is_empty : t -> bool = function 
      | None -> false
      | Some s -> S.is_empty s
    (* optimization hack: Not_found is caught in fold_pattern *)
    let fast_inter s1 s2 =
      if is_empty s1 || is_empty s2 then raise Not_found
      else let r = inter s1 s2 in 
      if is_empty r then raise Not_found else r
    let full = None
    let empty = Some S.empty
  end

  module OIdset = OSet(Idset)

  let fold_pattern ?(complete=true) f acc pat dn =
    let deferred = ref [] in
    let defer c = deferred := c::!deferred in

    let rec fp_rec metas p (Nodes(t,m) as dn:t) =
      (* TODO gérer les dnets non-linéaires *)
      let metas = Mmap.fold (fun _ -> Idset.union) m metas in
      match p with 
	| Meta m -> defer (metas,m,dn); OIdset.full
	| Term w ->
	    let curm = Mmap.fold (fun _ -> Idset.union) m Idset.empty in
	    try match select t w with
	      | Terminal (_,is) -> Some (Idset.union curm is)
	      | Node e -> 
		  let ids = if complete then T.fold2
		    (fun acc w e ->
		       OIdset.fast_inter acc (fp_rec metas w e)
		    ) OIdset.full w e 
		  else
		    let (all_metas, res) = T.fold2
		      (fun (b,acc) w e -> match w with
			 | Term _ -> false, OIdset.fast_inter acc (fp_rec metas w e)
			 | Meta _ -> b, acc
		      ) (true,OIdset.full) w e in
		    if all_metas then T.choose (T.choose (fp_rec metas) w) e
		    else res in
		  OIdset.union ids (Some curm)
	    with Not_found -> 
	      if Idset.is_empty metas then raise Not_found else Some curm in
    let cand = 
      try fp_rec Idset.empty pat dn
      with Not_found -> OIdset.empty in
    let res = List.fold_left f acc !deferred in
    cand, res

  (* intersection of two dnets. keep only the common pairs *)
  let rec inter (t1:t) (t2:t) : t =
    let inter_map f (Nodes (t1,m1):t) (Nodes (t2,m2):t) : t =
      Nodes
	(Tmap.fold
	   ( fun k e acc ->
	       try Tmap.add k (f e (Tmap.find k t2)) acc
	       with Not_found -> acc
	   ) t1 Tmap.empty,
	 Mmap.fold
	   ( fun m s acc ->
	       try Mmap.add m (Idset.inter s (Mmap.find m m2)) acc
	       with Not_found -> acc
	   ) m1 Mmap.empty
	) in
    inter_map
      (fun n1 n2 -> match n1,n2 with
	 | Terminal (e1,s1), Terminal (_,s2) -> Terminal (e1,Idset.inter s1 s2)
	 | Node e1, Node e2 -> Node (T.map2 inter e1 e2)
	 | _ -> assert false
      ) t1 t2

  let rec union (t1:t) (t2:t) : t =
    let union_map f (Nodes (t1,m1):t) (Nodes (t2,m2):t) : t =
      Nodes
	(Tmap.fold
	   ( fun k e acc ->
	       try Tmap.add k (f e (Tmap.find k acc)) acc
	       with Not_found -> Tmap.add k e acc
	   ) t1 t2,
	 Mmap.fold
	   ( fun m s acc ->
	       try Mmap.add m (Idset.inter s (Mmap.find m acc)) acc
	       with Not_found -> Mmap.add m s acc
	   ) m1 m2
	) in
    union_map
      (fun n1 n2 -> match n1,n2 with
	 | Terminal (e1,s1), Terminal (_,s2) -> Terminal (e1,Idset.union s1 s2)
	 | Node e1, Node e2 -> Node (T.map2 union e1 e2)
	 | _ -> assert false
      ) t1 t2

  let find_match (p:term_pattern) (t:t) : idset =
    let metas = ref Mmap.empty in
    let (mset,lset) = fold_pattern ~complete:false
      (fun acc (mset,m,t) ->
	 let all = OIdset.fast_inter acc
	   (Some(let t = try inter t (Mmap.find m !metas) with Not_found -> t in
		 metas := Mmap.add m t !metas;
		 find_all t)) in
	 OIdset.union (Some mset) all
      ) None p t in
    Option.get (OIdset.inter mset lset)

  let fold_pattern f acc p dn = fold_pattern ~complete:true f acc p dn

  let idset_map f is = Idset.fold (fun e acc -> Idset.add (f e) acc) is Idset.empty
  let tmap_map f g m = Tmap.fold (fun k e acc -> Tmap.add (f k) (g e) acc) m Tmap.empty

  let rec map sidset sterm (Nodes (t,m)) : t =
    let snode = function
      | Terminal (e,is) -> Terminal (e,idset_map sidset is)
      | Node e -> Node (T.map (map sidset sterm) e) in
    Nodes (tmap_map sterm snode t, Mmap.map (idset_map sidset) m)

  let rec map_metas f (Nodes (t, m)) : t =
    let f_node = function
      | Terminal (e, is) -> Terminal (T.map (map_metas f) e, is)
      | Node e -> Node (T.map (map_metas f) e)
    in
    let m' = Mmap.fold (fun m s acc -> Mmap.add (f m) s acc) m Mmap.empty in
    let t' = Tmap.fold (fun k n acc -> Tmap.add k (f_node n) acc) t Tmap.empty in
    Nodes (t', m')

end
