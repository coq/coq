(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(* This file implements the basic congruence-closure algorithm by *)
(* Downey,Sethi and Tarjan. *)

open Names
open Term

let init_size=251
  
type term=Symb of constr|Appli of term*term


(* Basic Union-Find algo w/o path compression *)
    
module UF = struct
  type tag=Congr|Ax of identifier
      
  type cl=Rep of int*(int list)|Eqto of int*(int*int*tag)

  type vertex=Leaf|Node of (int*int) 

  type t=(int ref)*((int,(cl*vertex*term)) Hashtbl.t)
	
  let empty ()=(((ref 0),(Hashtbl.create init_size)):t)
   	   
  let add_lst i t ((a,m):t)=
    match Hashtbl.find m i with
      ((Rep(l,lst)),v,trm)->Hashtbl.replace m i ((Rep((l+1),(t::lst))),v,trm)
    | _ ->failwith "add_lst: not a representative"
	  
  let rec find ((a,m):t) i=
    let (cl,_,_)=Hashtbl.find m i in
    match cl with
      Rep(_,_) -> i
    | Eqto(j,_) ->find (a,m) j
	  
  let list ((a,m):t) i=
    match Hashtbl.find m i with
      ((Rep(_,lst)),_,_)-> lst
    | _ ->failwith "list: not a class"
	  
  let size ((a,m):t) i=
    match Hashtbl.find m i with
      ((Rep (l,_)),_,_) -> l
    | _ ->failwith "size: not a class"
	  
  let signature ((a,m):t) i=
    let (_,v,_)=Hashtbl.find m i in
    match v with
      Node(j,k)->(find (a,m) j,find (a,m) k)
    | _ ->failwith "signature: not a node"

  let nodes ((a,m):t)=  (* cherche les noeuds binaires *)
    Hashtbl.fold (fun i (_,v,_) l->match v with Node (_,_)->i::l|_->l) m [] 

  let rec add t (a,m) syms = 
    try Hashtbl.find syms t with Not_found ->
	match t with
	  Symb s -> 
	    let b= !a in incr a;
	    Hashtbl.add m b ((Rep (0,[])),Leaf,t);
	    Hashtbl.add syms t b;
	    b
	| Appli (t1,t2) -> 
	    let i1=add t1 (a,m) syms and i2=add t2 (a,m) syms in
	    let b= !a in incr a;
	    add_lst (find (a,m) i1) b (a,m);
            add_lst (find (a,m) i2) b (a,m);
	    Hashtbl.add m b ((Rep (0,[])),(Node(i1,i2)),t);
	    Hashtbl.add syms t b;
	    b
	      
  let union ((a,m):t) i1 i2 t=
    let (cl1,v1,t1)=(Hashtbl.find m i1) and 
	(cl2,v2,t2)=(Hashtbl.find m i2) in
    match cl1,cl1 with
      ((Rep (l1,lst1)),(Rep (l2,lst2))) -> 
	Hashtbl.replace m i2 ((Eqto (i1,t)),v2,t2);
	Hashtbl.replace m i1 ((Rep((l2+l1),(lst2@lst1))),v1,t1)
    | _ ->failwith "union: not classes"
	  
	  
end    
    
(* Signature table *)

module ST=struct
  
(* l: sign -> term r: term -> sign *)
	
  type t = ((int*int,int) Hashtbl.t) * ((int,int*int) Hashtbl.t)
	
  let empty ()=((Hashtbl.create init_size),(Hashtbl.create init_size))
      
  let enter t sign ((l,r) as st:t)=
    if Hashtbl.mem l sign then 
	failwith "enter: signature already entered"
    else 
	Hashtbl.replace l sign t;
	Hashtbl.replace r t sign
	  
  let query sign ((l,r):t)=Hashtbl.find l sign
	  
  let delete t ((l,r) as st:t)=
    try let sign=Hashtbl.find r t in
	Hashtbl.remove l sign;
	Hashtbl.remove r t
    with
	Not_found -> ()

  let rec delete_list l st=
    match l with
      []->()
    | t::q -> delete t st;delete_list q st
	  
end
    
let rec combine_rec uf st=function 
    []->[]
  | v::pending->
      let combine=(combine_rec uf st pending) in
      let s=UF.signature uf v in
      try (v,(ST.query s st))::combine with
	Not_found->
	  ST.enter v s st;combine
	    
let rec process_rec uf st=function
    []->[] 
  | (v,w)::combine->
      let pending=process_rec uf st combine in
      let i=UF.find uf v 
      and j=UF.find uf w in
      if (i==j)|| ((Hashtbl.hash i)=(Hashtbl.hash j) && (i=j)) then 
	pending 
      else
	if (UF.size uf i)<(UF.size uf j) then
	  let l=UF.list uf i in
	  UF.union uf j i (v,w,UF.Congr);
	  ST.delete_list l st;
	  l@pending
	else
	  let l=UF.list uf j in
	  UF.union uf i j (w,v,UF.Congr);
	  ST.delete_list l st;
	  l@pending
	  
let rec cc_rec uf st=function
    []->()
  | pending->
      let combine=combine_rec uf st pending in
      let pending0=process_rec uf st combine in
      (cc_rec uf st pending0)
	
let cc uf=(cc_rec uf (ST.empty ()) (UF.nodes uf))

let rec make_uf syms=function
    []->(UF.empty ())
  | (ax,(v,w))::q->
      let uf=make_uf syms q in
      let i1=UF.add v uf syms in
      let i2=UF.add w uf syms in
      UF.union uf (UF.find uf i2) (UF.find uf i1) (i1,i2,(UF.Ax ax));
      uf
	
let decide_prb (axioms,(v,w))=
  let syms=Hashtbl.create init_size in
  let uf=make_uf syms axioms in
  let i1=UF.add v uf syms in
  let i2=UF.add w uf syms in
  cc uf;
  (UF.find uf i1)=(UF.find uf i2)





    
    
















