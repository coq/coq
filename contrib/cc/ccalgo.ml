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
  
type term=
    Symb of constr
  | Appli of term*term

type rule=
    Congruence
  | Axiom of identifier

type valid={lhs:int;rhs:int;rule:rule}

let congr_valid i j= {lhs=i;rhs=j;rule=Congruence}

let ax_valid i j id= {lhs=i;rhs=j;rule=Axiom id}

(* Basic Union-Find algo w/o path compression *)
    
module UF = struct

  type cl=Rep of int*(int list)|Eqto of int*valid

  type vertex=Leaf|Node of (int*int) 

  type node={clas:cl;vertex:vertex;term:term}    

  type t={mutable size:int;
	  map:(int,node) Hashtbl.t;
	  syms:(term,int) Hashtbl.t}
	
  let empty ():t={size=0;
		  map=Hashtbl.create init_size;
		  syms=Hashtbl.create init_size}

  let add_lst i t uf=
    let node=Hashtbl.find uf.map i in
      match node.clas with
	  Rep(l,lst)->Hashtbl.replace uf.map i 
	    {node with clas=Rep(l+1,t::lst)}
	| _ ->failwith "add_lst: not a representative"
	    
  let rec find uf i=
    match (Hashtbl.find uf.map i).clas with
	Rep(_,_) -> i
      | Eqto(j,_) ->find uf j
	  
  let list uf i=
    match (Hashtbl.find uf.map i).clas with
	Rep(_,lst)-> lst
      | _ ->failwith "list: not a class"
	  
  let size uf i=
    match (Hashtbl.find uf.map i).clas with
	Rep (l,_) -> l
      | _ ->failwith "size: not a class"

  let term uf i=(Hashtbl.find uf.map i).term

  let subterms uf i=
    match (Hashtbl.find uf.map i).vertex with
	Node(j,k) -> (j,k)
      | _ -> failwith "subterms: not a node"

  let signature uf i=
    match (Hashtbl.find uf.map i).vertex with
	Node(j,k)->(find uf j,find uf k)
      | _ ->failwith "signature: not a node"

  let nodes uf=  (* cherche les noeuds binaires *)
    Hashtbl.fold 
      (fun i node l->
	 match node.vertex with 
	     Node (_,_)->i::l
	   | _ ->l) uf.map [] 

  let next uf=
    let n=uf.size in uf.size<-n+1; n
	
  let rec add t uf= 
    try Hashtbl.find uf.syms t with 
	Not_found ->
	  let b=next uf in
	  let new_node=
	    match t with
		Symb s -> 
		  {clas=Rep (0,[]);
		   vertex=Leaf;
		   term=t}
	      | Appli (t1,t2) -> 
		  let i1=add t1 uf 
		  and i2=add t2 uf in
		    add_lst (find uf i1) b uf;
		    add_lst (find uf i2) b uf;
		    {clas=Rep (0,[]);
		     vertex=Node(i1,i2);
		     term=t}
      in
	    Hashtbl.add uf.map b new_node;
	    Hashtbl.add uf.syms t b;
	    b
	      
  let union uf i1 i2 t=
    let node1=(Hashtbl.find uf.map i1) 
    and node2=(Hashtbl.find uf.map i2) in
      match node1.clas,node2.clas with
	  Rep (l1,lst1),Rep (l2,lst2) -> 
	    Hashtbl.replace uf.map i2 {node2 with clas=Eqto (i1,t)};
	    Hashtbl.replace uf.map i1 
	      {node1 with clas=Rep(l2+l1,lst2@lst1)}
	| _ ->failwith "union: not classes"	  	  
	    
  let rec up_path uf i l=
    match (Hashtbl.find uf.map i).clas with
	Eqto(j,t)->up_path uf j (((i,j),t)::l)
      | Rep(_,_)->l

  let rec min_path=function
      ([],l2)->([],l2)
    | (l1,[])->(l1,[])
    | (((c1,t1)::q1),((c2,t2)::q2)) when c1=c2 -> min_path (q1,q2) 
    | cpl -> cpl
	
  let join_path uf i j=
    assert (find uf i=find uf j);
    min_path (up_path uf i [],up_path uf j [])
      
end    
    
(* Signature table *)

module ST=struct
  
  (* l: sign -> term r: term -> sign *)
	
  type t = {toterm:(int*int,int) Hashtbl.t;
	    tosign:(int,int*int) Hashtbl.t}
	
  let empty ()=
    {toterm=Hashtbl.create init_size;
     tosign=Hashtbl.create init_size}
      
  let enter t sign st=
    if Hashtbl.mem st.toterm sign then 
	failwith "enter: signature already entered"
    else 
	Hashtbl.replace st.toterm sign t;
	Hashtbl.replace st.tosign t sign
	  
  let query sign st=Hashtbl.find st.toterm sign
	  
  let delete t st=
    try let sign=Hashtbl.find st.tosign t in
	Hashtbl.remove st.toterm sign;
	Hashtbl.remove st.tosign t
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
      if i=j then 
	pending 
      else
	if (UF.size uf i)<(UF.size uf j) then
	  let l=UF.list uf i in
	  UF.union uf j i (congr_valid v w);
	  ST.delete_list l st;
	  l@pending
	else
	  let l=UF.list uf j in
	  UF.union uf i j (congr_valid w v);
	  ST.delete_list l st;
	  l@pending
	  
let rec cc_rec uf st=function
    []->()
  | pending->
      let combine=combine_rec uf st pending in
      let pending0=process_rec uf st combine in
      (cc_rec uf st pending0)
	
let cc uf=(cc_rec uf (ST.empty ()) (UF.nodes uf))

let rec make_uf=function
    []->(UF.empty ())
  | (ax,(v,w))::q->
      let uf=make_uf q in
      let i1=UF.add v uf in
      let i2=UF.add w uf in
      UF.union uf (UF.find uf i2) (UF.find uf i1) (ax_valid i1 i2 ax);
      uf
	





    
    
















