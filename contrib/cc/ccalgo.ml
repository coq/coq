(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* This file implements the basic congruence-closure algorithm by *)
(* Downey,Sethi and Tarjan. *)

open Util
open Names
open Term

let init_size=251

type pa_constructor=
    {head_constr: int;
     arity:int;
     nhyps:int;
     args:int list;
     term_head:int}


module PacMap=Map.Make(struct type t=int*int let compare=compare end) 

type term=
    Symb of constr
  | Appli of term*term
  | Constructor of constructor*int*int (* constructor arity+ nhyps *)

type rule=
    Congruence
  | Axiom of identifier
  | Injection of int*int*int*int (* terms+head+arg position *)

type equality = {lhs:int;rhs:int;rule:rule}

let swap eq=
  let swap_rule=match eq.rule with
      Congruence -> Congruence
    | Injection (i,j,c,a) -> Injection (j,i,c,a)
    | Axiom id -> anomaly "no symmetry for axioms"    
  in {lhs=eq.rhs;rhs=eq.lhs;rule=swap_rule}

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
	anomaly "enter: signature already entered"
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
    
(* Basic Union-Find algo w/o path compression *)
    
module UF = struct

module IndMap=Map.Make(struct type t=inductive let compare=compare end) 

  type representative=
      {mutable nfathers:int;
       mutable fathers:int list;
       mutable constructors:pa_constructor PacMap.t;
       mutable inductives:(int * int) IndMap.t}

  type cl = Rep of representative| Eqto of int*equality

  type vertex = Leaf| Node of (int*int) 

  type node = 
      {clas:cl;
       vertex:vertex;
       term:term;
       mutable node_constr: int PacMap.t}    

  type t={mutable size:int;
          map:(int,node) Hashtbl.t;
          syms:(term,int) Hashtbl.t;
	  sigtable:ST.t}

  let empty ():t={size=0;
		  map=Hashtbl.create init_size;
		  syms=Hashtbl.create init_size;
		  sigtable=ST.empty ()}

  let rec find uf i=
    match (Hashtbl.find uf.map i).clas with
	Rep _ -> i
      | Eqto (j,_) ->find uf j
	  
  let get_representative uf i=
    let node=Hashtbl.find uf.map i in
      match node.clas with
	  Rep r ->r
	| _ -> anomaly "get_representative: not a representative"

  let get_constructor uf i=
    match (Hashtbl.find uf.map i).term with
	Constructor (cstr,_,_)->cstr
      | _ -> anomaly "get_constructor: not a constructor"


  let fathers uf i=
    (get_representative uf i).fathers
	  
  let size uf i=
    (get_representative uf i).nfathers

  let add_father uf i t=
    let r=get_representative uf i in
      r.nfathers<-r.nfathers+1;
      r.fathers<-t::r.fathers 

  let pac_map uf i=
    (get_representative uf i).constructors  

  let pac_arity uf i sg=
    (PacMap.find sg (get_representative uf i).constructors).arity

  let add_node_pac uf i sg j=
    let node=Hashtbl.find uf.map i in
      if not (PacMap.mem sg node.node_constr) then
	node.node_constr<-PacMap.add sg j node.node_constr 
  
  let mem_node_pac uf i sg= 
    PacMap.find sg (Hashtbl.find uf.map i).node_constr
  
  exception Discriminable of int * int * int * int * t 

  let add_pacs uf i pacs =
    let rep=get_representative uf i in
    let pending=ref [] and combine=ref [] in 
    let add_pac sg pac=
      try  
	let opac=PacMap.find sg rep.constructors in
	  if (snd sg)>0 then () else
	    let tk=pac.term_head 
	    and tl=opac.term_head in
	    let rec f n lk ll q=
	      if n > 0 then match (lk,ll) with
		  k::qk,l::ql->
		    let eq=
		      {lhs=k;rhs=l;rule=Injection(tk,tl,pac.head_constr,n)} 
		    in f (n-1) qk ql (eq::q) 
		| _-> anomaly 
		    "add_pacs : weird error in injection subterms merge"
	      else q in
 	      combine:=f pac.nhyps pac.args opac.args !combine
      with Not_found -> (* Still Unknown Constructor *)
	rep.constructors <- PacMap.add sg pac rep.constructors;
	pending:=
	    (fathers uf (find uf pac.term_head)) @rep.fathers@ !pending;
	let (c,a)=sg in
	  if a=0 then
	    let (ind,_)=get_constructor uf c in  
	      try
		let th2,hc2=IndMap.find ind rep.inductives in
		  raise (Discriminable (pac.term_head,c,th2,hc2,uf)) 
	      with Not_found ->
		rep.inductives<-
		IndMap.add ind (pac.term_head,c) rep.inductives in
      PacMap.iter add_pac pacs;
      !pending,!combine
	
  let term uf i=(Hashtbl.find uf.map i).term
		  
  let subterms uf i=
    match (Hashtbl.find uf.map i).vertex with
	Node(j,k) -> (j,k)
      | _ -> anomaly "subterms: not a node"

  let signature uf i=
    let j,k=subterms uf i in (find uf j,find uf k)

  let nodes uf=  (* cherche les noeuds binaires *)
    Hashtbl.fold 
      (fun i node l->
	 match node.vertex with 
	     Node (_,_)->i::l
	   | _ ->l) uf.map [] 

  let next uf=
    let n=uf.size in uf.size<-n+1; n
	
  let new_representative pm im=
    {nfathers=0;
     fathers=[];
     constructors=pm;
     inductives=im}

  let rec add uf t= 
    try Hashtbl.find uf.syms t with 
	Not_found ->
	  let b=next uf in
	  let new_node=
	    match t with
		Symb s -> 
		  {clas=Rep (new_representative PacMap.empty IndMap.empty);
		   vertex=Leaf;term=t;node_constr=PacMap.empty}
	      | Appli (t1,t2) -> 
		  let i1=add uf t1 and i2=add uf t2 in
		    add_father uf (find uf i1) b;
		    add_father uf (find uf i2) b;
		    {clas=Rep (new_representative PacMap.empty IndMap.empty);
		     vertex=Node(i1,i2);term=t;node_constr=PacMap.empty}
	      | Constructor (c,a,n) ->
		  let pacs=
		    PacMap.add (b,a) 
		      {head_constr=b;arity=a;nhyps=n;args=[];term_head=b} 
		      PacMap.empty in
		  let inds=
		    if a=0 then
		      let (ind,_)=c in
			IndMap.add ind (b,b) IndMap.empty 
		    else IndMap.empty in
		    {clas=Rep (new_representative pacs inds);
		     vertex=Leaf;term=t;node_constr=PacMap.empty}
	  in
	    Hashtbl.add uf.map b new_node;
	    Hashtbl.add uf.syms t b;
	    b

  let link uf i j eq= (* links i -> j *)
    let node=Hashtbl.find uf.map i in 
      Hashtbl.replace uf.map i {node with clas=Eqto (j,eq)}
	      
  let union uf i1 i2 eq=
    let r1= get_representative uf i1 
    and r2= get_representative uf i2 in
      link uf i1 i2 eq;
      r2.nfathers<-r1.nfathers+r2.nfathers;
      r2.fathers<-r1.fathers@r2.fathers;
      add_pacs uf i2 r1.constructors 
	
  let rec down_path uf i l=
    match (Hashtbl.find uf.map i).clas with
	Eqto(j,t)->down_path uf j (((i,j),t)::l)
      | Rep _ ->l

  let rec min_path=function
      ([],l2)->([],l2)
    | (l1,[])->(l1,[])
    | (((c1,t1)::q1),((c2,t2)::q2)) when c1=c2 -> min_path (q1,q2) 
    | cpl -> cpl
	
  let join_path uf i j=
    assert (find uf i=find uf j);
    min_path (down_path uf i [],down_path uf j [])
      
end    
    
let rec combine_rec uf=function 
    []->[]
  | t::pending->
      let combine=combine_rec uf pending in
      let s=UF.signature uf t in
      let u=snd (UF.subterms uf t) in
      let f (c,a) pac pacs=
	if a=0 then pacs else 
	  let sg=(c,a-1) in
	    UF.add_node_pac uf t sg pac.term_head;
	    PacMap.add sg {pac with args=u::pac.args;term_head=t} pacs
      in
      let pacs=PacMap.fold f (UF.pac_map uf (fst s)) PacMap.empty in
      let i=UF.find uf t in
      let (p,c)=UF.add_pacs uf i pacs in
      let combine2=(combine_rec uf p)@c@combine in
      try {lhs=t;rhs=ST.query s uf.UF.sigtable;rule=Congruence}::combine2 with
	Not_found->
	  ST.enter t s uf.UF.sigtable;combine2
	    
let rec process_rec uf=function
    []->[] 
  | eq::combine->
      let pending=process_rec uf combine in
      let i=UF.find uf eq.lhs 
      and j=UF.find uf eq.rhs in
      if i=j then
	pending
      else
	if (UF.size uf i)<(UF.size uf j) then
	  let l=UF.fathers uf i in
	  let (p,c)=UF.union uf i j eq in
	  let _ =ST.delete_list l uf.UF.sigtable in
	  let inj_pending=process_rec uf c in
	    inj_pending@p@l@pending
	else
	  let l=UF.fathers uf j in
	  let (p,c)=UF.union uf j i (swap eq) in
	  let _ =ST.delete_list l uf.UF.sigtable in
	  let inj_pending=process_rec uf c in
	    inj_pending@p@l@pending
	  
let rec cc_rec uf=function
    []->()
  | pending->
      let combine=combine_rec uf pending in
      let pending0=process_rec uf combine in
	cc_rec uf pending0
	
let cc uf=cc_rec uf (UF.nodes uf)

let rec make_uf=function
    []->UF.empty ()
  | (ax,(t1,t2))::q->
      let uf=make_uf q in
      let i1=UF.add uf t1 in
      let i2=UF.add uf t2 in
      let j1=UF.find uf i1 and j2=UF.find uf i2 in
	if j1=j2 then uf else  
	    let (_,inj_combine)=
		UF.union uf j1 j2 {lhs=i1;rhs=i2;rule=Axiom ax} in
	    let _ = process_rec uf inj_combine in uf
      
let add_one_diseq uf (t1,t2)=(UF.add uf t1,UF.add uf t2)

let add_disaxioms uf disaxioms=
  let f (id,cpl)=(id,add_one_diseq uf cpl) in
    List.map f disaxioms

let check_equal uf (i1,i2) = UF.find uf i1 = UF.find uf i2

let find_contradiction uf diseq =
  List.find (fun (id,cpl) -> check_equal uf cpl) diseq
 

