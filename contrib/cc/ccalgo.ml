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
open Pp
open Goptions
open Names
open Term

let init_size=5

let cc_verbose=ref false 

let debug f x = 
  if !cc_verbose then f x

let _=
  let gdopt=
    { optsync=true;
      optname="Congruence Verbose";
      optkey=SecondaryTable("Congruence","Verbose"); 
      optread=(fun ()-> !cc_verbose); 
      optwrite=(fun b -> cc_verbose := b)}  
  in
    declare_bool_option gdopt

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

  let rev_query term st=Hashtbl.find st.tosign term
	  
  let delete st t=
    try let sign=Hashtbl.find st.tosign t in
	Hashtbl.remove st.toterm sign;
	Hashtbl.remove st.tosign t
    with
	Not_found -> ()

  let rec delete_set st s = Intset.iter (delete st) s
	  
end

type pa_constructor=
    { cnode : int;
      arity : int;
      args  : int list}

type pa_fun=
    {fsym:int;
     fnargs:int}

type pa_mark=
    Fmark of pa_fun
  | Cmark of pa_constructor

module PacMap=Map.Make(struct 
			 type t=pa_constructor 
			 let compare=Pervasives.compare end) 

module PafMap=Map.Make(struct 
			 type t=pa_fun
			 let compare=Pervasives.compare end)

type cinfo=
    {ci_constr: constructor; (* inductive type *)
     ci_arity: int;     (* # args *)
     ci_nhyps: int}     (* # projectable args *)

type term=
    Symb of constr
  | Eps
  | Appli of term*term
  | Constructor of cinfo (* constructor arity + nhyps *)

type ccpattern =
    PApp of term * ccpattern list (* arguments are reversed *)
  | PVar of int 

type rule=
    Congruence
  | Axiom of constr * bool 
  | Injection of int * pa_constructor * int * pa_constructor * int

type from=
    Goal
  | Hyp of constr
  | HeqG of constr
  | HeqnH of constr * constr

type 'a eq = {lhs:int;rhs:int;rule:'a}

type equality = rule eq

type disequality = from eq

type quant_eq =
    {qe_hyp_id: identifier;
     qe_pol: bool;
     qe_nvars:int;
     qe_lhs: ccpattern;
     qe_lhs_valid:bool;
     qe_rhs: ccpattern;
     qe_rhs_valid:bool}

let swap eq : equality =
  let swap_rule=match eq.rule with
      Congruence -> Congruence
    | Injection (i,pi,j,pj,k) -> Injection (j,pj,i,pi,k)
    | Axiom (id,reversed) -> Axiom (id,not reversed)
  in {lhs=eq.rhs;rhs=eq.lhs;rule=swap_rule}
    
type inductive_status =
    Unknown
  | Partial of pa_constructor
  | Partial_applied
  | Total of (int * pa_constructor)

type representative=
    {mutable nfathers:int;
     mutable lfathers:Intset.t;
     mutable fathers:Intset.t;
     mutable inductive_status: inductive_status;
     mutable functions: Intset.t PafMap.t;
     mutable constructors: int PacMap.t} (*pac -> term = app(constr,t) *)

type cl = Rep of representative| Eqto of int*equality
  
type vertex = Leaf| Node of (int*int) 

type node = 
    {mutable clas:cl;
     mutable cpath: int; 
     vertex:vertex;
     term:term}
    
type forest=
    {mutable max_size:int;
     mutable size:int;
     mutable map: node array;
     axioms: (constr,term*term) Hashtbl.t;
     mutable epsilons: pa_constructor list;
     syms:(term,int) Hashtbl.t}

type state = 
    {uf: forest;
     sigtable:ST.t;
     mutable terms: Intset.t; 
     combine: equality Queue.t; 
     marks: (int * pa_mark) Queue.t;
     mutable diseq: disequality list;
     mutable quant: quant_eq list;
     mutable pa_classes: Intset.t;
     q_history: (identifier,int array) Hashtbl.t;
     mutable rew_depth:int;
     mutable changed:bool}

let dummy_node =
  {clas=Eqto(min_int,{lhs=min_int;rhs=min_int;rule=Congruence});
   cpath=min_int;
   vertex=Leaf;
   term=Symb (mkRel min_int)}

let empty depth:state =
  {uf=
     {max_size=init_size;
      size=0;
      map=Array.create init_size dummy_node;
      epsilons=[];
      axioms=Hashtbl.create init_size;
      syms=Hashtbl.create init_size};
  terms=Intset.empty;
  combine=Queue.create ();
  marks=Queue.create ();
  sigtable=ST.empty ();
  diseq=[];
  quant=[];
  pa_classes=Intset.empty;
  q_history=Hashtbl.create init_size;
  rew_depth=depth;
  changed=false}

let forest state = state.uf 
       
let compress_path uf i j = uf.map.(j).cpath<-i
			     
let rec find_aux uf visited i=  
  let j = uf.map.(i).cpath in 
    if j<0 then let _ = List.iter (compress_path uf i) visited in i else
      find_aux uf (i::visited) j
	
let find uf i= find_aux uf [] i
		 
let get_representative uf i=
  match uf.map.(i).clas with
      Rep r -> r
    | _ -> anomaly "get_representative: not a representative"

let find_pac uf i pac =
  PacMap.find pac (get_representative uf i).constructors

let get_constructor_info uf i=
  match uf.map.(i).term with
      Constructor cinfo->cinfo
    | _ -> anomaly "get_constructor: not a constructor"
	
let size uf i=
  (get_representative uf i).nfathers

let axioms uf = uf.axioms

let epsilons uf = uf.epsilons

let add_lfather uf i t=
  let r=get_representative uf i in
    r.nfathers<-r.nfathers+1;
    r.lfathers<-Intset.add t r.lfathers;
    r.fathers <-Intset.add t r.fathers

let add_rfather uf i t=
  let r=get_representative uf i in
    r.nfathers<-r.nfathers+1;
    r.fathers <-Intset.add t r.fathers

exception Discriminable of int * pa_constructor * int * pa_constructor 

let append_pac t p =
  {p with arity=pred p.arity;args=t::p.args} 

let tail_pac p=
  {p with arity=succ p.arity;args=List.tl p.args}

let fsucc paf =
  {paf with fnargs=succ paf.fnargs}
    
let add_pac rep pac t =
  if not (PacMap.mem pac rep.constructors) then
    rep.constructors<-PacMap.add pac t rep.constructors

let add_paf rep paf t =
  let already = 
    try PafMap.find paf rep.functions with Not_found -> Intset.empty in
    rep.functions<- PafMap.add paf (Intset.add t already) rep.functions

let term uf i=uf.map.(i).term
		
let subterms uf i=
  match uf.map.(i).vertex with
      Node(j,k) -> (j,k)
    | _ -> anomaly "subterms: not a node"
	
let signature uf i=
  let j,k=subterms uf i in (find uf j,find uf k)
			     
let next uf=
  let size=uf.size in
  let nsize= succ size in
    if nsize=uf.max_size then
      let newmax=uf.max_size * 3 / 2 + 1 in
      let newmap=Array.create newmax dummy_node in
	begin
	  uf.max_size<-newmax;
	  Array.blit uf.map 0 newmap 0 size;
	  uf.map<-newmap
	end 
    else ();
    uf.size<-nsize; 
    size
	
let new_representative ()=
  {nfathers=0;
   lfathers=Intset.empty;
   fathers=Intset.empty;
   inductive_status=Unknown;
   functions=PafMap.empty;
   constructors=PacMap.empty}
    
(* rebuild a constr from an applicative term *)
    
let rec constr_of_term = function
    Symb s->s
  | Eps -> mkMeta 0
  | Constructor cinfo -> mkConstruct cinfo.ci_constr 
  | Appli (s1,s2)->
      make_app [(constr_of_term s2)] s1
and make_app l=function
    Appli (s1,s2)->make_app ((constr_of_term s2)::l) s1    
  | other -> applistc (constr_of_term other) l 

(* rebuild a term from a pattern and a substitution *)

let build_subst uf subst =
  Array.map (fun i -> 
	       try term uf i 
	       with _ -> anomaly "incomplete matching") subst

let rec inst_pattern subst = function
    PVar i -> 
      subst.(pred i) 
  | PApp (t, args) -> 
      List.fold_right
	(fun spat f -> Appli (f,inst_pattern subst spat))
	   args t  

let pr_idx_term state i = str "[" ++ int i ++ str ":=" ++
  Termops.print_constr (constr_of_term (term state.uf i)) ++ str "]"

let pr_term t = str "[" ++
  Termops.print_constr (constr_of_term t) ++ str "]"

let rec add_term state t= 
  let uf=state.uf in
    try Hashtbl.find uf.syms t with 
	Not_found ->
	  let b=next uf in
	  let new_node=
	    match t with
		Symb _ ->
		  let paf =
		    {fsym=b;
		     fnargs=0} in
		    Queue.add (b,Fmark paf) state.marks;
		    {clas= Rep (new_representative ());
		     cpath= -1;
		     vertex= Leaf;
		     term= t}
	      | Eps -> 
		  {clas= Rep (new_representative ());
		   cpath= -1;
		   vertex= Leaf;
		   term= t}
	      | Appli (t1,t2) -> 
		  let i1=add_term state t1 and i2=add_term state t2 in
		    add_lfather uf (find uf i1) b;
		    add_rfather uf (find uf i2) b;
		    state.terms<-Intset.add b state.terms;
		    {clas= Rep (new_representative ());
		     cpath= -1;
		     vertex= Node(i1,i2);
		     term= t}
	      | Constructor cinfo ->
		  let paf =
		    {fsym=b;
		     fnargs=0} in
		    Queue.add (b,Fmark paf) state.marks;
		  let pac =
		    {cnode= b;
		     arity= cinfo.ci_arity;
		     args=[]} in
		    Queue.add (b,Cmark pac) state.marks;
		    {clas=Rep (new_representative ());
		     cpath= -1;
		     vertex=Leaf;
		     term=t}
	  in
	    uf.map.(b)<-new_node;
	    Hashtbl.add uf.syms t b;
	    b

let add_equality state c s t=
  let i = add_term state s in
  let j = add_term state t in
    Queue.add {lhs=i;rhs=j;rule=Axiom(c,false)} state.combine;
    Hashtbl.add state.uf.axioms c (s,t)

let add_disequality state from s t =
  let i = add_term state s in
  let j = add_term state t in
    state.diseq<-{lhs=i;rhs=j;rule=from}::state.diseq

let add_quant state id pol (nvars,valid1,patt1,valid2,patt2) =
  state.quant<-
    {qe_hyp_id= id;
     qe_pol= pol;
     qe_nvars=nvars;
     qe_lhs= patt1;
     qe_lhs_valid=valid1;
     qe_rhs= patt2;
     qe_rhs_valid=valid2}::state.quant

let is_redundant state id args =
  try  
    let norm_args = Array.map (find state.uf) args in
    let prev_args = Hashtbl.find_all state.q_history id in
    List.exists 
      (fun old_args -> 
	 Util.array_for_all2 (fun i j -> i = find state.uf j) 
         norm_args old_args) 
      prev_args
    with Not_found -> false

let add_inst state (inst,int_subst) = 
  check_for_interrupt ();
  if state.rew_depth > 0 then
  if is_redundant state inst.qe_hyp_id int_subst then
    debug msgnl (str "discarding redundant (dis)equality")
  else   
    begin
      Hashtbl.add state.q_history inst.qe_hyp_id int_subst;
      let subst = build_subst (forest state) int_subst in
      let prfhead= mkVar inst.qe_hyp_id in
      let args = Array.map constr_of_term subst in
      let _ = array_rev args in (* highest deBruijn index first *)
      let prf= mkApp(prfhead,args) in
	  let s = inst_pattern subst inst.qe_lhs 
	  and t = inst_pattern subst inst.qe_rhs in
	    state.changed<-true;
	    state.rew_depth<-pred state.rew_depth;
	    if inst.qe_pol then
	      begin
		debug (fun () -> 
		  msgnl 
		   (str "Adding new equality, depth="++ int state.rew_depth);
	          msgnl (str "  [" ++ Termops.print_constr prf ++ str " : " ++ 
			   pr_term s ++ str " == " ++ pr_term t ++ str "]")) ();
		add_equality state prf s t
	      end
	    else
	      begin
		debug (fun () -> 
		  msgnl 
		   (str "Adding new disequality, depth="++ int state.rew_depth);
	          msgnl (str "  [" ++ Termops.print_constr prf ++ str " : " ++ 
			   pr_term s ++ str " <> " ++ pr_term t ++ str "]")) ();
		add_disequality state (Hyp prf) s t 
	      end
  end

let link uf i j eq = (* links i -> j *)
  let node=uf.map.(i) in 
    node.clas<-Eqto (j,eq);
    node.cpath<-j
	
let rec down_path uf i l=
  match uf.map.(i).clas with
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

let union state i1 i2 eq=
  debug (fun () -> msgnl (str "Linking " ++ pr_idx_term state i1 ++ 
		 str " and " ++ pr_idx_term state i2 ++ str ".")) ();
  let r1= get_representative state.uf i1 
  and r2= get_representative state.uf i2 in
    link state.uf i1 i2 eq;
    let f= Intset.union r1.fathers r2.fathers in
      r2.nfathers<-Intset.cardinal f;
      r2.fathers<-f;
      r2.lfathers<-Intset.union r1.lfathers r2.lfathers;
      ST.delete_set state.sigtable r1.fathers;
      state.terms<-Intset.union state.terms r1.fathers;       
      PacMap.iter 
	(fun pac b -> Queue.add (b,Cmark pac) state.marks) 
	r1.constructors;
      PafMap.iter 
	(fun paf -> Intset.iter 
	   (fun b -> Queue.add (b,Fmark paf) state.marks)) 
	r1.functions;
      match r1.inductive_status,r2.inductive_status with 
	  Unknown,_ -> ()
	| Partial pac,Unknown -> 
	    r2.inductive_status<-Partial pac;
	    state.pa_classes<-Intset.remove i1 state.pa_classes;
	    state.pa_classes<-Intset.add i2 state.pa_classes
	| Partial _ ,(Partial _ |Partial_applied) -> 
	    state.pa_classes<-Intset.remove i1 state.pa_classes
	| Partial_applied,Unknown -> 
	    r2.inductive_status<-Partial_applied	      
	| Partial_applied,Partial _ -> 
	    state.pa_classes<-Intset.remove i2 state.pa_classes;
	    r2.inductive_status<-Partial_applied
	| Total cpl,Unknown -> r2.inductive_status<-Total cpl;
	| Total (i,pac),Total _ -> Queue.add (i,Cmark pac) state.marks    
	| _,_ -> () 
            
let merge eq state = (* merge and no-merge *)
  debug (fun () -> msgnl 
    (str "Merging " ++ pr_idx_term state eq.lhs ++ 
       str " and " ++ pr_idx_term state eq.rhs ++ str ".")) ();
  let uf=state.uf in
  let i=find uf eq.lhs 
  and j=find uf eq.rhs in
    if i<>j then 
      if (size uf i)<(size uf j) then
	union state i j eq
      else
	union state j i (swap eq)

let update t state = (* update 1 and 2 *)
  debug (fun () -> msgnl 
    (str "Updating term " ++ pr_idx_term state t ++ str ".")) ();
  let (i,j) as sign = signature state.uf t in
  let (u,v) = subterms state.uf t in
  let rep = get_representative state.uf i in
    begin
      match rep.inductive_status with 
	  Partial _ ->
	    rep.inductive_status <- Partial_applied;
	    state.pa_classes <- Intset.remove i state.pa_classes
	| _ -> ()
    end;
    PacMap.iter 
      (fun pac _ -> Queue.add (t,Cmark (append_pac v pac)) state.marks) 
      rep.constructors; 
    PafMap.iter 
      (fun paf _ -> Queue.add (t,Fmark (fsucc paf)) state.marks) 
      rep.functions; 
    try 
      let s = ST.query sign state.sigtable in 
	Queue.add {lhs=t;rhs=s;rule=Congruence} state.combine
    with 
	Not_found -> ST.enter t sign state.sigtable

let process_function_mark t rep paf state  =
  add_paf rep paf t;
  state.terms<-Intset.union rep.lfathers state.terms
    
let process_constructor_mark t i rep pac state =
    match rep.inductive_status with
	Total (s,opac) ->
	  if pac.cnode <> opac.cnode then (* Conflict *) 
	    raise (Discriminable (s,opac,t,pac)) 
	  else (* Match *)
	    let cinfo = get_constructor_info state.uf pac.cnode in
	    let rec f n oargs args=
	      if n > 0 then 
		match (oargs,args) with
		    s1::q1,s2::q2->
		      Queue.add 
			{lhs=s1;rhs=s2;rule=Injection(s,opac,t,pac,n)}
			state.combine;
		      f (n-1) q1 q2 
		  | _-> anomaly 
		      "add_pacs : weird error in injection subterms merge" 
	    in f cinfo.ci_nhyps opac.args pac.args
      | Partial_applied | Partial _ ->
	  add_pac rep pac t;
	  state.terms<-Intset.union rep.lfathers state.terms
      | Unknown ->
	  if pac.arity = 0 then
	    rep.inductive_status <- Total (t,pac)
	  else
	    begin
	      add_pac rep pac t;
	      state.terms<-Intset.union rep.lfathers state.terms;
	      rep.inductive_status <- Partial pac;
	      state.pa_classes<- Intset.add i state.pa_classes
	    end

let process_mark t m state = 
  debug (fun () -> msgnl 
    (str "Processing mark for term " ++ pr_idx_term state t ++ str ".")) ();
  let i=find state.uf t in
  let rep=get_representative state.uf i in
    match m with
	Fmark paf -> process_function_mark t rep paf state
      | Cmark pac -> process_constructor_mark t i rep pac state

type explanation =
    Discrimination of (int*pa_constructor*int*pa_constructor)
  | Contradiction of disequality
  | Incomplete

let check_disequalities state =
  let uf=state.uf in
  let rec check_aux = function
      dis::q -> 
	debug (fun () -> msg   
	(str "Checking if " ++ pr_idx_term state dis.lhs ++ str " = " ++ 
	 pr_idx_term state dis.rhs ++ str " ... ")) ();  
	if find uf dis.lhs=find uf dis.rhs then 
	  begin debug msgnl (str "Yes");Some dis end 
	else
	  begin debug msgnl (str "No");check_aux q end
    | [] -> None 
  in
    check_aux state.diseq

let one_step state =
    try
      let eq = Queue.take state.combine in
	merge eq state;
	true
    with Queue.Empty -> 
      try 
	let (t,m) = Queue.take state.marks in
	  process_mark t m state;
	  true
      with Queue.Empty ->
	try
	  let t = Intset.choose state.terms in
	    state.terms<-Intset.remove t state.terms;
	    update t state;
	    true
	with Not_found -> false
	  

let complete_one_class state i=
  match (get_representative state.uf i).inductive_status with
      Partial pac ->
	let rec app t n = 
	  if n<=0 then t else
	    app (Appli(t,Eps)) (n-1) in
	  state.uf.epsilons <- pac :: state.uf.epsilons; 
	  ignore (add_term state (app (term state.uf i) pac.arity))
    | _ -> anomaly "wrong incomplete class" 

let complete state =
  Intset.iter (complete_one_class state) state.pa_classes

type matching_problem = 
{mp_subst : int array;
 mp_inst : quant_eq;
 mp_stack : (ccpattern*int) list }

let make_fun_table state =
  let uf= state.uf in
  let funtab=ref PafMap.empty in
  for cl=0 to pred uf.size do 
    match uf.map.(cl).clas with
	Rep rep ->
	  PafMap.iter 
	    (fun paf _ -> 
	       let elem = 
		 try PafMap.find paf !funtab 
		 with Not_found -> Intset.empty in
		 funtab:= PafMap.add paf (Intset.add cl elem) !funtab) 
	    rep.functions
      | _ -> ()   
  done;
    !funtab
  

let rec do_match state res pb_stack =
  let mp=Stack.pop pb_stack in
    match mp.mp_stack with
	[] -> 
	  res:= (mp.mp_inst,mp.mp_subst) :: !res
      | (patt,cl)::remains ->
	  let uf=state.uf in
	    match patt with
		PVar i -> 
		  if mp.mp_subst.(pred i)<0 then  
		    begin
		      mp.mp_subst.(pred i)<- cl; (* no aliasing problem here *)
		      Stack.push {mp with mp_stack=remains} pb_stack
		    end
		  else
		    if mp.mp_subst.(pred i) = cl then
		      Stack.push {mp with mp_stack=remains} pb_stack
		    else (* mismatch for non-linear variable in pattern *) ()
	      | PApp (f,[]) ->
		  begin
		    try let j=Hashtbl.find uf.syms f in
		      if find uf j =cl then
			Stack.push {mp with mp_stack=remains} pb_stack
		    with Not_found -> ()
		 
 end
	      | PApp(f, ((last_arg::rem_args) as args)) ->
		  try 
		    let j=Hashtbl.find uf.syms f in
		    let paf={fsym=j;fnargs=List.length args} in
		    let rep=get_representative uf cl in
		    let good_terms = PafMap.find paf rep.functions in
		    let aux i = 
		      let (s,t) = signature state.uf i in
			Stack.push 
			  {mp with 
			     mp_subst=Array.copy mp.mp_subst;
			     mp_stack=
			      (PApp(f,rem_args),s) :: 
				(last_arg,t) :: remains} pb_stack in
		      Intset.iter aux good_terms 
		  with Not_found -> ()

let paf_of_patt syms = function
    PVar _ -> invalid_arg "paf_of_patt: pattern is trivial"
  | PApp (f,args) ->
      {fsym=Hashtbl.find syms f;
       fnargs=List.length args}

let init_pb_stack state = 
  let syms= state.uf.syms in
  let pb_stack = Stack.create () in
  let funtab = make_fun_table state in
  let aux inst =
    begin
      if inst.qe_lhs_valid then
	try 
	  let paf= paf_of_patt syms inst.qe_lhs in
	  let good_classes = PafMap.find paf funtab in
	    Intset.iter (fun i -> 
			 Stack.push 
			   {mp_subst = Array.make inst.qe_nvars (-1); 
			    mp_inst=inst;
			    mp_stack=[inst.qe_lhs,i]} pb_stack) good_classes
	with Not_found -> ()
    end;
    begin 
      if inst.qe_rhs_valid then
	try 
	  let paf= paf_of_patt syms inst.qe_rhs in
	  let good_classes = PafMap.find paf funtab in
	    Intset.iter (fun i -> 
			   Stack.push 
			     {mp_subst = Array.make inst.qe_nvars (-1); 
			      mp_inst=inst;
			      mp_stack=[inst.qe_rhs,i]} pb_stack) good_classes
	with Not_found -> ()
    end in
    List.iter aux state.quant;
    pb_stack

let find_instances state = 
  let pb_stack= init_pb_stack state in
  let res =ref [] in
  let _ =
    debug msgnl (str "Running E-matching algorithm ... ");
    try
      while true do
	check_for_interrupt ();
	do_match state res pb_stack 
      done;
      anomaly "get out of here !"
    with Stack.Empty -> () in
    !res

let rec execute first_run state =
  debug msgnl (str "Executing ... ");
  try
    while 
      check_for_interrupt ();
      one_step state do ()
    done;
    match check_disequalities state with
	None -> 
	  if not(Intset.is_empty state.pa_classes) then
	    begin 
	      debug msgnl (str "First run was incomplete, completing ... ");
	      complete state;
	      execute false state
	    end
	  else 
	    if state.rew_depth>0 then
	      let l=find_instances state in
		List.iter (add_inst state) l;
		if state.changed then 
		  begin
		    state.changed <- false;
		    execute true state
		  end
		else
	      begin 
		debug msgnl (str "Out of instances ... ");
		None
	      end
	    else 
	      begin 
		debug msgnl (str "Out of depth ... ");
		None
	      end
      | Some dis -> Some
	  begin
	    if first_run then Contradiction dis
	    else Incomplete
	  end
  with Discriminable(s,spac,t,tpac) -> Some
    begin
      if first_run then Discrimination (s,spac,t,tpac)
      else Incomplete
    end


