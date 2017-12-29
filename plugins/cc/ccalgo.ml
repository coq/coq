(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file implements the basic congruence-closure algorithm by *)
(* Downey, Sethi and Tarjan. *)
(* Plus some e-matching and constructor handling by P. Corbineau *)

open CErrors
open Pp
open Names
open Sorts
open Constr
open Vars
open Goptions
open Tacmach
open Util

let init_size=5

let cc_verbose=ref false

let print_constr t =
  let sigma, env = Pfedit.get_current_context () in
  Printer.pr_econstr_env env sigma t

let debug x =
  if !cc_verbose then Feedback.msg_debug (x ())

let _=
  let gdopt=
    { optdepr=false;
      optname="Congruence Verbose";
      optkey=["Congruence";"Verbose"];
      optread=(fun ()-> !cc_verbose);
      optwrite=(fun b -> cc_verbose := b)}
  in
    declare_bool_option gdopt

(* Signature table *)

module ST=struct

  (* l: sign -> term r: term -> sign *)

  module IntTable = Hashtbl.Make(Int)
  module IntPair =
  struct
    type t = int * int
    let equal (i1, j1) (i2, j2) = Int.equal i1 i2 && Int.equal j1 j2
    let hash (i, j) = Hashset.Combine.combine (Int.hash i) (Int.hash j)
  end
  module IntPairTable = Hashtbl.Make(IntPair)

  type t = {toterm: int IntPairTable.t;
	    tosign: (int * int) IntTable.t}

  let empty ()=
    {toterm=IntPairTable.create init_size;
     tosign=IntTable.create init_size}

  let enter t sign st=
    if IntPairTable.mem st.toterm sign then
	anomaly ~label:"enter" (Pp.str "signature already entered.")
    else
	IntPairTable.replace st.toterm sign t;
	IntTable.replace st.tosign t sign

  let query sign st=IntPairTable.find st.toterm sign

  let delete st t=
    try let sign=IntTable.find st.tosign t in
	IntPairTable.remove st.toterm sign;
	IntTable.remove st.tosign t
    with
	Not_found -> ()

  let delete_set st s = Int.Set.iter (delete st) s

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

module PacOrd =
struct
  type t = pa_constructor
  let compare { cnode = cnode0; arity = arity0; args = args0 }
              { cnode = cnode1; arity = arity1; args = args1 } =
    let cmp = Int.compare cnode0 cnode1 in
    if cmp = 0 then
      let cmp' = Int.compare arity0 arity1 in
      if cmp' = 0 then
        List.compare Int.compare args0 args1
      else
        cmp'
    else
      cmp
end

module PafOrd =
struct
  type t = pa_fun
  let compare { fsym = fsym0; fnargs = fnargs0 } { fsym = fsym1; fnargs = fnargs1 } =
    let cmp = Int.compare fsym0 fsym1 in
    if cmp = 0 then
      Int.compare fnargs0 fnargs1
    else
      cmp
end

module PacMap=Map.Make(PacOrd)
module PafMap=Map.Make(PafOrd)

type cinfo=
    {ci_constr: pconstructor; (* inductive type *)
     ci_arity: int;     (* # args *)
     ci_nhyps: int}     (* # projectable args *)

let family_eq f1 f2 = match f1, f2 with
  | Set, Set
  | Prop, Prop
  | Type _, Type _ -> true
  | _ -> false

type term=
    Symb of constr
  | Product of Sorts.t * Sorts.t
  | Eps of Id.t
  | Appli of term*term
  | Constructor of cinfo (* constructor arity + nhyps *)

let rec term_equal t1 t2 =
  match t1, t2 with
    | Symb c1, Symb c2 -> eq_constr_nounivs c1 c2
    | Product (s1, t1), Product (s2, t2) -> family_eq s1 s2 && family_eq t1 t2
    | Eps i1, Eps i2 -> Id.equal i1 i2
    | Appli (t1, u1), Appli (t2, u2) -> term_equal t1 t2 && term_equal u1 u2
    | Constructor {ci_constr=(c1,u1); ci_arity=i1; ci_nhyps=j1},
      Constructor {ci_constr=(c2,u2); ci_arity=i2; ci_nhyps=j2} ->
      Int.equal i1 i2 && Int.equal j1 j2 && eq_constructor c1 c2 (* FIXME check eq? *)
    | _ -> false

open Hashset.Combine

let rec hash_term = function
  | Symb c -> combine 1 (Constr.hash c)
  | Product (s1, s2) -> combine3 2 (Sorts.hash s1) (Sorts.hash s2)
  | Eps i -> combine 3 (Id.hash i)
  | Appli (t1, t2) -> combine3 4 (hash_term t1) (hash_term t2)
  | Constructor {ci_constr=(c,u); ci_arity=i; ci_nhyps=j} -> combine4 5 (constructor_hash c) i j

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

type patt_kind =
    Normal
  | Trivial of types
  | Creates_variables

type quant_eq =
  {
    qe_hyp_id: Id.t;
    qe_pol: bool;
    qe_nvars:int;
    qe_lhs: ccpattern;
    qe_lhs_valid:patt_kind;
    qe_rhs: ccpattern;
    qe_rhs_valid:patt_kind
  }
    
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
    {mutable weight:int;
     mutable lfathers:Int.Set.t;
     mutable fathers:Int.Set.t;
     mutable inductive_status: inductive_status;
     class_type : types;
     mutable functions: Int.Set.t PafMap.t} (*pac -> term = app(constr,t) *)

type cl = Rep of representative| Eqto of int*equality

type vertex = Leaf| Node of (int*int)

type node =
    {mutable clas:cl;
     mutable cpath: int;
     mutable constructors: int PacMap.t;
     vertex:vertex;
     term:term}

module Constrhash = Hashtbl.Make
  (struct type t = constr
	  let equal = eq_constr_nounivs
	  let hash = Constr.hash
   end)
module Typehash = Constrhash

module Termhash = Hashtbl.Make
  (struct type t = term
	  let equal = term_equal
	  let hash = hash_term
   end)

module Identhash = Hashtbl.Make
  (struct type t = Id.t
	  let equal = Id.equal
	  let hash = Id.hash
   end)

type forest=
    {mutable max_size:int;
     mutable size:int;
     mutable map: node array;
     axioms: (term*term) Constrhash.t;
     mutable epsilons: pa_constructor list;
     syms: int Termhash.t}

type state =
    {uf: forest;
     sigtable:ST.t;
     mutable terms: Int.Set.t;
     combine: equality Queue.t;
     marks: (int * pa_mark) Queue.t;
     mutable diseq: disequality list;
     mutable quant: quant_eq list;
     mutable pa_classes: Int.Set.t;
     q_history: (int array) Identhash.t;
     mutable rew_depth:int;
     mutable changed:bool;
     by_type: Int.Set.t Typehash.t;
     mutable env:Environ.env;
     sigma:Evd.evar_map}

let dummy_node =
  {
    clas=Eqto (min_int,{lhs=min_int;rhs=min_int;rule=Congruence});
    cpath=min_int;
    constructors=PacMap.empty;
    vertex=Leaf;
    term=Symb (mkRel min_int)
  }

let empty_forest() =
  {
    max_size=init_size;
    size=0;
    map=Array.make init_size dummy_node;
    epsilons=[];
    axioms=Constrhash.create init_size;
    syms=Termhash.create init_size
  }
    
let empty depth gls:state =
  {
    uf= empty_forest ();
    terms=Int.Set.empty;
    combine=Queue.create ();
    marks=Queue.create ();
    sigtable=ST.empty ();
    diseq=[];
    quant=[];
    pa_classes=Int.Set.empty;
    q_history=Identhash.create init_size;
    rew_depth=depth;
    by_type=Constrhash.create init_size;
    changed=false;
    env=pf_env gls;
    sigma=project gls
  }
    
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
    | _ -> anomaly ~label:"get_representative" (Pp.str "not a representative.")

let get_constructors uf i= uf.map.(i).constructors

let find_pac uf i pac =
  PacMap.find pac (get_constructors uf i)

let rec find_oldest_pac uf i pac=
  try PacMap.find pac (get_constructors uf i) with
    Not_found -> 
      match uf.map.(i).clas with 
	Eqto (j,_) -> find_oldest_pac uf j pac
      | Rep _ -> raise Not_found
     

let get_constructor_info uf i=
  match uf.map.(i).term with
      Constructor cinfo->cinfo
    | _ -> anomaly ~label:"get_constructor" (Pp.str "not a constructor.")

let size uf i=
  (get_representative uf i).weight

let axioms uf = uf.axioms

let epsilons uf = uf.epsilons

let add_lfather uf i t=
  let r=get_representative uf i in
    r.weight<-r.weight+1;
    r.lfathers<-Int.Set.add t r.lfathers;
    r.fathers <-Int.Set.add t r.fathers

let add_rfather uf i t=
  let r=get_representative uf i in
    r.weight<-r.weight+1;
    r.fathers <-Int.Set.add t r.fathers

exception Discriminable of int * pa_constructor * int * pa_constructor

let append_pac t p =
  {p with arity=pred p.arity;args=t::p.args}

let tail_pac p=
  {p with arity=succ p.arity;args=List.tl p.args}

let fsucc paf =
  {paf with fnargs=succ paf.fnargs}

let add_pac node pac t =
  if not (PacMap.mem pac node.constructors) then
    node.constructors<-PacMap.add pac t node.constructors

let add_paf rep paf t =
  let already =
    try PafMap.find paf rep.functions with Not_found -> Int.Set.empty in
    rep.functions<- PafMap.add paf (Int.Set.add t already) rep.functions

let term uf i=uf.map.(i).term

let subterms uf i=
  match uf.map.(i).vertex with
      Node(j,k) -> (j,k)
    | _ -> anomaly ~label:"subterms" (Pp.str "not a node.")

let signature uf i=
  let j,k=subterms uf i in (find uf j,find uf k)

let next uf=
  let size=uf.size in
  let nsize= succ size in
    if Int.equal nsize uf.max_size then
      let newmax=uf.max_size * 3 / 2 + 1 in
      let newmap=Array.make newmax dummy_node in
	begin
	  uf.max_size<-newmax;
	  Array.blit uf.map 0 newmap 0 size;
	  uf.map<-newmap
	end
    else ();
    uf.size<-nsize;
    size

let new_representative typ =
  {weight=0;
   lfathers=Int.Set.empty;
   fathers=Int.Set.empty;
   inductive_status=Unknown;
   class_type=typ;
   functions=PafMap.empty}

(* rebuild a constr from an applicative term *)

let _A_ = Name (Id.of_string "A")
let _B_ = Name (Id.of_string "A")
let _body_ =  mkProd(Anonymous,mkRel 2,mkRel 2)

let cc_product s1 s2 =
  mkLambda(_A_,mkSort(s1),
	   mkLambda(_B_,mkSort(s2),_body_))

let rec constr_of_term = function
    Symb s-> s
  | Product(s1,s2) -> cc_product s1 s2
  | Eps id -> mkVar id
  | Constructor cinfo -> mkConstructU cinfo.ci_constr
  | Appli (s1,s2)->
      make_app [(constr_of_term s2)] s1
and make_app l=function
    Appli (s1,s2)->make_app ((constr_of_term s2)::l) s1
  | other -> Term.applist (constr_of_term other,l)

let rec canonize_name sigma c =
  let c = EConstr.Unsafe.to_constr c in
  let func c = canonize_name sigma (EConstr.of_constr c) in
    match Constr.kind c with
      | Const (kn,u) ->
	  let canon_const = Constant.make1 (Constant.canonical kn) in 
	    (mkConstU (canon_const,u))
      | Ind ((kn,i),u) ->
	  let canon_mind = MutInd.make1 (MutInd.canonical kn) in
	    (mkIndU ((canon_mind,i),u))
      | Construct (((kn,i),j),u) ->
	  let canon_mind = MutInd.make1 (MutInd.canonical kn) in
	    mkConstructU (((canon_mind,i),j),u)
      | Prod (na,t,ct) ->
	  mkProd (na,func t, func ct)
      | Lambda (na,t,ct) ->
	  mkLambda (na, func t,func ct)
      | LetIn (na,b,t,ct) ->
	  mkLetIn (na, func b,func t,func ct)
      | App (ct,l) ->
          mkApp (func ct,Array.Smart.map func l)
      | Proj(p,c) ->
	let p' = Projection.map (fun kn ->
          MutInd.make1 (MutInd.canonical kn)) p in
	  (mkProj (p', func c))
      | _ -> c

(* rebuild a term from a pattern and a substitution *)

let build_subst uf subst =
  Array.map
    (fun i ->
      try term uf i
      with e when CErrors.noncritical e ->
        anomaly (Pp.str "incomplete matching."))
    subst

let rec inst_pattern subst = function
    PVar i ->
      subst.(pred i)
  | PApp (t, args) ->
      List.fold_right
	(fun spat f -> Appli (f,inst_pattern subst spat))
	   args t

let pr_idx_term uf i = str "[" ++ int i ++ str ":=" ++
  print_constr (EConstr.of_constr (constr_of_term (term uf i))) ++ str "]"

let pr_term t = str "[" ++
  print_constr (EConstr.of_constr (constr_of_term t)) ++ str "]"

let rec add_term state t=
  let uf=state.uf in
    try Termhash.find uf.syms t with
	Not_found ->
	  let b=next uf in
          let trm = constr_of_term t in
          let typ = Typing.unsafe_type_of state.env state.sigma (EConstr.of_constr trm) in
          let typ = canonize_name state.sigma typ in
	  let new_node=
	    match t with
		Symb _ | Product (_,_) ->
		  let paf =
		    {fsym=b;
		     fnargs=0} in
		    Queue.add (b,Fmark paf) state.marks;
		    {clas= Rep (new_representative typ);
		     cpath= -1;
		     constructors=PacMap.empty;
		     vertex= Leaf;
		     term= t}
	      | Eps id ->
		  {clas= Rep (new_representative typ);
		   cpath= -1;
		   constructors=PacMap.empty;
		   vertex= Leaf;
		   term= t}
	      | Appli (t1,t2) ->
		  let i1=add_term state t1 and i2=add_term state t2 in
		    add_lfather uf (find uf i1) b;
		    add_rfather uf (find uf i2) b;
		    state.terms<-Int.Set.add b state.terms;
		    {clas= Rep (new_representative typ);
		     cpath= -1;
		     constructors=PacMap.empty;
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
		    {clas=Rep (new_representative typ);
		     cpath= -1;
		     constructors=PacMap.empty;
		     vertex=Leaf;
		     term=t}
	  in
	    uf.map.(b)<-new_node;
	    Termhash.add uf.syms t b;
	    Typehash.replace state.by_type typ
	      (Int.Set.add b
		 (try Typehash.find state.by_type typ with
		      Not_found -> Int.Set.empty));
	    b

let add_equality state c s t=
  let i = add_term state s in
  let j = add_term state t in
    Queue.add {lhs=i;rhs=j;rule=Axiom(c,false)} state.combine;
    Constrhash.add state.uf.axioms c (s,t)

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
    let prev_args = Identhash.find_all state.q_history id in
    List.exists
      (fun old_args ->
	 Util.Array.for_all2 (fun i j -> Int.equal i (find state.uf j))
         norm_args old_args)
      prev_args
    with Not_found -> false

let add_inst state (inst,int_subst) =
  Control.check_for_interrupt ();
  if state.rew_depth > 0 then
  if is_redundant state inst.qe_hyp_id int_subst then
    debug (fun () -> str "discarding redundant (dis)equality")
  else
    begin
      Identhash.add state.q_history inst.qe_hyp_id int_subst;
      let subst = build_subst (forest state) int_subst in
      let prfhead= mkVar inst.qe_hyp_id in
      let args = Array.map constr_of_term subst in
      let _ = Array.rev args in (* highest deBruijn index first *)
      let prf= mkApp(prfhead,args) in
	  let s = inst_pattern subst inst.qe_lhs
	  and t = inst_pattern subst inst.qe_rhs in
	    state.changed<-true;
	    state.rew_depth<-pred state.rew_depth;
	    if inst.qe_pol then
	      begin
		debug (fun () ->
		   (str "Adding new equality, depth="++ int state.rew_depth) ++ fnl () ++
                  (str "  [" ++ print_constr (EConstr.of_constr prf) ++ str " : " ++
			   pr_term s ++ str " == " ++ pr_term t ++ str "]"));
		add_equality state prf s t
	      end
	    else
	      begin
		debug (fun () ->
		   (str "Adding new disequality, depth="++ int state.rew_depth) ++ fnl () ++
                  (str "  [" ++ print_constr (EConstr.of_constr prf) ++ str " : " ++
			   pr_term s ++ str " <> " ++ pr_term t ++ str "]"));
		add_disequality state (Hyp prf) s t
	      end
  end

let link uf i j eq = (* links i -> j *)
  let node=uf.map.(i) in
    node.clas<-Eqto (j,eq);
    node.cpath<-j

let rec down_path uf i l=
  match uf.map.(i).clas with
      Eqto (j,eq) ->down_path uf j (((i,j),eq)::l)
    | Rep _ ->l

let eq_pair (i1, j1) (i2, j2) = Int.equal i1 i2 && Int.equal j1 j2

let rec min_path=function
    ([],l2)->([],l2)
  | (l1,[])->(l1,[])
  | (((c1,t1)::q1),((c2,t2)::q2)) when eq_pair c1 c2 -> min_path (q1,q2)
  | cpl -> cpl

let join_path uf i j=
  assert (Int.equal (find uf i) (find uf j));
  min_path (down_path uf i [],down_path uf j [])

let union state i1 i2 eq=
  debug (fun () -> str "Linking " ++ pr_idx_term state.uf i1 ++
		 str " and " ++ pr_idx_term state.uf i2 ++ str ".");
  let r1= get_representative state.uf i1
  and r2= get_representative state.uf i2 in
    link state.uf i1 i2 eq;
    Constrhash.replace state.by_type r1.class_type
      (Int.Set.remove i1
	 (try Constrhash.find state.by_type r1.class_type with
	      Not_found -> Int.Set.empty));
    let f= Int.Set.union r1.fathers r2.fathers in
      r2.weight<-Int.Set.cardinal f;
      r2.fathers<-f;
      r2.lfathers<-Int.Set.union r1.lfathers r2.lfathers;
      ST.delete_set state.sigtable r1.fathers;
      state.terms<-Int.Set.union state.terms r1.fathers;
      PacMap.iter
	(fun pac b -> Queue.add (b,Cmark pac) state.marks)
	state.uf.map.(i1).constructors;
      PafMap.iter
	(fun paf -> Int.Set.iter
	   (fun b -> Queue.add (b,Fmark paf) state.marks))
	r1.functions;
      match r1.inductive_status,r2.inductive_status with
	  Unknown,_ -> ()
	| Partial pac,Unknown ->
	    r2.inductive_status<-Partial pac;
	    state.pa_classes<-Int.Set.remove i1 state.pa_classes;
	    state.pa_classes<-Int.Set.add i2 state.pa_classes
	| Partial _ ,(Partial _ |Partial_applied) ->
	    state.pa_classes<-Int.Set.remove i1 state.pa_classes
	| Partial_applied,Unknown ->
	    r2.inductive_status<-Partial_applied
	| Partial_applied,Partial _ ->
	    state.pa_classes<-Int.Set.remove i2 state.pa_classes;
	    r2.inductive_status<-Partial_applied
	| Total cpl,Unknown -> r2.inductive_status<-Total cpl;
	| Total (i,pac),Total _ -> Queue.add (i,Cmark pac) state.marks
	| _,_ -> ()

let merge eq state = (* merge and no-merge *)
  debug
    (fun () -> str "Merging " ++ pr_idx_term state.uf eq.lhs ++
       str " and " ++ pr_idx_term state.uf eq.rhs ++ str ".");
  let uf=state.uf in
  let i=find uf eq.lhs
  and j=find uf eq.rhs in
    if not (Int.equal i j) then
      if (size uf i)<(size uf j) then
	union state i j eq
      else
	union state j i (swap eq)

let update t state = (* update 1 and 2 *)
  debug
    (fun () -> str "Updating term " ++ pr_idx_term state.uf t ++ str ".");
  let (i,j) as sign = signature state.uf t in
  let (u,v) = subterms state.uf t in
  let rep = get_representative state.uf i in
    begin
      match rep.inductive_status with
	  Partial _ ->
	    rep.inductive_status <- Partial_applied;
	    state.pa_classes <- Int.Set.remove i state.pa_classes
	| _ -> ()
    end;
    PacMap.iter
      (fun pac _ -> Queue.add (t,Cmark (append_pac v pac)) state.marks)
      (get_constructors state.uf i);
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
  state.terms<-Int.Set.union rep.lfathers state.terms

let process_constructor_mark t i rep pac state =
     add_pac state.uf.map.(i) pac t;
     match rep.inductive_status with
	Total (s,opac) ->
	  if not (Int.equal pac.cnode opac.cnode) then (* Conflict *)
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
		  | _-> anomaly ~label:"add_pacs"
		      (Pp.str "weird error in injection subterms merge.")
	    in f cinfo.ci_nhyps opac.args pac.args
      | Partial_applied | Partial _ ->
(*	  add_pac state.uf.map.(i) pac t; *)
	  state.terms<-Int.Set.union rep.lfathers state.terms
      | Unknown ->
	  if Int.equal pac.arity 0 then
	    rep.inductive_status <- Total (t,pac)
	  else
	    begin
	     (* add_pac state.uf.map.(i) pac t; *)
	      state.terms<-Int.Set.union rep.lfathers state.terms;
	      rep.inductive_status <- Partial pac;
	      state.pa_classes<- Int.Set.add i state.pa_classes
	    end

let process_mark t m state =
  debug
    (fun () -> str "Processing mark for term " ++ pr_idx_term state.uf t ++ str ".");
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
    | dis::q ->
        let (info, ans) =
          if Int.equal (find uf dis.lhs) (find uf dis.rhs) then (str "Yes", Some dis)
          else (str "No", check_aux q)
        in
        let _ = debug
        (fun () -> str "Checking if " ++ pr_idx_term state.uf dis.lhs ++ str " = " ++
         pr_idx_term state.uf dis.rhs ++ str " ... " ++ info) in
        ans
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
	  let t = Int.Set.choose state.terms in
	    state.terms<-Int.Set.remove t state.terms;
	    update t state;
	    true
	with Not_found -> false

let __eps__ = Id.of_string "_eps_"

let new_state_var typ state =
  let ids = Environ.ids_of_named_context_val (Environ.named_context_val state.env) in
  let id = Namegen.next_ident_away __eps__ ids in
  state.env<- EConstr.push_named (Context.Named.Declaration.LocalAssum (id,typ)) state.env;
  id

let complete_one_class state i=
  match (get_representative state.uf i).inductive_status with
      Partial pac ->
	let rec app t typ n =
	  if n<=0 then t else
	    let _,etyp,rest= destProd typ in
            let id = new_state_var (EConstr.of_constr etyp) state in
		app (Appli(t,Eps id)) (substl [mkVar id] rest) (n-1) in
        let _c = Typing.unsafe_type_of state.env state.sigma
	  (EConstr.of_constr (constr_of_term (term state.uf pac.cnode))) in
        let _c = EConstr.Unsafe.to_constr _c in
	let _args =
	  List.map (fun i -> constr_of_term (term state.uf  i))
	    pac.args in
        let typ = Term.prod_applist _c (List.rev _args) in
	let ct = app (term state.uf i) typ pac.arity in
	  state.uf.epsilons <- pac :: state.uf.epsilons;
	  ignore (add_term state ct)
    | _ -> anomaly (Pp.str "wrong incomplete class.")

let complete state =
  Int.Set.iter (complete_one_class state) state.pa_classes

type matching_problem =
{mp_subst : int array;
 mp_inst : quant_eq;
 mp_stack : (ccpattern*int) list }

let make_fun_table state =
  let uf= state.uf in
  let funtab=ref PafMap.empty in
  Array.iteri
    (fun i inode -> if i < uf.size then
       match inode.clas with
	   Rep rep ->
	     PafMap.iter
	       (fun paf _ ->
		  let elem =
		    try PafMap.find paf !funtab
		    with Not_found -> Int.Set.empty in
		    funtab:= PafMap.add paf (Int.Set.add i elem) !funtab)
	       rep.functions
	 | _ -> ()) state.uf.map;
    !funtab


let do_match state res pb_stack =
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
		    if Int.equal mp.mp_subst.(pred i) cl then
		      Stack.push {mp with mp_stack=remains} pb_stack
		    else (* mismatch for non-linear variable in pattern *) ()
	      | PApp (f,[]) ->
		  begin
		    try let j=Termhash.find uf.syms f in
		      if Int.equal (find uf j) cl then
			Stack.push {mp with mp_stack=remains} pb_stack
		    with Not_found -> ()
		  end
	      | PApp(f, ((last_arg::rem_args) as args)) ->
		  try
		    let j=Termhash.find uf.syms f in
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
		      Int.Set.iter aux good_terms
		  with Not_found -> ()

let paf_of_patt syms = function
    PVar _ -> invalid_arg "paf_of_patt: pattern is trivial"
  | PApp (f,args) ->
      {fsym=Termhash.find syms f;
       fnargs=List.length args}

let init_pb_stack state =
  let syms= state.uf.syms in
  let pb_stack = Stack.create () in
  let funtab = make_fun_table state in
  let aux inst =
    begin
      let good_classes =
	match inst.qe_lhs_valid with
	  Creates_variables -> Int.Set.empty
	| Normal ->
	    begin
	      try
		let paf= paf_of_patt syms inst.qe_lhs in
		  PafMap.find paf funtab
	      with Not_found -> Int.Set.empty
	    end
	| Trivial typ ->
	    begin
	      try
		Typehash.find state.by_type typ
	      with Not_found -> Int.Set.empty
	    end in
	Int.Set.iter (fun i ->
		       Stack.push
			 {mp_subst = Array.make inst.qe_nvars (-1);
			  mp_inst=inst;
			  mp_stack=[inst.qe_lhs,i]} pb_stack) good_classes
    end;
    begin
      let good_classes =
	match inst.qe_rhs_valid with
	  Creates_variables -> Int.Set.empty
	| Normal ->
	    begin
	      try
		let paf= paf_of_patt syms inst.qe_rhs in
		  PafMap.find paf funtab
	      with Not_found -> Int.Set.empty
	    end
	| Trivial typ ->
	    begin
	      try
		Typehash.find state.by_type typ
	      with Not_found -> Int.Set.empty
	    end in
	Int.Set.iter (fun i ->
		       Stack.push
			 {mp_subst = Array.make inst.qe_nvars (-1);
			  mp_inst=inst;
			  mp_stack=[inst.qe_rhs,i]} pb_stack) good_classes
    end in
    List.iter aux state.quant;
    pb_stack

let find_instances state =
  let pb_stack= init_pb_stack state in
  let res =ref [] in
  let _ =
    debug (fun () -> str "Running E-matching algorithm ... ");
    try
      while true do
	Control.check_for_interrupt ();
	do_match state res pb_stack
      done;
      anomaly (Pp.str "get out of here!")
    with Stack.Empty -> () in
    !res

let rec execute first_run state =
  debug (fun () -> str "Executing ... ");
  try
    while
      Control.check_for_interrupt ();
      one_step state do ()
    done;
    match check_disequalities state with
	None ->
	  if not(Int.Set.is_empty state.pa_classes) then
	    begin
	      debug (fun () -> str "First run was incomplete, completing ... ");
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
		debug (fun () -> str "Out of instances ... ");
		None
	      end
	    else
	      begin
		debug (fun () -> str "Out of depth ... ");
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


