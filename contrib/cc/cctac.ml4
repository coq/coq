(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

(* This file is the interface between the c-c algorithm and Coq *)

open Evd
open Proof_type
open Names
open Libnames
open Nameops
open Inductiveops
open Declarations
open Term
open Termops
open Tacmach
open Tactics
open Tacticals
open Ccalgo
open Tacinterp
open Ccproof
open Pp
open Util
open Format

exception Not_an_eq

let fail()=raise Not_an_eq
    
let constant dir s = lazy (Coqlib.gen_constant "CC" dir s)

let f_equal_theo = constant ["Init";"Logic"] "f_equal"

let eq_rect_theo = constant ["Init";"Logic"] "eq_rect"

(* decompose member of equality in an applicative format *)

let rec decompose_term env t=
  match kind_of_term t with
      App (f,args)->
	let tf=decompose_term env f in
	let targs=Array.map (decompose_term env) args in
	  Array.fold_left (fun s t->Appli (s,t)) tf targs
    | Construct c->
	let (_,oib)=Global.lookup_inductive (fst c) in
	let nargs=mis_constructor_nargs_env env c in
	  Constructor (c,nargs,nargs-oib.mind_nparams)
    | _ ->(Symb t)
	
(* decompose equality in members and type *)
	
let rec eq_type_of_term term=
  match kind_of_term term with
      App (f,args)->
	(try 
	   let ref = reference_of_constr f in
	     if ref=Coqlib.glob_eq && (Array.length args)=3 
	     then (true,args.(0),args.(1),args.(2)) 
	     else 
	       if ref=(Lazy.force Coqlib.coq_not_ref) && 
		 (Array.length args)=1 then
		   let (pol,t,a,b)=eq_type_of_term args.(0) in
		     if pol then (false,t,a,b) else fail ()
	       else fail ()
	 with Not_found -> fail ())
    | Prod (_,eq,ff) ->
	(try 
	   let ref = reference_of_constr ff in
	     if ref=(Lazy.force Coqlib.coq_False_ref) then
	       let (pol,t,a,b)=eq_type_of_term eq in
		 if pol then (false,t,a,b) else fail ()
	     else fail ()
	 with Not_found -> fail ())
    | _ -> fail ()
	
(* read an equality *)
	  
let read_eq env term=
  let (pol,_,t1,t2)=eq_type_of_term term in 
    (pol,(decompose_term env t1,decompose_term env t2))

(* rebuild a term from applicative format *)
    
let rec make_term=function
    Symb s->s
  | Constructor(c,_,_)->mkConstruct c 
  | Appli (s1,s2)->
      make_app [(make_term s2)] s1
and make_app l=function
    Symb s->applistc s l
  | Constructor(c,_,_)->applistc (mkConstruct c) l
  | Appli (s1,s2)->make_app ((make_term s2)::l) s1

(* store all equalities from the context *)
	
let rec read_hyps env=function
    []->[],[]
  | (id,_,e)::hyps->let eq,diseq=read_hyps env hyps in
      try let pol,cpl=read_eq env e in
	if pol then 
	  ((id,cpl)::eq),diseq 
	else 
	  eq,((id,cpl)::diseq)
      with Not_an_eq -> eq,diseq

(* build a problem ( i.e. read the goal as an equality ) *)
	
let make_prb gl=
  let env=pf_env gl in
  let eq,diseq=read_hyps env gl.it.evar_hyps in
    try
      let pol,cpl=read_eq env gl.it.evar_concl in
	if pol then (eq,diseq,Some cpl) else assert false with 
	    Not_an_eq -> (eq,diseq,None)

(* indhyps builds the array of arrays of constructor hyps for (ind largs) *)

let build_projection intype outtype (cstr:constructor) special default gls=
  let env=pf_env gls in 
  let (h,argv) = 
    try destApplication intype with 
	Invalid_argument _ -> (intype,[||])  in
  let ind=destInd h in 
  let types=Inductive.arities_of_constructors env ind in
  let lp=Array.length types in
  let ci=(snd cstr)-1 in
  let branch i=
    let ti=Term.prod_appvect types.(i) argv in
    let rc=fst (Sign.decompose_prod_assum ti) in
    let head=
      if i=ci then special else default in  
      Sign.it_mkLambda_or_LetIn head rc in
  let branches=Array.init lp branch in
  let casee=mkRel 1 in
  let pred=mkLambda(Anonymous,intype,outtype) in
  let case_info=make_default_case_info (pf_env gls) RegularStyle ind in
  let body= mkCase(case_info, pred, casee, branches) in
  let id=pf_get_new_id (id_of_string "t") gls in     
    mkLambda(Name id,intype,body)
  
(* generate an adhoc tactic following the proof tree  *)

let rec proof_tac axioms=function
    Ax id->exact_check (mkVar id)
  | SymAx id->tclTHEN symmetry (exact_check (mkVar id))
  | Refl t->reflexivity
  | Trans (p1,p2)->let t=(make_term (snd (type_proof axioms p1))) in
      (tclTHENS (transitivity t) 
	 [(proof_tac axioms p1);(proof_tac axioms p2)])
  | Congr (p1,p2)->
      fun gls->
	let (f1,f2)=(type_proof axioms p1) 
	and (x1,x2)=(type_proof axioms p2) in
        let tf1=make_term f1 and tx1=make_term x1 
	and tf2=make_term f2 and tx2=make_term x2 in
	let typf=pf_type_of gls tf1 and typx=pf_type_of gls tx1
	and typfx=pf_type_of gls (mkApp(tf1,[|tx1|])) in
	let id=pf_get_new_id (id_of_string "f") gls in
	let appx1=mkLambda(Name id,typf,mkApp(mkRel 1,[|tx1|])) in
	let lemma1=
	  mkApp(Lazy.force f_equal_theo,[|typf;typfx;appx1;tf1;tf2|])
	and lemma2=
	  mkApp(Lazy.force f_equal_theo,[|typx;typfx;tf2;tx1;tx2|]) in
	  (tclTHENS (transitivity (mkApp(tf2,[|tx1|])))
	     [tclTHEN (apply lemma1) (proof_tac axioms p1);
  	      tclFIRST
		[tclTHEN (apply lemma2) (proof_tac axioms p2);
		 reflexivity;
		 fun gls ->
		   errorlabstrm  "Congruence" 
		   (Pp.str 
		      "I don't know how to handle dependent equality")]]
	     gls)
  | Inject (prf,cstr,nargs,argind)  as gprf->
      (fun gls ->
	 let ti,tj=type_proof axioms prf in
	 let ai,aj=type_proof axioms gprf in
	 let cti=make_term ti in
	 let ctj=make_term tj in
	 let cai=make_term ai in
	 let intype=pf_type_of gls cti in
	 let outtype=pf_type_of gls cai in
	 let special=mkRel (1+nargs-argind) in
	 let default=make_term ai in
	 let proj=build_projection intype outtype cstr special default gls in
	 let injt=
	   mkApp (Lazy.force f_equal_theo,[|intype;outtype;proj;cti;ctj|]) in 
	   tclTHEN (apply injt) (proof_tac axioms prf) gls)

let refute_tac axioms disaxioms id p gls =      
  let t1,t2=List.assoc id disaxioms in
  let tt1=make_term t1 and tt2=make_term t2 in
  let intype=pf_type_of gls tt1 in
  let neweq=
    mkApp(constr_of_reference Coqlib.glob_eq,
	  [|intype;tt1;tt2|]) in
  let hid=pf_get_new_id (id_of_string "Heq") gls in
  let false_t=mkApp (mkVar id,[|mkVar hid|]) in
    tclTHENS (true_cut (Name hid) neweq)
      [proof_tac axioms p; simplest_elim false_t] gls

let discriminate_tac axioms cstr p gls =
  let t1,t2=type_proof axioms p in 
  let tt1=make_term t1 and tt2=make_term t2 in
  let intype=pf_type_of gls tt1 in
  let concl=pf_concl gls in
  let outsort=mkType (new_univ ()) in
  let xid=pf_get_new_id (id_of_string "X") gls in
  let tid=pf_get_new_id (id_of_string "t") gls in
  let identity=mkLambda(Name xid,outsort,mkLambda(Name tid,mkRel 1,mkRel 1)) in
  let trivial=pf_type_of gls identity in
  let outtype=mkType (new_univ ()) in
  let pred=mkLambda(Name xid,outtype,mkRel 1) in
  let hid=pf_get_new_id (id_of_string "Heq") gls in     
  let proj=build_projection intype outtype cstr trivial concl gls in
  let injt=mkApp (Lazy.force f_equal_theo,
		  [|intype;outtype;proj;tt1;tt2;mkVar hid|]) in   
  let endt=mkApp (Lazy.force eq_rect_theo,
		  [|outtype;trivial;pred;identity;concl;injt|]) in
  let neweq=mkApp(constr_of_reference Coqlib.glob_eq,[|intype;tt1;tt2|]) in
    tclTHENS (true_cut (Name hid) neweq) 
      [proof_tac axioms p;exact_check endt] gls
      
(* wrap everything *)
	
let cc_tactic gls=
  Library.check_required_library ["Coq";"Init";"Logic"];
  let (axioms,disaxioms,glo)=make_prb gls in
    match (cc_proof axioms disaxioms glo) with
        `Prove_goal p -> proof_tac axioms p gls
      | `Refute_hyp (id,p) -> refute_tac axioms disaxioms id p gls
      | `Discriminate (cstr,p) -> discriminate_tac axioms cstr p gls

(* Tactic registration *)
      
TACTIC EXTEND CC
 [ "Congruence" ] -> [ tclSOLVE [tclTHEN (tclREPEAT introf) cc_tactic] ]
END
   
