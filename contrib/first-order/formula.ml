(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Hipattern
open Names
open Term
open Termops
open Reductionops
open Tacmach
open Util
open Declarations
open Libnames

let qflag=ref true

let (=?) f g i1 i2 j1 j2=
  let c=f i1 i2 in
    if c=0 then g j1 j2 else c

let (==?) fg h i1 i2 j1 j2 k1 k2=
  let c=fg i1 i2 j1 j2 in
    if c=0 then h k1 k2 else c

type ('a,'b)sum=Left of 'a|Right of 'b
	
type kind_of_formula=
   Arrow of constr*constr
  |And of inductive*constr list
  |Or of inductive*constr list
  |Exists of inductive*constr*constr*constr
  |Forall of constr*constr
  |Atom of constr
  |Evaluable of evaluable_global_reference*constr
  |False

type counter = bool -> int

let constant path str ()=Coqlib.gen_constant "User" ["Init";path] str

let op2bool=function Some _->true |None->false

let id_ex=constant "Logic" "ex"
let id_sig=constant "Specif" "sig"
let id_sigT=constant "Specif" "sigT"
let id_sigS=constant "Specif" "sigS"
let id_not=constant "Logic" "not"
let id_iff=constant "Logic" "iff"

let is_ex t = 
  t=(id_ex ()) || 
    t=(id_sig ()) || 
      t=(id_sigT ()) || 
	t=(id_sigS ())

let match_with_exist_term t=
  match kind_of_term t with
      App(t,v)->
	if t=id_ex () && (Array.length v)=2 then
	  let p=v.(1) in
	    match kind_of_term p with 
		Lambda(na,a,b)->Some(t,a,b,p)
	      | _ ->Some(t,v.(0),mkApp(p,[|mkRel 1|]),p)
	else None
    | _->None

let match_with_evaluable t=
  match kind_of_term t with
      App (hd,b)-> 
	if (hd=id_not () && (Array.length b) = 1) ||
	  (hd=id_iff () && (Array.length b) = 2) then 
	    Some(destConst hd,t)
	else None
    | _-> None

let rec nb_prod_after n c=
  match kind_of_term c with
    | Prod (_,_,b) ->if n>0 then nb_prod_after (n-1) b else 
	1+(nb_prod_after 0 b)
    | _ -> 0

let nhyps mip = 
  let constr_types = mip.mind_nf_lc in 
  let hyp = nb_prod_after mip.mind_nparams in	
    Array.map hyp constr_types

let construct_nhyps ind= nhyps (snd (Global.lookup_inductive ind))
    
exception Dependent_Inductive

(* builds the array of arrays of constructor hyps for (ind Vargs)*)
let ind_hyps ind largs= 
  let (mib,mip) = Global.lookup_inductive ind in
  let n = mip.mind_nparams in
    if n<>(List.length largs) then 
      raise Dependent_Inductive
    else
      let p=nhyps mip in
      let lp=Array.length p in
      let types= mip.mind_nf_lc in   
      let myhyps i=
	let t1=Term.prod_applist types.(i) largs in
	  fst (Sign.decompose_prod_n_assum p.(i) t1) in
	Array.init lp myhyps

let kind_of_formula cciterm =
  match match_with_imp_term cciterm with
      Some (a,b)-> Arrow(a,(pop b))
    |_->
       match match_with_forall_term cciterm with
	   Some (_,a,b)-> Forall(a,b)
	 |_-> 
	    match match_with_exist_term cciterm with
		Some (i,a,b,p)-> Exists((destInd i),a,b,p)
	      |_-> 
		 match match_with_nodep_ind cciterm with
		     Some (i,l)->
		       let ind=destInd i in
		       let (mib,mip) = Global.lookup_inductive ind in
			 if Inductiveops.mis_is_recursive (ind,mib,mip) then
			   Atom cciterm 
			 else
			   (match Array.length mip.mind_consnames with
				0->False
			      | 1->And(ind,l)
			      | _->Or(ind,l)) 
		   | None -> 
		       match match_with_evaluable cciterm with 
			   Some (cst,t)->Evaluable ((EvalConstRef cst),t)
			 | None ->Atom cciterm

 
let build_atoms gl metagen=
  let rec build_rec env polarity cciterm =
    match kind_of_formula cciterm with
	False->[]
      | Arrow (a,b)->
	  (build_rec env (not polarity) a)@
	  (build_rec env polarity b)
      | And(i,l) | Or(i,l)->
	  (try
	     let v = ind_hyps i l in
	     let g i accu (_,_,t) =
	       (build_rec env polarity (lift i t))@accu in
	     let f l accu =
	       list_fold_left_i g (1-(List.length l)) accu l in
	       Array.fold_right f v [] 
	   with Dependent_Inductive ->
	     [polarity,(substnl env 0 cciterm)])
      | Forall(_,b)|Exists(_,_,b,_)->
	  let var=mkMeta (metagen true) in
	    build_rec (var::env) polarity b 
      | Atom t->
	  [polarity,(substnl env 0 cciterm)]
      | Evaluable(ec,t)->
	  let nt=Tacred.unfoldn [[1],ec] (pf_env gl) (Refiner.sig_sig gl) t in
	  build_rec env polarity nt
  in build_rec []
       
type right_pattern =
    Rand
  | Ror 
  | Rforall
  | Rexists of int*constr
  | Rarrow
  | Revaluable of evaluable_global_reference
      
type right_formula =
    Complex of right_pattern*constr*((bool*constr) list)
  | Atomic of constr
      
type left_arrow_pattern=
    LLatom
  | LLfalse
  | LLand of inductive*constr list
  | LLor of inductive*constr list
  | LLforall of constr
  | LLexists of inductive*constr*constr*constr
  | LLarrow of constr*constr*constr
  | LLevaluable of evaluable_global_reference

type left_pattern=
    Lfalse    
  | Land of inductive
  | Lor of inductive 
  | Lforall of int*constr
  | Lexists
  | Levaluable of evaluable_global_reference
  | LA of constr*left_arrow_pattern

type left_formula={id:global_reference;
		   constr:constr;
		   pat:left_pattern;
		   atoms:(bool*constr) list;
		   internal:bool}
    
exception Is_atom of constr

let build_left_entry nam typ internal gl metagen=
  try 
    let pattern=
      match kind_of_formula typ with
	  False        ->  Lfalse
	| Atom a       ->  raise (Is_atom a)
	| And(i,_)         ->  Land i
	| Or(i,_)          ->  Lor i
	| Exists (_,_,_,_) ->  Lexists
	| Forall (d,_) -> let m=1+(metagen false) in Lforall(m,d)
	| Evaluable (egc,_) ->Levaluable egc 
	| Arrow (a,b) ->LA (a, 
			    match kind_of_formula a with
				False->      LLfalse
			      | Atom t->     LLatom
			      | And(i,l)->      LLand(i,l)
			      | Or(i,l)->       LLor(i,l)
			      | Arrow(a,c)-> LLarrow(a,c,b)
			      | Exists(i,a,_,p)->LLexists(i,a,p,b)
			      | Forall(_,_)->LLforall a
			      | Evaluable (egc,_)-> LLevaluable egc) in    
    let l=
      if !qflag then 
	build_atoms gl metagen false typ 
      else [] in
      Left {id=nam;
	    constr=typ;
	    pat=pattern;
	    atoms=l;
	    internal=internal}
  with Is_atom a-> Right a
    
let build_right_entry typ gl metagen=
  try
    let pattern=
      match kind_of_formula typ with
	  False        -> raise (Is_atom typ)
	| Atom a       -> raise (Is_atom a)
	| And(_,_)        -> Rand
	| Or(_,_)         -> Ror
	| Exists (_,d,_,_) -> 
	    let m=1+(metagen false) in Rexists(m,d) 
	| Forall (_,a) -> Rforall 
	| Arrow (a,b) -> Rarrow 
	| Evaluable (egc,_)->Revaluable egc in
    let l=
      if !qflag then 
	build_atoms gl metagen true typ
      else [] in
      Complex(pattern,typ,l)
  with Is_atom a-> Atomic a

