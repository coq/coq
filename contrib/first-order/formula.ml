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

type ('a,'b) sum = Left of 'a | Right of 'b
	
type kind_of_formula=
   Arrow of constr*constr
  |And of inductive*constr list
  |Or of inductive*constr list
  |Exists of inductive*constr list
  |Forall of constr*constr
  |Atom of constr
  |Evaluable of evaluable_global_reference*constr
  |False

type counter = bool -> metavariable

let constant path str () = Coqlib.gen_constant "User" ["Init";path] str

let op2bool = function Some _->true | None->false

let id_not=constant "Logic" "not"
let id_iff=constant "Logic" "iff"

let defined_connectives=lazy
  [[],EvalConstRef (destConst (id_not ()));
   [],EvalConstRef (destConst (id_iff ()))]

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

(* builds the array of arrays of constructor hyps for (ind largs)*)

let ind_hyps nevar ind largs= 
  let (mib,mip) = Global.lookup_inductive ind in
  let n = mip.mind_nparams in
(*  assert (n=(List.length largs));*)
    let lp=Array.length mip.mind_consnames in
    let types= mip.mind_nf_lc in   
    let lp=Array.length types in     
    let myhyps i=
      let t1=Term.prod_applist types.(i) largs in
      let t2=snd (Sign.decompose_prod_n_assum nevar t1) in
	fst (Sign.decompose_prod_assum t2) in
      Array.init lp myhyps

let kind_of_formula term =
  let cciterm=whd_betaiotazeta term in
    match match_with_imp_term cciterm with
	Some (a,b)-> Arrow(a,(pop b))
      |_->
	 match match_with_forall_term cciterm with
	     Some (_,a,b)-> Forall(a,b)
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
		| _ ->  
		    match match_with_sigma_type cciterm with
			Some (i,l)-> Exists((destInd i),l)
		      |_-> 
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
	  let v = ind_hyps 0 i l in
	  let g i accu (_,_,t) =
	    (build_rec env polarity (lift i t))@accu in
	  let f l accu =
	    list_fold_left_i g (1-(List.length l)) accu l in
	    Array.fold_right f v [] 
      | Exists(i,l)->
	  let var=mkMeta (metagen true) in
	  let v =(ind_hyps 1 i l).(0) in
	  let g i accu (_,_,t) =
	    (build_rec (var::env) polarity (lift i t))@accu in
	    list_fold_left_i g (2-(List.length l)) [] v
      | Forall(_,b)->
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
  | Rexists of metavariable*constr
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
  | LLexists of inductive*constr list
  | LLarrow of constr*constr*constr
  | LLevaluable of evaluable_global_reference

type left_pattern=
    Lfalse    
  | Land of inductive
  | Lor of inductive 
  | Lforall of metavariable*constr
  | Lexists
  | Levaluable of evaluable_global_reference
  | LA of constr*left_arrow_pattern

type left_formula={id:global_reference;
		   constr:constr;
		   pat:left_pattern;
		   atoms:(bool*constr) list;
		   internal:bool}
    
exception Is_atom of constr

let meta_succ m = m+1

let build_left_entry nam typ internal gl metagen=
  try 
    let pattern=
      match kind_of_formula typ with
	  False        ->  Lfalse
	| Atom a       ->  raise (Is_atom a)
	| And(i,_)         ->  Land i
	| Or(i,_)          ->  Lor i
	| Exists (_,_) ->  Lexists
	| Forall (d,_) -> let m=meta_succ(metagen false) in Lforall(m,d)
	| Evaluable (egc,_) ->Levaluable egc 
	| Arrow (a,b) ->LA (a, 
			    match kind_of_formula a with
				False->      LLfalse
			      | Atom t->     LLatom
			      | And(i,l)->      LLand(i,l)
			      | Or(i,l)->       LLor(i,l)
			      | Arrow(a,c)-> LLarrow(a,c,b)
			      | Exists(i,l)->LLexists(i,l)
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
	| Exists (i,l) -> 
	    let m=meta_succ(metagen false) in 
	    let (_,_,d)=list_last (ind_hyps 0 i l).(0) in
	      Rexists(m,d)
	| Forall (_,a) -> Rforall 
	| Arrow (a,b) -> Rarrow 
	| Evaluable (egc,_)->Revaluable egc in
    let l=
      if !qflag then 
	build_atoms gl metagen true typ
      else [] in
      Complex(pattern,typ,l)
  with Is_atom a-> Atomic a

