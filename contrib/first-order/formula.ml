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

type counter = bool -> metavariable

exception Is_atom of constr

let meta_succ m = m+1

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

(* indhyps builds the array of arrays of constructor hyps for (ind largs)*)
let ind_hyps nevar ind largs= 
  let (mib,mip) = Global.lookup_inductive ind in
  let n = mip.mind_nparams in
    (* assert (n=(List.length largs));*)
  let lp=Array.length mip.mind_consnames in
  let types= mip.mind_nf_lc in   
  let lp=Array.length types in     
  let myhyps i=
    let t1=Term.prod_applist types.(i) largs in
    let t2=snd (Sign.decompose_prod_n_assum nevar t1) in
      fst (Sign.decompose_prod_assum t2) in
    Array.init lp myhyps

let constant str = Coqlib.gen_constant "User" ["Init";"Logic"] str

let id_not=lazy (destConst (constant "not"))
let id_iff=lazy (destConst (constant "iff"))

let match_with_evaluable gl t=
  let env=pf_env gl in
    match kind_of_term t with
	App (hd,b)-> 
	  (match kind_of_term hd with
	       Const cst->
		 if (*Environ.evaluable_constant cst env*) 
		   cst=(Lazy.force id_not) || 
		   cst=(Lazy.force id_iff) then 
		   Some(EvalConstRef cst,t)
		 else None
	     | _-> None)
      | _-> None
	
type kind_of_formula=
    Arrow of constr*constr
  | And of inductive*constr list
  | Or of inductive*constr list
  | Exists of inductive*constr list
  | Forall of constr*constr
  | Atom of constr
  | Evaluable of evaluable_global_reference*constr
  | False
      
let rec kind_of_formula gl term =
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
			 match match_with_evaluable gl cciterm with 
			     Some (ec,t)->Evaluable (ec,t)
			   | None ->Atom cciterm
  
type atoms = {positive:constr list;negative:constr list}

let no_atoms = (false,{positive=[];negative=[]})

let build_atoms gl metagen polarity cciterm =
  let trivial =ref false
  and positive=ref []
  and negative=ref [] in
  let pfenv=lazy (pf_env gl) in
  let rec build_rec env polarity cciterm =
    match kind_of_formula gl cciterm with
	False->if not polarity then trivial:=true
      | Arrow (a,b)->
	  build_rec env (not polarity) a;
	  build_rec env polarity b
      | And(i,l) | Or(i,l)->
	  let v = ind_hyps 0 i l in
	  let g i _ (_,_,t) =
	    build_rec env polarity (lift i t) in
	  let f l =
	    list_fold_left_i g (1-(List.length l)) () l in
	    if polarity && (* we have a constant constructor *)
	      array_exists (function []->true|_->false) v 
	    then trivial:=true;
	    Array.iter f v 
      | Exists(i,l)->
	  let var=mkMeta (metagen true) in
	  let v =(ind_hyps 1 i l).(0) in
	  let g i _ (_,_,t) =
	    build_rec (var::env) polarity (lift i t) in
	    list_fold_left_i g (2-(List.length l)) () v
      | Forall(_,b)->
	  let var=mkMeta (metagen true) in
	    build_rec (var::env) polarity b
      | Atom t->
	  let unsigned=substnl env 0 t in
	    if polarity then 
	      positive:= unsigned :: !positive 
	    else 
	      negative:= unsigned :: !negative
      | Evaluable(ec,t)->
	  let nt=Tacred.unfoldn [[1],ec] (Lazy.force pfenv) 
		   (Refiner.sig_sig gl) t in
	    build_rec env polarity nt
  in 
    build_rec [] polarity cciterm;
    (!trivial,
     {positive= !positive;
      negative= !negative})

       
type right_pattern =
    Rand
  | Ror 
  | Rforall
  | Rexists of metavariable*constr*bool
  | Rarrow
  | Revaluable of evaluable_global_reference
      
type right_formula =
    Complex of right_pattern*constr*atoms
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
  | Lforall of metavariable*constr*bool
  | Lexists of inductive
  | Levaluable of evaluable_global_reference
  | LA of constr*left_arrow_pattern

type left_formula={id:global_reference;
		   constr:constr;
		   pat:left_pattern;
		   atoms:atoms;
		   internal:bool}
    
let build_left_entry nam typ internal gl metagen=
  try 
    let m=meta_succ(metagen false) in
    let trivial,atoms=
      if !qflag then 
	build_atoms gl metagen false typ 
      else no_atoms in
    let pattern=
      match kind_of_formula gl typ with
	  False        ->  Lfalse
	| Atom a       ->  raise (Is_atom a)
	| And(i,_)         ->  Land i
	| Or(i,_)          ->  Lor i
	| Exists (ind,_) ->  Lexists ind 
	| Forall (d,_) -> 
	    Lforall(m,d,trivial)
	| Evaluable (egc,_) ->Levaluable egc 
	| Arrow (a,b) ->LA (a, 
			    match kind_of_formula gl a with
				False->      LLfalse
			      | Atom t->     LLatom
			      | And(i,l)->      LLand(i,l)
			      | Or(i,l)->       LLor(i,l)
			      | Arrow(a,c)-> LLarrow(a,c,b)
			      | Exists(i,l)->LLexists(i,l)
			      | Forall(_,_)->LLforall a
			      | Evaluable (egc,_)-> LLevaluable egc) in
      Left {id=nam;
	    constr=typ;
	    pat=pattern;
	    atoms=atoms;
	    internal=internal}
  with Is_atom a-> Right a
    
let build_right_entry typ gl metagen=
  try
    let m=meta_succ(metagen false) in 
    let trivial,atoms=
      if !qflag then 
	build_atoms gl metagen true typ
      else no_atoms in
    let pattern=
      match kind_of_formula gl typ with
	  False        -> raise (Is_atom typ)
	| Atom a       -> raise (Is_atom a)
	| And(_,_)        -> Rand
	| Or(_,_)         -> Ror
	| Exists (i,l) -> 
	    let (_,_,d)=list_last (ind_hyps 0 i l).(0) in
	      Rexists(m,d,trivial)
	| Forall (_,a) -> Rforall 
	| Arrow (a,b) -> Rarrow 
	| Evaluable (egc,_)->Revaluable egc in
      Complex(pattern,typ,atoms)
  with Is_atom a-> Atomic a

