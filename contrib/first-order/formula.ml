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

type ('a,'b)sum=Left of 'a|Right of 'b

type kind_of_formula=
   Arrow of constr*constr
  |And of inductive*constr list
  |Or of inductive*constr list
  |Exists of inductive*constr*constr*constr
  |Forall of constr*constr
  |Atom of constr
  |False

type counter = bool -> int

let newcnt ()=
  let cnt=ref (-1) in
    fun b->if b then incr cnt;!cnt

let constant path str ()=Coqlib.gen_constant "User" ["Init";path] str

let op2bool=function Some _->true |None->false

let id_ex=constant "Logic" "ex"
let id_sig=constant "Specif" "sig"
let id_sigT=constant "Specif" "sigT"
let id_sigS=constant "Specif" "sigS"
let id_not=constant "Logic" "not"
 
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

let match_with_not_term t=
  match match_with_nottype t with 
    | None ->
	(match kind_of_term t with
	     App (no,b) when no=id_not ()->Some (no,b.(0))
	   | _->None)
    | o -> o

let rec nb_prod_after n c=
  match kind_of_term c with
    | Prod (_,_,b) ->if n>0 then nb_prod_after (n-1) b else 
	1+(nb_prod_after 0 b)
    | _            -> 0

let nhyps mip = 
  let constr_types = mip.mind_nf_lc in 
  let nhyps = nb_prod_after mip.mind_nparams in	
    Array.map nhyps constr_types

let construct_nhyps ind= nhyps (snd (Global.lookup_inductive ind))
      
(* builds the array of arrays of constructor hyps for (ind Vargs)*)
let ind_hyps ind largs= 
  let (mib,mip) = Global.lookup_inductive ind in
    if Inductiveops.mis_is_recursive (ind,mib,mip) then 
      failwith "no_recursion" else      
	let n=mip.mind_nparams in
	  if n<>(List.length largs) then anomaly "params ?" else
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
		     None -> Atom cciterm 
		   | Some (i,l)->
		       let ind=destInd i in
		       let (mib,mip) = Global.lookup_inductive ind in
			 if Inductiveops.mis_is_recursive (ind,mib,mip) then
			   Atom cciterm 
			 else
			   match Array.length mip.mind_consnames with
			       0->False
			     | 1->And(ind,l)
			     | _->Or(ind,l) 

let build_atoms metagen=
  let rec build_rec env polarity cciterm =
    match kind_of_formula cciterm with
	False->[]
      | Arrow (a,b)->
	  (build_rec env (not polarity) a)@
	  (build_rec env polarity b)
      | And(i,l) | Or(i,l)->
	  let v = ind_hyps i l in
	    Array.fold_right
	      (fun l accu->
		 List.fold_right 
		 (fun (_,_,t) accu0->
		    (build_rec env polarity t)@accu0) l accu) v []
      | Forall(_,b)|Exists(_,_,b,_)->
	  let var=mkMeta (metagen true) in
	    build_rec (var::env) polarity b 
      | Atom t->
	  [polarity,(substnl env 0 cciterm)]
  in build_rec []
       
type right_pattern =
    Rand
  | Ror 
  | Rforall
  | Rexists of int*constr
  | Rarrow
      
type right_formula =
    Complex of right_pattern*((bool*constr) list)
  | Atomic of constr
      
type left_pattern=
    Lfalse    
  | Land of inductive
  | Lor of inductive 
  | Lforall of int*constr
  | Lexists
  | LAatom of constr
  | LAfalse
  | LAand of inductive*constr list
  | LAor of inductive*constr list
  | LAforall of constr
  | LAexists of inductive*constr*constr*constr
  | LAarrow of constr*constr*constr
      
type left_formula={id:identifier;
		   pat:left_pattern;
		   atoms:(bool*constr) list}
    
exception Is_atom of constr

let build_left_entry nam typ metagen=
  try 
    let pattern=
      match kind_of_formula typ with
	  False        ->  Lfalse
	| Atom a       ->  raise (Is_atom a)
	| And(i,_)         ->  Land i
	| Or(i,_)          ->  Lor i
	| Exists (_,_,_,_) ->  Lexists
	| Forall (d,_) -> let m=1+(metagen false) in Lforall(m,d)
	| Arrow (a,b) ->
	    (match kind_of_formula a with
		 False->      LAfalse
	       | Atom a->     LAatom a
	       | And(i,l)->      LAand(i,l)
	       | Or(i,l)->       LAor(i,l)
	       | Arrow(a,c)-> LAarrow(a,c,b)
	       | Exists(i,a,_,p)->LAexists(i,a,p,b)
	       | Forall(_,_)->LAforall a) in    
    let l=build_atoms metagen false typ in
      Left {id=nam;pat=pattern;atoms=l}
  with Is_atom a-> Right a

let build_right_entry typ metagen=
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
	| Arrow (a,b) -> Rarrow in
    let l=build_atoms metagen true typ in
      Complex(pattern,l)
  with Is_atom a-> Atomic a

