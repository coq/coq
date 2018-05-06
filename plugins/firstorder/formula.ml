(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Hipattern
open Names
open Constr
open EConstr
open Vars
open Termops
open Util
open Declarations
open Globnames

module RelDecl = Context.Rel.Declaration

let qflag=ref true

let red_flags=ref CClosure.betaiotazeta

let (=?) f g i1 i2 j1 j2=
  let c=f i1 i2 in
    if Int.equal c 0 then g j1 j2 else c

let (==?) fg h i1 i2 j1 j2 k1 k2=
  let c=fg i1 i2 j1 j2 in
    if Int.equal c 0 then h k1 k2 else c

type ('a,'b) sum = Left of 'a | Right of 'b

type counter = bool -> metavariable

exception Is_atom of constr

let meta_succ m = m+1

let rec nb_prod_after n c=
  match Constr.kind c with
    | Prod (_,_,b) ->if n>0 then nb_prod_after (n-1) b else
	1+(nb_prod_after 0 b)
    | _ -> 0

let construct_nhyps env ind =
  let nparams = (fst (Global.lookup_inductive (fst ind))).mind_nparams in
  let constr_types = Inductiveops.arities_of_constructors env ind in
  let hyp = nb_prod_after nparams in
    Array.map hyp constr_types

(* indhyps builds the array of arrays of constructor hyps for (ind largs)*)
let ind_hyps env sigma nevar ind largs =
  let types= Inductiveops.arities_of_constructors env ind in
  let myhyps t =
    let t = EConstr.of_constr t in
    let nparam_decls = Context.Rel.length (fst (Global.lookup_inductive (fst ind))).mind_params_ctxt in
    let t1=Termops.prod_applist_assum sigma nparam_decls t largs in
    let t2=snd (decompose_prod_n_assum sigma nevar t1) in
      fst (decompose_prod_assum sigma t2) in
    Array.map myhyps types

let special_nf env sigma t =
  Reductionops.clos_norm_flags !red_flags env sigma t

let special_whd env sigma t =
  Reductionops.clos_whd_flags !red_flags env sigma t

type kind_of_formula=
    Arrow of constr*constr
  | False of pinductive*constr list
  | And of pinductive*constr list*bool
  | Or of pinductive*constr list*bool
  | Exists of pinductive*constr list
  | Forall of constr*constr
  | Atom of constr

let pop t = Vars.lift (-1) t

let kind_of_formula env sigma term =
  let normalize = special_nf env sigma in
  let cciterm = special_whd env sigma term in
    match match_with_imp_term sigma cciterm with
	Some (a,b)-> Arrow (a, pop b)
      |_->
	 match match_with_forall_term sigma cciterm with
	     Some (_,a,b)-> Forall (a, b)
	   |_->
	      match match_with_nodep_ind sigma cciterm with
		  Some (i,l,n)->
		    let ind,u=EConstr.destInd sigma i in
		    let u = EConstr.EInstance.kind sigma u in
		    let (mib,mip) = Global.lookup_inductive ind in
		    let nconstr=Array.length mip.mind_consnames in
		      if Int.equal nconstr 0 then
			False((ind,u),l)
		      else
			let has_realargs=(n>0) in
			let is_trivial=
			  let is_constant c =
			    Int.equal (nb_prod sigma (EConstr.of_constr c)) mib.mind_nparams in
			    Array.exists is_constant mip.mind_nf_lc in
			  if Inductiveops.mis_is_recursive (ind,mib,mip) ||
			    (has_realargs && not is_trivial)
			  then
			    Atom cciterm
			  else
			    if Int.equal nconstr 1 then
			      And((ind,u),l,is_trivial)
			    else
			      Or((ind,u),l,is_trivial)
		| _ ->
		    match match_with_sigma_type sigma cciterm with
			Some (i,l)->
                          let (ind, u) = EConstr.destInd sigma i in
                          let u = EConstr.EInstance.kind sigma u in
                          Exists((ind, u), l)
		      |_-> Atom (normalize cciterm)

type atoms = {positive:constr list;negative:constr list}

type side = Hyp | Concl | Hint

let no_atoms = (false,{positive=[];negative=[]})

let dummy_id=VarRef (Id.of_string "_") (* "_" cannot be parsed *)

let build_atoms env sigma metagen side cciterm =
  let trivial =ref false
  and positive=ref []
  and negative=ref [] in
  let normalize=special_nf env sigma in
  let rec build_rec subst polarity cciterm=
    match kind_of_formula env sigma cciterm with
	False(_,_)->if not polarity then trivial:=true
      | Arrow (a,b)->
	  build_rec subst (not polarity) a;
	  build_rec subst polarity b
      | And(i,l,b) | Or(i,l,b)->
	  if b then
	    begin
	      let unsigned=normalize (substnl subst 0 cciterm) in
		if polarity then
		  positive:= unsigned :: !positive
		else
		  negative:= unsigned :: !negative
	    end;
	  let v = ind_hyps env sigma 0 i l in
	  let g i _ decl =
	    build_rec subst polarity (lift i (RelDecl.get_type decl)) in
	  let f l =
	    List.fold_left_i g (1-(List.length l)) () l in
	    if polarity && (* we have a constant constructor *)
	      Array.exists (function []->true|_->false) v
	    then trivial:=true;
	    Array.iter f v
      | Exists(i,l)->
	  let var=mkMeta (metagen true) in
	  let v =(ind_hyps env sigma 1 i l).(0) in
	  let g i _ decl =
	    build_rec (var::subst) polarity (lift i (RelDecl.get_type decl)) in
	    List.fold_left_i g (2-(List.length l)) () v
      | Forall(_,b)->
	  let var=mkMeta (metagen true) in
	    build_rec (var::subst) polarity b
      | Atom t->
	  let unsigned=substnl subst 0 t in
	    if not (isMeta sigma unsigned) then (* discarding wildcard atoms *)
	      if polarity then
		positive:= unsigned :: !positive
	      else
		negative:= unsigned :: !negative in
    begin
      match side with
	  Concl    -> build_rec [] true cciterm
	| Hyp      -> build_rec [] false cciterm
	| Hint     ->
	    let rels,head=decompose_prod sigma cciterm in
	    let subst=List.rev_map (fun _->mkMeta (metagen true)) rels in
	      build_rec subst false head;trivial:=false (* special for hints *)
    end;
    (!trivial,
     {positive= !positive;
      negative= !negative})

type right_pattern =
    Rarrow
  | Rand
  | Ror
  | Rfalse
  | Rforall
  | Rexists of metavariable*constr*bool

type left_arrow_pattern=
    LLatom
  | LLfalse of pinductive*constr list
  | LLand of pinductive*constr list
  | LLor of pinductive*constr list
  | LLforall of constr
  | LLexists of pinductive*constr list
  | LLarrow of constr*constr*constr

type left_pattern=
    Lfalse
  | Land of pinductive
  | Lor of pinductive
  | Lforall of metavariable*constr*bool
  | Lexists of pinductive
  | LA of constr*left_arrow_pattern

type t={id:GlobRef.t;
	constr:constr;
	pat:(left_pattern,right_pattern) sum;
	atoms:atoms}

let build_formula env sigma side nam typ metagen=
  let normalize = special_nf env sigma in
    try
      let m=meta_succ(metagen false) in
      let trivial,atoms=
	if !qflag then
	  build_atoms env sigma metagen side typ
	else no_atoms in
      let pattern=
	match side with
	    Concl ->
	      let pat=
		match kind_of_formula env sigma typ with
		    False(_,_)        -> Rfalse
		  | Atom a       -> raise (Is_atom a)
		  | And(_,_,_)        -> Rand
		  | Or(_,_,_)         -> Ror
		  | Exists (i,l) ->
		      let d = RelDecl.get_type (List.last (ind_hyps env sigma 0 i l).(0)) in
			Rexists(m,d,trivial)
		  | Forall (_,a) -> Rforall
		  | Arrow (a,b) -> Rarrow in
		Right pat
	  | _ ->
	      let pat=
		match kind_of_formula env sigma typ with
		    False(i,_)        ->  Lfalse
		  | Atom a       ->  raise (Is_atom a)
		  | And(i,_,b)         ->
		      if b then
			let nftyp=normalize typ in raise (Is_atom nftyp)
		      else Land i
		  | Or(i,_,b)          ->
		      if b then
			let nftyp=normalize typ in raise (Is_atom nftyp)
		      else Lor i
		  | Exists (ind,_) ->  Lexists ind
		  | Forall (d,_) ->
		      Lforall(m,d,trivial)
		  | Arrow (a,b) ->
		      let nfa=normalize a in
			LA (nfa,
			    match kind_of_formula env sigma a with
				False(i,l)-> LLfalse(i,l)
			      | Atom t->     LLatom
			      | And(i,l,_)-> LLand(i,l)
			      | Or(i,l,_)->  LLor(i,l)
			      | Arrow(a,c)-> LLarrow(a,c,b)
			      | Exists(i,l)->LLexists(i,l)
			      | Forall(_,_)->LLforall a) in
		Left pat
      in
	Left {id=nam;
	      constr=normalize typ;
	      pat=pattern;
	      atoms=atoms}
    with Is_atom a-> Right a (* already in nf *)

