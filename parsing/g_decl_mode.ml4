(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id:$ *)
(*i camlp4deps: "parsing/grammar.cma" i*)

open Decl_expr
open Names
open Term
open Genarg
open Pcoq

open Pcoq.Constr
open Pcoq.Tactic
open Pcoq.Vernac_

let none_is_empty = function
    None -> []
  | Some l -> l

GEXTEND Gram
GLOBAL: proof_instr;
  thesis :
    [[ "thesis" -> Plain 
     | "thesis"; "for"; i=ident -> (For i)
     | "thesis"; "["; n=INT ;"]" -> (Sub (int_of_string n))
     ]];
  statement :
    [[ i=ident ; ":" ; c=constr -> {st_label=Name i;st_it=c}
     | i=ident -> {st_label=Anonymous;
		   st_it=Topconstr.CRef (Libnames.Ident (loc, i))}
     | c=constr -> {st_label=Anonymous;st_it=c}
     ]];
  constr_or_thesis :
     [[ t=thesis -> Thesis t ] |
      [ c=constr -> This c
      ]];
  statement_or_thesis : 
    [
      [ t=thesis -> {st_label=Anonymous;st_it=Thesis t} ] 
    |
      [ i=ident ; ":" ; cot=constr_or_thesis -> {st_label=Name i;st_it=cot}
      | i=ident -> {st_label=Anonymous;
		    st_it=This (Topconstr.CRef (Libnames.Ident (loc, i)))}
      | c=constr -> {st_label=Anonymous;st_it=This c}
      ]
    ];
  justification_items : 
    [[ -> Some [] 
     | IDENT "by"; l=LIST1 constr SEP "," -> Some l
     | IDENT "by"; "*"                    -> None ]]
  ;
  justification_method : 
    [[ -> None 
     | "using";  tac = tactic -> Some tac ]]
  ;
  simple_cut_or_thesis :
    [[ ls = statement_or_thesis;
       j = justification_items;
       taco = justification_method 	
	 -> {cut_stat=ls;cut_by=j;cut_using=taco} ]]
  ;
  simple_cut :
    [[ ls = statement;
       j = justification_items;
       taco = justification_method 	
	 -> {cut_stat=ls;cut_by=j;cut_using=taco} ]]
  ;
  elim_type:
    [[ IDENT "induction" -> ET_Induction
     | IDENT "cases" -> ET_Case_analysis ]]
  ;
  block_type :
    [[ IDENT "claim" -> B_claim
     | IDENT "focus" -> B_focus
     | IDENT "proof" -> B_proof
     | et=elim_type -> B_elim et ]]
  ;    
  elim_obj:
    [[ IDENT "on"; c=constr -> Real c
     | IDENT "of"; c=simple_cut -> Virtual c ]]
  ;    
  elim_step:
    [[ IDENT "consider" ; h=vars ; IDENT "from" ; c=constr -> Pconsider (c,h)
     | IDENT "per"; et=elim_type; obj=elim_obj -> Pper (et,obj)]]
  ;
  rew_step :
    [[ "~=" ;         c=simple_cut -> (Rhs,c)       
     | "=~" ;         c=simple_cut -> (Lhs,c)]]
  ;
  cut_step:
    [[ "then"; tt=elim_step -> Pthen tt
     | "then"; c=simple_cut_or_thesis -> Pthen (Pcut c)
     | IDENT "thus"; tt=rew_step -> Pthus (let s,c=tt in Prew (s,c)) 
     | IDENT "thus"; c=simple_cut_or_thesis -> Pthus (Pcut c)
     | IDENT "hence"; c=simple_cut_or_thesis -> Phence (Pcut c)
     | tt=elim_step -> tt
     | tt=rew_step -> let s,c=tt in Prew (s,c); 
     | IDENT "have"; c=simple_cut_or_thesis -> Pcut c;
     | IDENT "claim"; c=statement -> Pclaim c;
     | IDENT "focus"; IDENT "on"; c=statement -> Pfocus c;    
     | "end"; bt = block_type -> Pend bt;
     | IDENT "escape" -> Pescape ]]
  ;
  (* examiner s'il est possible de faire R _ et _ R pour R une relation qcq*)
  loc_id: 
    [[ id=ident -> fun x -> (loc,(id,x)) ]];
  hyp:
    [[ id=loc_id -> id None ;
     | id=loc_id ; ":" ; c=constr -> id (Some c)]]
  ;
  vars:
    [[ name=hyp -> [Hvar name]
     | name=hyp; ","; v=vars -> (Hvar name) :: v
     | name=hyp; IDENT "be"; 
       IDENT "such"; IDENT "that"; h=hyps -> (Hvar name)::h
     | name=hyp; 
       IDENT "such"; IDENT "that"; h=hyps -> (Hvar name)::h
     ]]
  ;
  hyps:  
    [[ IDENT "we"; IDENT "have"; v=vars -> v
     | st=statement; IDENT "and"; h=hyps  -> Hprop st::h
     | st=statement; IDENT "and"; v=vars  -> Hprop st::v
     | st=statement -> [Hprop st]
     ]]
  ;
  vars_or_thesis:
    [[name=hyp -> [Hvar name] 
     |name=hyp; ","; v=vars_or_thesis -> (Hvar name) :: v
     |name=hyp; OPT[IDENT "be"]; 
      IDENT "such"; IDENT "that"; h=hyps_or_thesis -> (Hvar name)::h
     ]]
  ;
  hyps_or_thesis:  
    [[ IDENT "we"; IDENT "have"; v=vars_or_thesis -> v
     | st=statement_or_thesis; IDENT "and"; h=hyps_or_thesis  -> Hprop st::h
     | st=statement_or_thesis; IDENT "and"; v=vars_or_thesis  -> Hprop st::v
     | st=statement_or_thesis -> [Hprop st];
     ]]
  ;
  intro_step:
    [[ IDENT "suppose" ; h=hyps -> Psuppose h
     | IDENT "suppose" ; IDENT "it"; IDENT "is" ; c=pattern LEVEL "0" ;
       po=OPT[ IDENT "with"; p=LIST1 hyp -> p ] ; 
       ho=OPT[ IDENT "and" ; h=hyps_or_thesis -> h ] -> 
	 Pcase (none_is_empty po,c,none_is_empty ho)
     | "let" ; v=vars -> Plet v	 
     | IDENT "take"; witnesses = LIST1 constr SEP ","  -> Ptake witnesses
     | IDENT "assume"; h=hyps -> Passume h
     | IDENT "given"; h=vars -> Pgiven h
     | IDENT "define"; id=ident; args=LIST0 hyp; 
       "as"; body=constr -> Pdefine(id,args,body)
     | IDENT "reconsider"; id=ident; "as" ; typ=constr -> Pcast (This id,typ)
     | IDENT "reconsider"; t=thesis; "as" ; typ=constr -> Pcast (Thesis t ,typ)
     ]]
  ;
  emphasis : 
    [[ -> 0
     | "*" -> 1
     | "**" -> 2
     | "***" -> 3
     ]]
  ;
  bare_proof_instr:
    [[ c = cut_step -> c ;
     | i = intro_step -> i ]]
  ;
  proof_instr :
    [[ e=emphasis;i=bare_proof_instr -> {emph=e;instr=i}]]
  ;
END;;

 
