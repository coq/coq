(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Formula
open Sequent
open Unify
open Rules
open Util
open Term
open Tacmach
open Tactics
open Tacticals
open Termops
open Reductionops
open Declarations
open Formula
open Sequent
open Libnames

let rev_rels n t= (* requires n = max (free_rels t) *) 
  let l=list_tabulate (fun i->mkRel (n-i)) n in
    substl l t
 	  
let renum_metas_from k n t=(* requires n = max (free_rels t) *)
  let l=list_tabulate (fun i->mkMeta (k+i)) n in
    substl l t

(* ordre lexico:
   nombre de metas dans terme;
   profondeur de matching;
   le reste
*)
      
let compare_instance inst1 inst2=
	match inst1,inst2 with
	    Phantom(d1),Phantom(d2)->
	      (OrderedConstr.compare d1 d2)
	  | Real((m1,c1),n1),Real((m2,c2),n2)->
	      ((-) =? (-) ==? OrderedConstr.compare) m2 m1 n2 n1 c1 c2
	  | Phantom(_),Real((m,_),_)-> if m=0 then -1 else 1
	  | Real((m,_),_),Phantom(_)-> if m=0 then 1 else -1

module OrderedRightInstance=
struct 
  type t = instance
  let compare = compare_instance
end

module OrderedLeftInstance=
struct
  type t=instance * Libnames.global_reference
  let compare (inst1,id1) (inst2,id2)=
    (compare_instance =? Pervasives.compare) inst1 inst2 id1 id2
    (* we want a __decreasing__ total order *)
end
  
module RIS=Set.Make(OrderedRightInstance)
module LIS=Set.Make(OrderedLeftInstance)

let make_goal_atoms seq=
  match seq.gl with
      Atomic t->{negative=[];positive=[t]}
    | Complex (_,_,l)->l 

let make_left_atoms seq=
    {negative=seq.latoms;positive=[]}

let do_sequent setref triv add mkelt seq i dom atoms=
  let flag=ref true in
  let phref=ref triv in
  let do_atoms a1 a2 =
    let do_pair t1 t2 = 
      match unif_atoms i dom t1 t2 with
	  None->()
	| Some (Phantom _) ->phref:=true
	| Some c ->flag:=false;setref:=add (mkelt c) !setref in
      List.iter (fun t->List.iter (do_pair t) a2.negative) a1.positive;
      List.iter (fun t->List.iter (do_pair t) a2.positive) a1.negative in
    HP.iter (fun lf->do_atoms atoms lf.atoms) seq.redexes;
    do_atoms atoms (make_left_atoms seq);
    do_atoms atoms (make_goal_atoms seq);
    !flag && !phref 
 
let give_right_instances i dom triv atoms seq=
  let setref=ref RIS.empty in
  let inj inst=inst in
  if do_sequent setref triv RIS.add inj seq i dom atoms then
    None
  else
    Some (RIS.elements !setref)

let match_one_forall_hyp setref seq lf=
  match lf.pat with 
      Lforall(i,dom,triv)->
	let inj x=(x,lf.id) in
	  if do_sequent setref triv LIS.add inj seq i dom lf.atoms then
	    setref:=LIS.add ((Phantom dom),lf.id) !setref 
    | _ ->anomaly "can't happen" 

let give_left_instances lfh seq=
  let setref=ref LIS.empty in
    List.iter (match_one_forall_hyp setref seq) lfh;
    LIS.elements !setref
	  	  
(*tactics*)


let rec collect_forall seq=
  if is_empty_left seq then ([],seq) 
  else
    let hd,seq1=take_left seq in
      (match hd.pat with 
	   Lforall(_,_,_)-> 
	     let (q,seq2)=collect_forall seq1 in
	       ((hd::q),seq2)
	 | _->[],seq)

let left_instance_tac (inst,id) tacrec seq=
  match inst with
      Phantom dom->
	if lookup (id,None) seq then 
	  tclFAIL 0 "already done"
	else
	  tclTHENS (cut dom) 
	    [tclTHENLIST
	       [intro;
		(fun gls->generalize 
		   [mkApp(constr_of_reference id,
			  [|mkVar (Tacmach.pf_nth_hyp_id gls 1)|])] gls);
		intro;
		tclSOLVE [wrap 1 false tacrec 
			    (deepen (record (id,None) seq))]];
	    tclTRY assumption]
    | Real((m,t) as c,_)->
	if lookup (id,Some c) seq || m>0 then 
	  tclFAIL 0 "already done" 
	else
	  tclTHENLIST 
	    [generalize [mkApp(constr_of_reference id,[|t|])];
	     intro; 
	     tclSOLVE 
	       [wrap 1 false tacrec 
		  (deepen (record (id,Some c) seq))]]

let left_forall_tac lfp tacrec seq gl=
  let insts=give_left_instances lfp seq in
    tclFIRST (List.map (fun inst->left_instance_tac inst tacrec seq) insts) gl
	  
let dummy_exists_tac dom  tacrec seq=
	tclTHENS (cut dom) 
	[tclTHENLIST
	   [intro;
	    (fun gls->
	       split (Rawterm.ImplicitBindings 
			[mkVar (Tacmach.pf_nth_hyp_id gls 1)]) gls);
	    tclSOLVE [wrap 0 false tacrec (deepen seq)]];
	 tclTRY assumption] 
 
let right_instance_tac inst tacrec seq=
  match inst with
      Phantom _ ->anomaly "can't happen" 
    | Real ((m,t),_) ->
	if m>0 then tclFAIL 0 "not implemented ... yes"
	else
	tclTHEN (split (Rawterm.ImplicitBindings [t]))
	(tclSOLVE [wrap 0 true tacrec (deepen seq)])

let exists_tac insts tacrec seq gl=
    tclFIRST 
      (List.map (fun inst -> right_instance_tac inst tacrec seq) insts) gl

