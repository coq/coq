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
	      ((-) =? (-) ==? OrderedConstr.compare) m1 m2 n1 n2 c1 c2
	  | Phantom(_),Real((m,_),_)-> if m=0 then -1 else 1
	  | Real((m,_),_),Phantom(_)-> if m=0 then 1 else -1

let compare_gr id1 id2=
  if id1==id2 then 0 else
    if id1==dummy_id then 1 
    else if id2==dummy_id then -1 
    else Pervasives.compare id1 id2

module OrderedInstance=
struct
  type t=instance * Libnames.global_reference
  let compare (inst1,id1) (inst2,id2)=
    (compare_instance =? compare_gr) inst2 inst1 id2 id1
    (* we want a __decreasing__ total order *)
end
  
module IS=Set.Make(OrderedInstance)

let make_simple_atoms seq=
  let ratoms=
    match seq.glatom with
	Some t->[t]
      | None->[]
  in {negative=seq.latoms;positive=ratoms}

let do_sequent setref triv id seq i dom atoms=
  let flag=ref true in
  let phref=ref triv in
  let do_atoms a1 a2 =
    let do_pair t1 t2 = 
      match unif_atoms i dom t1 t2 with
	  None->()
	| Some (Phantom _) ->phref:=true
	| Some c ->flag:=false;setref:=IS.add (c,id) !setref in
      List.iter (fun t->List.iter (do_pair t) a2.negative) a1.positive;
      List.iter (fun t->List.iter (do_pair t) a2.positive) a1.negative in
    HP.iter (fun lf->do_atoms atoms lf.atoms) seq.redexes;
    do_atoms atoms (make_simple_atoms seq);
    !flag && !phref 
 
let match_one_quantified_hyp setref seq lf=
  match lf.pat with 
      Left(Lforall(i,dom,triv))|Right(Rexists(i,dom,triv))->
	if do_sequent setref triv lf.id seq i dom lf.atoms then
	  setref:=IS.add ((Phantom dom),lf.id) !setref 
    | _ ->anomaly "can't happen" 

let give_instances lf seq=
  let setref=ref IS.empty in
    List.iter (match_one_quantified_hyp setref seq) lf;
    IS.elements !setref
	  	  
(* collector for the engine *)

let rec collect_quantified seq=
  try
    let hd,seq1=take_formula seq in
      (match hd.pat with 
	   Left(Lforall(_,_,_)) | Right(Rexists(_,_,_)) -> 
	     let (q,seq2)=collect_quantified seq1 in
	       ((hd::q),seq2)
	 | _->[],seq)
  with Heap.EmptyHeap -> [],seq

(* tactics   *)

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

let right_instance_tac inst tacrec seq=
  match inst with
      Phantom dom ->
	tclTHENS (cut dom) 
	[tclTHENLIST
	   [intro;
	    (fun gls->
	       split (Rawterm.ImplicitBindings 
			[mkVar (Tacmach.pf_nth_hyp_id gls 1)]) gls);
	    tclSOLVE [wrap 0 false tacrec (deepen seq)]];
	 tclTRY assumption] 
    | Real ((m,t),_) ->
	if m>0 then tclFAIL 0 "not implemented ... yes"
	else
	  tclTHEN (split (Rawterm.ImplicitBindings [t]))
	    (tclSOLVE [wrap 0 true tacrec (deepen seq)])

let instance_tac inst=
  if (snd inst)==dummy_id then 
    right_instance_tac (fst inst)
  else
    left_instance_tac inst

let quantified_tac lf tacrec seq gl=
  let insts=give_instances lf seq in
    tclFIRST (List.map (fun inst->instance_tac inst tacrec seq) insts) gl
