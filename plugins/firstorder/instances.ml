(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Formula
open Sequent
open Unify
open Rules
open Util
open Term
open Rawterm
open Tacmach
open Tactics
open Tacticals
open Termops
open Reductionops
open Declarations
open Formula
open Sequent
open Names
open Libnames

let compare_instance inst1 inst2=
	match inst1,inst2 with
	    Phantom(d1),Phantom(d2)->
	      (OrderedConstr.compare d1 d2)
	  | Real((m1,c1),n1),Real((m2,c2),n2)->
	      ((-) =? (-) ==? OrderedConstr.compare) m2 m1 n1 n2 c1 c2
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

(* open instances processor *)

let dummy_constr=mkMeta (-1)

let dummy_bvid=id_of_string "x"

let mk_open_instance id gl m t=
  let env=pf_env gl in
  let evmap=Refiner.project gl in
  let var_id=
    if id==dummy_id then dummy_bvid else
      let typ=pf_type_of gl (constr_of_global id) in
	(* since we know we will get a product,
	   reduction is not too expensive *)
      let (nam,_,_)=destProd (whd_betadeltaiota env evmap typ) in
	match nam with
	    Name id -> id
	  | Anonymous ->  dummy_bvid in
  let revt=substl (list_tabulate (fun i->mkRel (m-i)) m) t in
  let rec aux n avoid=
    if n=0 then [] else
      let nid=(fresh_id avoid var_id gl) in
	(Name nid,None,dummy_constr)::(aux (n-1) (nid::avoid)) in
  let nt=it_mkLambda_or_LetIn revt (aux m []) in
  let rawt=Detyping.detype false [] [] nt in
  let rec raux n t=
    if n=0 then t else
      match t with
	  GLambda(loc,name,k,_,t0)->
	    let t1=raux (n-1) t0 in
	      GLambda(loc,name,k,GHole (dummy_loc,Evd.BinderType name),t1)
	| _-> anomaly "can't happen" in
  let ntt=try
    Pretyping.Default.understand evmap env (raux m rawt)
  with _ ->
    error "Untypable instance, maybe higher-order non-prenex quantification" in
    decompose_lam_n_assum m ntt

(* tactics   *)

let left_instance_tac (inst,id) continue seq=
  match inst with
      Phantom dom->
	if lookup (id,None) seq then
	  tclFAIL 0 (Pp.str "already done")
	else
	  tclTHENS (cut dom)
	    [tclTHENLIST
	       [introf;
		(fun gls->generalize
		   [mkApp(constr_of_global id,
			  [|mkVar (Tacmach.pf_nth_hyp_id gls 1)|])] gls);
		introf;
		tclSOLVE [wrap 1 false continue
			    (deepen (record (id,None) seq))]];
	    tclTRY assumption]
    | Real((m,t) as c,_)->
	if lookup (id,Some c) seq then
	  tclFAIL 0 (Pp.str "already done")
	else
	  let special_generalize=
	    if m>0 then
	      fun gl->
		let (rc,ot)= mk_open_instance id gl m t in
		let gt=
		  it_mkLambda_or_LetIn
		    (mkApp(constr_of_global id,[|ot|])) rc in
		  generalize [gt] gl
	    else
	      generalize [mkApp(constr_of_global id,[|t|])]
	  in
	    tclTHENLIST
	      [special_generalize;
	       introf;
	       tclSOLVE
		 [wrap 1 false continue (deepen (record (id,Some c) seq))]]

let right_instance_tac inst continue seq=
  match inst with
      Phantom dom ->
	tclTHENS (cut dom)
	[tclTHENLIST
	   [introf;
	    (fun gls->
	       split (Rawterm.ImplicitBindings
			[mkVar (Tacmach.pf_nth_hyp_id gls 1)]) gls);
	    tclSOLVE [wrap 0 true continue (deepen seq)]];
	 tclTRY assumption]
    | Real ((0,t),_) ->
	(tclTHEN (split (Rawterm.ImplicitBindings [t]))
	   (tclSOLVE [wrap 0 true continue (deepen seq)]))
    | Real ((m,t),_) ->
	tclFAIL 0 (Pp.str "not implemented ... yet")

let instance_tac inst=
  if (snd inst)==dummy_id then
    right_instance_tac (fst inst)
  else
    left_instance_tac inst

let quantified_tac lf backtrack continue seq gl=
  let insts=give_instances lf seq in
    tclORELSE
      (tclFIRST (List.map (fun inst->instance_tac inst continue seq) insts))
      backtrack gl


