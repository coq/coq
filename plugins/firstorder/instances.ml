(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Unify
open Rules
open CErrors
open Util
open Term
open Vars
open Tacmach
open Tactics
open Tacticals
open Termops
open Reductionops
open Formula
open Sequent
open Names
open Misctypes
open Sigma.Notations
open Context.Rel.Declaration

let compare_instance inst1 inst2=
	match inst1,inst2 with
	    Phantom(d1),Phantom(d2)->
	      (OrderedConstr.compare d1 d2)
	  | Real((m1,c1),n1),Real((m2,c2),n2)->
	      ((-) =? (-) ==? OrderedConstr.compare) m2 m1 n1 n2 c1 c2
	  | Phantom(_),Real((m,_),_)-> if Int.equal m 0 then -1 else 1
	  | Real((m,_),_),Phantom(_)-> if Int.equal m 0 then 1 else -1

let compare_gr id1 id2 =
  if id1==id2 then 0 else
    if id1==dummy_id then 1
    else if id2==dummy_id then -1
    else Globnames.RefOrdered.compare id1 id2

module OrderedInstance=
struct
  type t=instance * Globnames.global_reference
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
    | _ -> anomaly (Pp.str "can't happen")

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

let dummy_bvid=Id.of_string "x"

let mk_open_instance id idc gl m t=
  let env=pf_env gl in
  let evmap=Refiner.project gl in
  let var_id=
    if id==dummy_id then dummy_bvid else
      let typ=pf_unsafe_type_of gl (EConstr.of_constr idc) in
	(* since we know we will get a product,
	   reduction is not too expensive *)
      let (nam,_,_)=destProd (EConstr.Unsafe.to_constr (whd_all env evmap (EConstr.of_constr typ))) in
	match nam with
	    Name id -> id
	  | Anonymous ->  dummy_bvid in
  let revt=substl (List.init m (fun i->mkRel (m-i))) t in
  let rec aux n avoid env evmap decls =
    if Int.equal n 0 then evmap, decls else
      let nid=(fresh_id avoid var_id gl) in
      let evmap = Sigma.Unsafe.of_evar_map evmap in
      let Sigma ((c, _), evmap, _) = Evarutil.new_type_evar env evmap Evd.univ_flexible in
      let c = EConstr.Unsafe.to_constr c in
      let evmap = Sigma.to_evar_map evmap in
      let decl = LocalAssum (Name nid, c) in
	aux (n-1) (nid::avoid) (Environ.push_rel decl env) evmap (decl::decls) in
  let evmap, decls = aux m [] env evmap [] in
    evmap, decls, revt

(* tactics   *)

let left_instance_tac (inst,id) continue seq=
  match inst with
      Phantom dom->
	if lookup (id,None) seq then
	  tclFAIL 0 (Pp.str "already done")
	else
	  tclTHENS (Proofview.V82.of_tactic (cut (EConstr.of_constr dom)))
	    [tclTHENLIST
	       [Proofview.V82.of_tactic introf;
                pf_constr_of_global id (fun idc ->
		(fun gls-> Proofview.V82.of_tactic (generalize
		   [EConstr.of_constr (mkApp(idc,
			  [|mkVar (Tacmach.pf_nth_hyp_id gls 1)|]))]) gls));
		Proofview.V82.of_tactic introf;
		tclSOLVE [wrap 1 false continue
			    (deepen (record (id,None) seq))]];
	    tclTRY (Proofview.V82.of_tactic assumption)]
    | Real((m,t) as c,_)->
	if lookup (id,Some c) seq then
	  tclFAIL 0 (Pp.str "already done")
	else
	  let special_generalize=
	    if m>0 then
	      pf_constr_of_global id (fun idc ->
		fun gl->
		  let evmap,rc,ot = mk_open_instance id idc gl m t in
		  let gt=
		    it_mkLambda_or_LetIn
		      (mkApp(idc,[|ot|])) rc in
                  let gt = EConstr.of_constr gt in
		  let evmap, _ =
		    try Typing.type_of (pf_env gl) evmap gt
		    with e when CErrors.noncritical e ->
		      error "Untypable instance, maybe higher-order non-prenex quantification" in
		    tclTHEN (Refiner.tclEVARS evmap) (Proofview.V82.of_tactic (generalize [gt])) gl)
	    else
	      pf_constr_of_global id (fun idc ->
		Proofview.V82.of_tactic (generalize [EConstr.of_constr (mkApp(idc,[|t|]))]))
	  in
	    tclTHENLIST
	      [special_generalize;
	       Proofview.V82.of_tactic introf;
	       tclSOLVE
		 [wrap 1 false continue (deepen (record (id,Some c) seq))]]

let right_instance_tac inst continue seq=
  match inst with
      Phantom dom ->
	tclTHENS (Proofview.V82.of_tactic (cut (EConstr.of_constr dom)))
	[tclTHENLIST
	   [Proofview.V82.of_tactic introf;
	    (fun gls->
	       Proofview.V82.of_tactic (split (ImplicitBindings
			[EConstr.mkVar (Tacmach.pf_nth_hyp_id gls 1)])) gls);
	    tclSOLVE [wrap 0 true continue (deepen seq)]];
	 tclTRY (Proofview.V82.of_tactic assumption)]
    | Real ((0,t),_) ->
	(tclTHEN (Proofview.V82.of_tactic (split (ImplicitBindings [EConstr.of_constr t])))
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


