(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(*i $Id$ i*)

open Ast
open Coqast
open Hipattern
open Names
open Libnames
open Pp
open Proof_type
open Tacticals
open Tacinterp
open Tactics
open Tacexpr
open Util
open Term
open Termops
open Declarations

let myprint env rc t=
	let env2=Environ.push_rel_context rc env in
	let ppstr=Printer.prterm_env env2 t in
	Pp.msgnl ppstr

let tclTRY_REV_HYPS (tac : constr->tactic) gl = 
  tclTRY_sign tac (List.rev (Tacmach.pf_hyps gl)) gl
 
let rec nb_prod_after n c=
  match kind_of_term c with
    | Prod (_,_,b) ->if n>0 then nb_prod_after (n-1) b else 
	1+(nb_prod_after 0 b)
    | _            -> 0

let nhyps ind = 
  let (mib,mip) = Global.lookup_inductive ind in
  let constr_types = mip.mind_nf_lc in 
  let nhyps = nb_prod_after mip.mind_nparams in	
    Array.map nhyps constr_types

let isrec ind=
  let (mib,mip) = Global.lookup_inductive ind in
  Inductiveops.mis_is_recursive (ind,mib,mip)

let unfold_not_iff = function
  | None -> interp <:tactic<Try Progress Unfold not iff>>
  | Some id -> let id = (dummy_loc,id) in
	interp <:tactic<Try Progress Unfold not iff in $id>>

let simplif =
  onAllClauses (fun ido -> unfold_not_iff ido)
  
let rule_axiom=assumption
		      
let rule_rforall tac=tclTHEN intro tac

let rule_rarrow=interp  <:tactic<Match Reverse Context With
      | [|- ?1 -> ?2 ] -> Intro>>

let rule_larrow= 
  (interp <:tactic<(Match Reverse Context With 
			    [f:?1->?2;x:?1|-?] ->
			      Generalize (f x);Clear f;Intro)>>)

let rule_named_llarrow id gl=
    (try let nam=destVar id in
    let body=Tacmach.pf_get_hyp_typ gl nam in
    let (_,cc,c)=destProd body in
    if dependent (mkRel 1) c then tclFAIL 0 else
    let (_,ta,b)=destProd cc in
    if dependent (mkRel 1) b then tclFAIL 0 else 
    let tb=pop b and tc=pop c in
    let d=mkLambda (Anonymous,tb,
    mkApp (id,[|mkLambda (Anonymous,(lift 1 ta),(mkRel 2))|])) in
    let env=Tacmach.pf_env gl in
      tclTHENS (cut tc)
	[tclTHEN intro (clear [nam]);
	 tclTHENS (cut cc) 
	   [refine id; tclTHENLIST [generalize [d];intro;clear [nam]]]]
   with Invalid_argument _ -> tclFAIL 0) gl

let rule_llarrow tac=tclTRY_REV_HYPS (fun id->tclTHEN (rule_named_llarrow id) tac)

let rule_rind tac gl=
  (let (hdapp,args)=decompose_app gl.it.Evd.evar_concl in
     try let ind=destInd hdapp in
       if isrec ind then tclFAIL 0 else
	 any_constructor (Some tac)
     with Invalid_argument _ -> tclFAIL 0) gl 
  
let rule_rind_rev gl=  
  (let (hdapp,args)=decompose_app gl.it.Evd.evar_concl in
     try let ind=destInd hdapp in
       if isrec ind then tclFAIL 0 else
	 simplest_split
     with Invalid_argument _ -> tclFAIL 0) gl 

let rule_named_false id gl=
  (try let nam=destVar id in
   let body=Tacmach.pf_get_hyp_typ gl nam in
     if is_empty_type body then (simplest_elim id)
     else tclFAIL 0
   with Invalid_argument _ -> tclFAIL 0) gl

let rule_false=tclTRY_REV_HYPS rule_named_false

let rule_named_lind id gl= 
  (try let nam=destVar id in
   let body=Tacmach.pf_get_hyp_typ gl nam in
   let (hdapp,args) = decompose_app body in
   let ind=destInd hdapp in
     if isrec ind then tclFAIL 0 else 
       let l=nhyps ind in
       let f n= tclDO n intro in
	 tclTHENSV (tclTHEN (simplest_elim id) (clear [nam])) (Array.map f l)
   with Invalid_argument _ -> tclFAIL 0) gl
  
let rule_lind=tclTRY_REV_HYPS rule_named_lind

 
let rule_named_llind id gl= 
    (try let nam=destVar id in 
    let body=Tacmach.pf_get_hyp_typ gl nam in
    let (_,xind,b) =destProd body in
    if dependent (mkRel 1) b then tclFAIL 0 else  
    let (hdapp,args) = decompose_app xind in
    let vargs=Array.of_list args in
    let ind=destInd hdapp in
    if isrec ind then tclFAIL 0 else
    let (mib,mip) = Global.lookup_inductive ind in
    let n=mip.mind_nparams in
    if n<>(List.length args) then tclFAIL 0 else
    let p=nhyps ind in
    let types= mip.mind_nf_lc in
    let names= mip.mind_consnames in

	(* construire le terme  H->B, le generaliser etc *)   
    let myterm i=
	let env=Tacmach.pf_env gl and emap=Tacmach.project gl in
	let t1=Reductionops.hnf_prod_appvect env emap types.(i) vargs in
	let (rc,_)=Sign.decompose_prod_n_assum p.(i) t1 in
	let cstr=mkApp ((mkConstruct (ind,(i+1))),vargs) in
	let vars=Array.init p.(i) (fun j->mkRel (p.(i)-j)) in
	let capply=mkApp ((lift p.(i) cstr),vars) in
	let head=mkApp ((lift p.(i) id),[|capply|]) in
	Sign.it_mkLambda_or_LetIn head rc in
	
    let newhyps=List.map myterm (interval 0 ((Array.length p)-1)) in
     tclTHEN (generalize newhyps)
	(tclTHEN (clear [nam]) (tclDO (Array.length p) intro))
	with Invalid_argument _ ->tclFAIL 0) gl

let rule_llind=tclTRY_REV_HYPS rule_named_llind



let default_stac = interp(<:tactic< Auto with * >>)

let rec newtauto stac gl=
    (tclTHEN simplif 
       (tclORELSE 
	  (tclTHEN 
	     (tclFIRST [
		rule_axiom;
		rule_false;
		rule_rarrow;
		rule_lind; 
		rule_larrow;
		rule_llind;
		rule_rind_rev;
		rule_llarrow (tclSOLVE [newtauto stac]);
		rule_rind (tclSOLVE [newtauto stac]);
		rule_rforall (tclSOLVE [newtauto stac])])
		(tclPROGRESS (newtauto stac)))
		stac)) gl

			   
let q_elim tac=
  let vtac=Tacexpr.TacArg (valueIn (VTactic tac)) in	
  interp <:tactic<
  Match Context With 
   [x:?1|-(? ?1 ?)]->
      Exists x;$vtac  
  |[x:?1;H:?1->?|-?]->
      Generalize (H x);Clear H;$vtac>>

let rec lfo n=
  if n=0 then (tclFAIL 0) else
    let p=if n<0 then n else (n-1) in
    let lfo_rec=q_elim (fun gl->lfo p gl) in
      newtauto lfo_rec

let lfo_wrap n gl= 
  try lfo n gl
  with
    Refiner.FailError _ | UserError _ ->
      errorlabstrm "NewLinearIntuition" [< str "NewLinearIntuition failed." >]

TACTIC EXTEND NewIntuition
      [ "NewIntuition" ] -> [ newtauto default_stac ]
      |[ "NewIntuition" tactic(t)] -> [ newtauto (interp t) ]
END

TACTIC EXTEND NewTauto
  [ "NewTauto" ] -> [ newtauto (tclFAIL 0) ]
END

TACTIC EXTEND NewLinearIntuition
  [ "NewLinearIntuition" ] -> [ lfo_wrap (-1) ]
|  [ "NewLinearIntuition" integer(n)] -> [ lfo_wrap n ]
END

