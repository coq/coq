(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(*i $Id$ i*)

open Dpctypes

open Names
open Nameops
open Pp
open Term
open Termops
open Environ
open Himsg
open Tacmach
open Reductionops
open Clenv
open Tactics
open Hipattern
open Tacticals
open Tactics
open Util
open Sign
open Tacinterp

(*
let mmk = make_module_marker ["#Prelude.obj"]

let and_pattern   = put_pat mmk "(and ? ?)"
let or_pattern    = put_pat mmk "(or ? ?)"
let not_pattern   = put_pat mmk "(not ?)"
let exist_pattern = put_pat mmk "(ex ? ?)"

let and_head      = put_pat mmk "and"
let or_head       = put_pat mmk "or"
let not_head      = put_pat mmk "not"
let exist_head    = put_pat mmk "ex"

*)

let op2bool=function Some _->true |None->false

let match_with_imp_term t =
  match kind_of_term t with
      Prod (_,a,b)->
	if not (dependent (mkRel 1) b) then
	  Some (a,b) else None
    | _-> None

let is_imp_term t=op2bool (match_with_imp_term t)

let match_with_forall_term t =
  match kind_of_term (whd_betaiota t) with
      Prod (x,a,b)->
	if dependent (mkRel 1) b then Some (x,a,b) else None
    | _ -> None

let is_forall_term t=op2bool (match_with_forall_term t)

let constr_of_string s () =
  Libnames.constr_of_reference (Nametab.locate (Libnames.qualid_of_string s))

let id_ex=constr_of_string "Logic.ex" 

let match_with_exist_term t=
  match kind_of_term t with
      App(t,v)->
	if t=id_ex () && (Array.length v)=2 then
	  match kind_of_term v.(1) with
	      Lambda(na,a,b)->Some(na,a,b)
	    |_->raise Impossible_case
	else None
    | _->None

let is_exist_term t=op2bool (match_with_exist_term t)

let id_not=constr_of_string "Logic.not"

let id_false=constr_of_string "Logic.False"

let match_with_not_term t=
  match kind_of_term t with
      App(t,v)->
	if t=id_not () && (Array.length v)=1 then
	  Some v.(0) 
	else None
    | Prod(_,a,b)->
	if b=id_false () then
	  Some a
	else None
    | _->None


let is_not_term t=op2bool (match_with_not_term t)

let ctr = ref 0

let gen_ident id = make_ident (atompart_of_id id) (incr ctr;Some !ctr)

let gen_name a na =
    match (named_hd Environ.empty_env a na) with 
	(Name id)->gen_ident id
      | Anonymous->raise Impossible_case

let dpc_of_cci_term lid = 
 let rec tradrec cciterm =
    let (hd,args) = whd_betaiota_stack cciterm in
    let dpcargs = List.map tradrec args
    in (match kind_of_term hd with
            Var id -> if dpcargs=[] then VAR id 
                  else if List.mem id lid 
                  then failwith "dpc_of_cci_term (not first order)"
                  else APP (VAR id :: dpcargs)

      | (Const _ | Ind _ | Construct _) as t 
      	   -> if dpcargs=[] then GLOB (CN hd)
	                    else APP (GLOB (CN hd) :: dpcargs)

      | _ -> errorlabstrm "dpc_of_cci_term"
                (str "Not a first order formula"))
 in tradrec
    

let cci_of_dpc_term tradsign sign = 
  let rec tradrec = function
      VAR id -> 
	(try let (_,t,_)=lookup_named id tradsign in
	   match t with
	       Some t'-> t'
	     |None ->Term.mkVar id
	   with Not_found->Term.mkVar id)
    | GLOB (ID id) -> Term.mkVar id
    | GLOB (CN t)  -> t
    | APP (t::dpcargs) ->
	let t' = tradrec t in
	  Term.applist(t', List.map tradrec dpcargs)
    | _-> raise Impossible_case
  in tradrec
    

let dpc_of_cci_fmla gls cciterm = 
  let rec tradrec lid cciterm =
    match match_with_exist_term cciterm with
	 Some ((na,a,b)as trp)->
	   let id = gen_name a na in
	   let f=whd_beta (mkApp ((mkLambda trp),[|mkVar id|])) in
	     Exists(id,tradrec (id::lid) f)
       |_-> 
    (match match_with_conjunction cciterm with
	Some (_,[a;b])->Conj(tradrec lid a,tradrec lid b)
      |_->
	  (match match_with_disjunction cciterm with
	       Some (_,[a;b])->Disj(tradrec lid a,tradrec lid b)
	     |_->
		 (match match_with_not_term cciterm with
		   	       Some a->Neg(tradrec lid a)
		    |_->
		       (match match_with_imp_term cciterm with
			    Some (a,b)->Imp (tradrec lid a,tradrec lid (pop b))
			  |_->
    (match match_with_forall_term cciterm with
	 Some ((na,a,b) as trp)->
	   let id = gen_name a na in
	   let f=whd_beta (mkApp ((mkLambda trp),[|mkVar id|])) in
	     ForAll(id,tradrec (id::lid) f)
       |_-> 
    let (hd,args) = whd_betaiota_stack cciterm in
    let dpcargs = List.map (dpc_of_cci_term lid) args
    in (match kind_of_term hd with
	    Var id -> if List.mem id lid 
	    then errorlabstrm "dpc_of_cci_fmla"
	      (str "Quantification over a predicate")
	    else Atom((ID id,0),dpcargs)
	  | Ind _ | Construct _ | Const _ 
    	      -> Atom( (CN hd,0) , dpcargs)
	  | _ -> errorlabstrm "dpc_of_cci_flma"
		((Printer.prterm_env 
		    (Global.env_of_context (pf_hyps gls)) hd) ++ 
		 (spc ()) ++
		 (str "is not an atomic predicate"))))))))
	  in tradrec [] (whd_betaiota cciterm)  
	       
let rec index x=function
    []-> raise Not_found
  | y::q-> if x=y then 0 else 1+(index x q)
      

let rec alpha_term bl1 bl2 p_0 p_1 =
  match p_0,p_1 with
      ((VAR id1), (VAR id2)) ->
      	if not (List.mem id1 bl1) then
	  id1=id2
      	else
	  index id1 bl1 = index id2 bl2
    | ((GLOB t1), (GLOB t2)) -> t1=t2
    | ((APP al1), (APP al2)) ->
      	List.for_all2 (alpha_term bl1 bl2) al1 al2
    | (_, _) -> false


let forAllI id gls=if is_forall_term (pf_concl gls) then
  intro_using id gls else tclFAIL 0 "goal is not universally quantified" gls

let forAllE id t gls =
  let rgl=pf_whd_betadeltaiota gls (pf_type_of gls (mkVar id)) in
    if is_forall_term rgl then
      tclTHEN (generalize [mkApp (mkVar id,[|t|])]) intro gls
    else  tclFAIL 0 "hypothesis is not universally quantified" gls

let existE id id2 gls =
  let (_,_,t)=lookup_named id (pf_hyps gls) in
    if is_exist_term t then
        ((tclTHEN (simplest_elim (mkVar id))
         (tclTHEN (intro_using id2) (dImp None)))) gls
    else tclFAIL 0 "hypothesis is not existentially quantified" gls

let negE id gls = 
  let (_,_,t)=lookup_named id (pf_hyps gls) in
    if is_not_term t then
        (simplest_elim (mkVar id)) gls
    else tclFAIL 0 "hypothesis is not negated" gls

(*t exist_intro_head = put_pat mmk "ex_intro"*)

let existI t gls =
  if is_exist_term (pf_concl gls) then
    split (Rawterm.ImplicitBindings [t]) gls
  else tclFAIL 0 "goal is not existentially quantified" gls 
    (*
 
    let (wc,kONT) = Evar_refiner.startWalk gls in
    let clause = mk_clenv_hnf_constr_type_of wc (pf_concl gls) in
    let clause' = clenv_constrain_missing_args [t] clause
    in res_pf kONT clause' gls
    *)

let rec alpha_fmla bl1 bl2 p_0 p_1 =
  match p_0,p_1 with
      ((Atom((cn1,_),al1)), (Atom((cn2,_),al2))) ->
    	cn1=cn2 & List.for_all2 (alpha_term bl1 bl2) al1 al2
    | ((Conj(a1,b1)),(Conj(a2,b2))) ->
    	alpha_fmla bl1 bl2 a1 a2 & alpha_fmla bl1 bl2 b1 b2

    | ((Disj(a1,b1)),(Disj(a2,b2))) ->
    	alpha_fmla bl1 bl2 a1 a2 & alpha_fmla bl1 bl2 b1 b2

    | ((Imp(a1,b1)),(Imp(a2,b2))) ->
    	alpha_fmla bl1 bl2 a1 a2 & alpha_fmla bl1 bl2 b1 b2

    | ((Neg(a1)), (Neg(a2))) -> alpha_fmla bl1 bl2 a1 a2

    | ((ForAll(x1,a1)), (ForAll(x2,a2))) ->
    	alpha_fmla (x1::bl1) (x2::bl2) a1 a2

    | ((Exists(x1,a1)), (Exists(x2,a2))) ->
    	alpha_fmla (x1::bl1) (x2::bl2) a1 a2

    | (_, _) -> false

let alpha_eq (kspine,m) (jspine,n) = alpha_fmla kspine jspine m n

let first_pred p = 
 let rec firstrec = function
    [] -> error "first_pred"
  | h::t -> if p h then h else firstrec t
 in firstrec


let find_fmla_left (kspine,f) (jspine,gl) = 
    let sign= pf_hyps gl in
    let (id,_,_)=first_pred 
        (fun (id,_,t) -> 
	   ( try
	      alpha_eq (kspine,f)
                       (jspine,dpc_of_cci_fmla gl t)
		     with _ -> false) 
        ) sign in id


let onNthClause tac n gls =
    let cls = nth_clause n gls
    in onClause tac cls gls


let elimTypeFalse gls =
  (elim_type (pf_global gls (id_of_string "False"))) gls


let rec tradpf kspine jspine dpcpf gls =
    match dpcpf with

    Proof2(_,_,Axiom2 f) ->
    let id = find_fmla_left (kspine,f) (jspine,gls)
    in (*exact_check (mkVar id)*)assumption gls

  | Proof2(_,_,LWeakening2(_,pf)) -> trad kspine jspine pf gls

  | Proof2(_,_,RWeakening2(_,pf)) ->
     ( (tclTHEN (elimTypeFalse) (tradpf kspine jspine pf)) ) gls

  | Proof2(_,_,RConj2(f1,pf1,f2,pf2)) ->
    ((tclTHENS (dAnd None) ([trad kspine jspine pf1;
                      trad kspine jspine pf2]))) gls

  | Proof2(_,_,LConj2(f1,f2,pf)) ->
    let id = find_fmla_left (kspine,Conj(f1,f2)) (jspine,gls)
    in ((tclTHEN (dAnd (Some id)) ((trad kspine jspine pf)))) gls

  | Proof2(_,_,LDisj2(f1,pf1,f2,pf2)) ->
    let id = find_fmla_left (kspine,Disj(f1,f2)) (jspine,gls)
    in (match pf1 with 
          Proof2(_,[],_) -> ((tclTHENS (orE id) 
                            ([ ((tclTHEN (elimTypeFalse) (trad kspine jspine pf1)));
                              trad kspine jspine pf2]))) gls
        | _              -> ((tclTHENS (orE id) 
                            ([ trad kspine jspine pf1;
                              ((tclTHEN (elimTypeFalse) (trad kspine jspine pf2)))]))) gls
       )

  | Proof2(_,_,RImp2(f1,f2,pf)) ->
    ((tclTHEN (dImp None) ((trad kspine jspine pf)))) gls

  | Proof2(_,_,LImp2(f1,pf1,f2,pf2)) ->
    let id = find_fmla_left (kspine,Imp(f1,f2)) (jspine,gls)
    in ((tclTHENS (dImp (Some id))
	   ([trad kspine jspine pf2;
             trad kspine jspine pf1]))) gls

  | Proof2(_,_,RForAll2(kid,f,pf)) ->
    ((tclTHEN (forAllI kid)
     ((onLastHyp (fun jid ->
                     trad (kid::kspine) (jid::jspine) pf))))) gls

  | Proof2(_,_,LForAll2(kid,kterm,f,pf)) ->
    let jterm = cci_of_dpc_term (pf_hyps gls) (kspine,jspine) kterm in
    let id = find_fmla_left (kspine,ForAll(kid,f)) (jspine,gls)
    in ((tclTHEN (forAllE id jterm)
        (trad kspine jspine pf))) gls

  | Proof2(_,_,LExists2(kid,f,pf)) ->
    let id = find_fmla_left (kspine,Exists(kid,f)) (jspine,gls)
    in ((tclTHEN (existE id kid)
        ((onNthClause (function (Some jid) ->
                          trad (kid::kspine) (jid::jspine) pf
			 | None-> raise Impossible_case)
         (-2))))) gls

  | Proof2(_,_,RExists2(kid,kterm,f,pf)) ->
    let jterm = cci_of_dpc_term (pf_hyps gls) (kspine,jspine) kterm
    in ((tclTHEN (existI jterm) (tradpf kspine jspine pf))) gls

  | Proof2(_,_,RDisj2(f1,f2,Proof2(_,_,RWeakening2(f3,pf)))) ->
    if alpha_eq (kspine,f1) (kspine,f3) then
        ((tclTHEN (right Rawterm.NoBindings) (tradpf kspine jspine pf))) gls
    else if alpha_eq (kspine,f2) (kspine,f3) then
        ((tclTHEN (left Rawterm.NoBindings) (tradpf kspine jspine pf))) gls
    else error "Not Intuitionistic, eh?"

  | Proof2(_,_,RNeg2(f,pf)) -> 
      ((tclTHEN ((tclTHEN (red_in_concl) (Tactics.intro))) (tradpf kspine jspine pf))) gls

  | Proof2(_,_,LNeg2(f,pf)) -> 
     let id = find_fmla_left (kspine,Neg(f)) (jspine,gls)
     in ((tclTHEN (negE id) (tradpf kspine jspine pf))) gls

  | _ -> error "tradpf : Not an intuitionistic proof !"

and trad kspine jspine dpcpf gls =
    tradpf kspine jspine dpcpf gls



