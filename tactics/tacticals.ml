(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Term
open Termops
open Sign
open Declarations
open Inductive
open Reduction
open Environ
open Declare
open Tacmach
open Clenv
open Pattern
open Evar_refiner
open Wcclausenv

(******************************************)
(*         Basic Tacticals                *)
(******************************************)

let tclIDTAC         = Tacmach.tclIDTAC
let tclORELSE        = Tacmach.tclORELSE
let tclTHEN          = Tacmach.tclTHEN
let tclTHEN_i        = Tacmach.tclTHEN_i
let tclTHENL         = Tacmach.tclTHENL
let tclTHENS         = Tacmach.tclTHENS
let tclTHENSi        = Tacmach.tclTHENSi
let tclREPEAT        = Tacmach.tclREPEAT
let tclFIRST         = Tacmach.tclFIRST
let tclSOLVE         = Tacmach.tclSOLVE
let tclTRY           = Tacmach.tclTRY
let tclINFO          = Tacmach.tclINFO
let tclCOMPLETE      = Tacmach.tclCOMPLETE
let tclAT_LEAST_ONCE = Tacmach.tclAT_LEAST_ONCE
let tclFAIL          = Tacmach.tclFAIL
let tclDO            = Tacmach.tclDO
let tclPROGRESS      = Tacmach.tclPROGRESS
let tclWEAK_PROGRESS = Tacmach.tclWEAK_PROGRESS

(* [rclTHENSEQ [t1;..;tn] is equivalent to t1;..;tn *)
let tclTHENSEQ = List.fold_left tclTHEN tclIDTAC

(* map_tactical f [x1..xn] = (f x1);(f x2);...(f xn) *)
(* tclMAP f [x1..xn] = (f x1);(f x2);...(f xn) *)
let tclMAP tacfun l = 
  List.fold_right (fun x -> (tclTHEN (tacfun x))) l tclIDTAC

(*let dyn_tclIDTAC = function [] -> tclIDTAC |  _ -> anomaly "tclIDTAC"*)

(*let dyn_tclFAIL  = function [] -> tclFAIL |  _ -> anomaly "tclFAIL"*)

(* apply a tactic to the nth element of the signature  *)

let tclNTH_HYP m (tac : constr->tactic) gl =
  tac (try mkVar(let (id,_,_) = List.nth (pf_hyps gl) (m-1) in id) 
       with Failure _ -> error "No such assumption") gl

(* apply a tactic to the last element of the signature  *)

let tclLAST_HYP = tclNTH_HYP 1

let tclTRY_sign (tac : constr->tactic) sign gl =
  let rec arec = function
    | []      -> tclFAIL 0
    | [s]     -> tac (mkVar s) (*added in order to get useful error messages *)
    | (s::sl) -> tclORELSE (tac (mkVar s)) (arec sl) 
  in 
  arec (ids_of_named_context sign) gl

let tclTRY_HYPS (tac : constr->tactic) gl = 
  tclTRY_sign tac (pf_hyps gl) gl

(* OR-branch *)
let tryClauses tac = 
  let rec firstrec = function
    | []      -> tclFAIL 0
    | [cls]   -> tac cls (* added in order to get a useful error message *)
    | cls::tl -> (tclORELSE (tac cls) (firstrec tl))
  in 
  firstrec

(***************************************)
(*           Clause Tacticals          *)
(***************************************)

(* The following functions introduce several tactic combinators and
   functions useful for working with clauses. A clause is either None
   or (Some id), where id is an identifier. This type is useful for
   defining tactics that may be used either to transform the
   conclusion (None) or to transform a hypothesis id (Some id).  --
   --Eduardo (8/8/97) 
*)

(* The type of clauses *)

type clause = identifier option

(* A clause corresponding to the |n|-th hypothesis or None *)

let nth_clause n gl =
  if n = 0 then 
    None
  else if n < 0 then 
    let id = List.nth (pf_ids_of_hyps gl) (-n-1) in 
    Some id
  else 
    let id = List.nth (pf_ids_of_hyps gl) (n-1) in 
    Some id

(* Gets the conclusion or the type of a given hypothesis *)

let clause_type cls gl =
  match cls with
    | None    -> pf_concl gl
    | Some id -> pf_get_hyp_typ gl id

(* Functions concerning matching of clausal environments *)

let pf_is_matching gls pat n =
  let (wc,_) = startWalk gls in 
  is_matching_conv (w_env wc) (w_Underlying wc) pat n

let pf_matches gls pat n =
  matches_conv (pf_env gls) (project gls) pat n

(* [OnCL clausefinder clausetac]
 * executes the clausefinder to find the clauses, and then executes the
 * clausetac on the list so obtained. *)

let onCL cfind cltac gl = cltac (cfind gl) gl


(* [OnHyps hypsfinder hypstac]
 * idem [OnCL] but only for hypotheses, not for conclusion *)

let onHyps find tac gl = tac (find gl) gl


(* Create a clause list with all the hypotheses from the context *)

let allHyps gl = pf_ids_of_hyps gl


(* Create a clause list with all the hypotheses from the context, occuring
   after id *)

let afterHyp id gl =
  fst (list_splitby (fun (hyp,_,_) -> hyp = id) (pf_hyps gl))
    

(* Create a singleton clause list with the last hypothesis from then context *)

let lastHyp gl = List.hd (pf_ids_of_hyps gl)


(* Create a clause list with the n last hypothesis from then context *)

let nLastHyps n gl =
  try list_firstn n (pf_hyps gl)
  with Failure "firstn" -> error "Not enough hypotheses in the goal"


(* A clause list with the conclusion and all the hypotheses *)

let allClauses gl = 
  let ids = pf_ids_of_hyps gl in  
  (None::(List.map in_some ids))

let onClause t cls gl  = t cls gl
let tryAllClauses  tac = onCL allClauses (tryClauses tac)
let onAllClauses   tac = onCL allClauses (tclMAP tac)
let onAllClausesLR tac = onCL (compose List.rev allClauses) (tclMAP tac)
let onNthLastHyp n tac gls = tac (nth_clause n gls) gls

let tryAllHyps     tac gls = tryClauses tac (allHyps gls) gls
let onNLastHyps n  tac     = onHyps (nLastHyps n) (tclMAP tac)
let onLastHyp      tac gls = tac (lastHyp gls) gls

(* Serait-ce possible de compiler d'abord la tactique puis de faire la
   substitution sans passer par bdize dont l'objectif est de préparer un
   terme pour l'affichage ? (HH) *)

(* Si on enlève le dernier argument (gl) conclPattern est calculé une
fois pour toutes : en particulier si Pattern.somatch produit une UserError 
Ce qui fait que si la conclusion ne matche pas le pattern, Auto échoue, même
si après Intros la conclusion matche le pattern.
*)

(* conclPattern doit échouer avec error car il est rattraper par tclFIRST *)

let conclPattern concl pat tacast gl =
  let constr_bindings =
    try Pattern.matches pat concl
    with PatternMatchingFailure -> error "conclPattern" in
  let ast_bindings = 
    List.map 
      (fun (i,c) ->
	 (i, Termast.ast_of_constr false (pf_env gl) c))
      constr_bindings in 
  let tacast' = Coqast.subst_meta ast_bindings tacast in
  Tacinterp.interp tacast' gl

let clauseTacThen tac continuation =
  (fun cls -> (tclTHEN (tac cls) continuation))

let if_tac pred tac1 tac2 gl =
  if pred gl then tac1 gl else tac2 gl

let ifOnClause pred tac1 tac2 cls gl =
  if pred (cls,clause_type cls gl) then
    tac1 cls gl
  else 
    tac2 cls gl

let ifOnHyp pred tac1 tac2 id gl =
  if pred (id,pf_get_hyp_typ gl id) then
    tac1 id gl
  else 
    tac2 id gl

(***************************************)
(*         Elimination Tacticals       *)
(***************************************)

(* The following tacticals allow to apply a tactic to the
   branches generated by the application of an elimination
  tactic. 

  Two auxiliary types --branch_args and branch_assumptions-- are
  used to keep track of some information about the ``branches'' of 
  the elimination. *)

type branch_args = {
  ity        : inductive;   (* the type we were eliminating on *)
  largs      : constr list; (* its arguments *)
  branchnum  : int;         (* the branch number *)
  pred       : constr;      (* the predicate we used *)
  nassums    : int;         (* the number of assumptions to be introduced *)
  branchsign : bool list}   (* the signature of the branch.
                               true=recursive argument, false=constant *)

type branch_assumptions = {
  ba        : branch_args;     (* the branch args *)
  assums    : named_context; (* the list of assumptions introduced *)
  cargs     : identifier list; (* the constructor arguments *)
  constargs : identifier list; (* the CONSTANT constructor arguments *)
  recargs   : identifier list; (* the RECURSIVE constructor arguments *)
  indargs   : identifier list} (* the inductive arguments *)

let compute_construtor_signatures isrec (_,k as ity) =
  let rec analrec c recargs =
    match kind_of_term c, recargs with 
    | Prod (_,_,c), recarg::rest ->
	  (match dest_recarg recarg with
	    | Norec   -> false :: (analrec c rest)
	    | Imbr _  -> false :: (analrec c rest)
	    | Mrec j  -> (isrec & j=k) :: (analrec c rest))
    | LetIn (_,_,_,c), rest -> false :: (analrec c rest)
    | _, [] -> []
    | _ -> anomaly "compute_construtor_signatures"
  in 
  let (mib,mip) = Global.lookup_inductive ity in
  let n = mip.mind_nparams in
  let lc =
    Array.map (fun c -> snd (decompose_prod_n_assum n c)) mip.mind_nf_lc in
  let lrecargs = dest_subterms mip.mind_recargs in
  array_map2 analrec lc lrecargs

let case_sign = compute_construtor_signatures false
let elim_sign = compute_construtor_signatures true

let elimination_sort_of_goal gl = 
  match kind_of_term (hnf_type_of gl (pf_concl gl)) with 
    | Sort s ->
	(match s with
	   | Prop Null -> InProp
	   | Prop Pos -> InSet
	   | Type _ -> InType)
    | _        -> anomaly "goal should be a type"

let elimination_sort_of_hyp id gl = 
  match kind_of_term (hnf_type_of gl (pf_get_hyp_typ gl id)) with 
    | Sort s ->
	(match s with
	   | Prop Null -> InProp
	   | Prop Pos -> InSet
	   | Type _ -> InType)
    | _        -> anomaly "goal should be a type"


(* Find the right elimination suffix corresponding to the sort of the goal *)
(* c should be of type A1->.. An->B with B an inductive definition *)

let last_arg c = match kind_of_term c with
  | App (f,cl) -> array_last cl
  | _ -> anomaly "last_arg"

let general_elim_then_using 
  elim elim_sign_fun tac predicate (indbindings,elimbindings) c gl =
  let (ity,t) = pf_reduce_to_quantified_ind gl (pf_type_of gl c) in
  (* applying elimination_scheme just a little modified *)
  let (wc,kONT)  = startWalk gl in
  let indclause  = mk_clenv_from wc (c,t) in
  let indclause' = clenv_constrain_with_bindings indbindings indclause in
  let elimclause = mk_clenv_from () (elim,w_type_of wc elim) in
  let indmv = 
    match kind_of_term (last_arg (clenv_template elimclause).rebus) with
      | Meta mv -> mv
      | _         -> error "elimination"
  in
  let pmv =
    let p, _ = decompose_app (clenv_template_type elimclause).rebus in
    match kind_of_term p with
      | Meta p -> p
      | _ ->
	  let name_elim =
	    match kind_of_term elim with
	      | Const sp -> string_of_path sp
	      | Var id -> string_of_id id
	      | _ -> "\b"
	  in
	  error ("The elimination combinator " ^ name_elim ^ " is not known") 
  in
  let elimclause' = clenv_fchain indmv elimclause indclause' in
  let elimclause' = clenv_constrain_with_bindings elimbindings elimclause' in
  let branchsigns = elim_sign_fun ity in
  let after_tac ce i gl =
    let (hd,largs) = decompose_app (clenv_template_type ce).rebus in
    let ba = { branchsign = branchsigns.(i-1);
               nassums = 
		 List.fold_left 
                   (fun acc b -> if b then acc+2 else acc+1)
                   0 branchsigns.(i-1);
               branchnum = i;
               ity = ity;
               largs = List.map (clenv_instance_term ce) largs;
               pred = clenv_instance_term ce hd }
    in 
    tac ba gl
  in
  let elimclause' =
    match predicate with
       | None   -> elimclause'
       | Some p -> clenv_assign pmv p elimclause'
  in 
  elim_res_pf_THEN_i kONT elimclause' after_tac gl


let elimination_then_using tac predicate (indbindings,elimbindings) c gl = 
  let (ind,t) = pf_reduce_to_quantified_ind gl (pf_type_of gl c) in
  let elim =
    Indrec.lookup_eliminator ind (elimination_sort_of_goal gl) in
  general_elim_then_using
    elim elim_sign tac predicate (indbindings,elimbindings) c gl


let elimination_then tac        = elimination_then_using tac None 
let simple_elimination_then tac = elimination_then tac ([],[])

let case_then_using tac predicate (indbindings,elimbindings) c gl =
  (* finding the case combinator *)
  let (ity,t) = pf_reduce_to_quantified_ind gl (pf_type_of gl c) in
  let sigma = project gl in 
  let sort  = elimination_sort_of_goal gl  in
  let elim  = Indrec.make_case_dep (pf_env gl) sigma ity sort in  
  general_elim_then_using 
    elim case_sign tac predicate (indbindings,elimbindings) c gl

let case_nodep_then_using tac predicate (indbindings,elimbindings) c gl =
  (* finding the case combinator *)
  let (ity,t) = pf_reduce_to_quantified_ind gl (pf_type_of gl c) in
  let sigma = project gl in 
  let sort  = elimination_sort_of_goal gl  in
  let elim  = Indrec.make_case_nodep (pf_env gl) sigma ity sort in  
  general_elim_then_using 
    elim case_sign tac predicate (indbindings,elimbindings) c gl


let make_elim_branch_assumptions ba gl =   
  let rec makerec (assums,cargs,constargs,recargs,indargs) lb lc =
    match lb,lc with 
      | ([], _) -> 
          { ba = ba;
            assums    = assums;
            cargs     = cargs;
            constargs = constargs;
            recargs   = recargs;
            indargs   = indargs}
      | ((true::tl), ((idrec,_,_ as recarg)::(idind,_,_ as indarg)::idtl)) ->
	  makerec (recarg::indarg::assums,
		   idrec::cargs,
		   idrec::recargs,
		   constargs,
		   idind::indargs) tl idtl
      | ((false::tl), ((id,_,_ as constarg)::idtl))      ->
	  makerec (constarg::assums,
		   id::cargs,
		   id::constargs,
		   recargs,
		   indargs) tl idtl
      | (_, _) -> error "make_elim_branch_assumptions"
  in 
  makerec ([],[],[],[],[]) ba.branchsign
    (try list_firstn ba.nassums (pf_hyps gl)
     with Failure _ -> anomaly "make_elim_branch_assumptions")

let elim_on_ba tac ba gl = tac (make_elim_branch_assumptions ba gl) gl

let make_case_branch_assumptions ba gl =
  let rec makerec (assums,cargs,constargs,recargs) p_0 p_1 =
    match p_0,p_1 with 
      | ([], _) -> 
          { ba = ba;
            assums    = assums;
            cargs     = cargs;
            constargs = constargs;
            recargs   = recargs;
            indargs   = []}
      | ((true::tl), ((idrec,_,_ as recarg)::idtl)) ->
	  makerec (recarg::assums,
		   idrec::cargs,
		   idrec::recargs,
		   constargs) tl idtl
      | ((false::tl), ((id,_,_ as constarg)::idtl)) ->
	  makerec (constarg::assums,
		   id::cargs,
		   recargs,
		   id::constargs) tl idtl
      | (_, _) -> error "make_case_branch_assumptions"
  in 
  makerec ([],[],[],[]) ba.branchsign
    (try list_firstn ba.nassums (pf_hyps gl)
     with Failure _ -> anomaly "make_case_branch_assumptions")

let case_on_ba tac ba gl = tac (make_case_branch_assumptions ba gl) gl

