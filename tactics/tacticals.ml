(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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
open Libnames
open Refiner
open Tacmach
open Clenv
open Clenvtac
open Rawterm
open Pattern
open Matching
open Evar_refiner
open Genarg
open Tacexpr

(******************************************)
(*         Basic Tacticals                *)
(******************************************)

(*************************************************)
(* Tacticals re-exported from the Refiner module.*)
(*************************************************)

let tclNORMEVAR      = tclNORMEVAR
let tclIDTAC         = tclIDTAC
let tclIDTAC_MESSAGE = tclIDTAC_MESSAGE
let tclORELSE        = tclORELSE
let tclTHEN          = tclTHEN
let tclTHENLIST      = tclTHENLIST
let tclTHEN_i        = tclTHEN_i
let tclTHENFIRST     = tclTHENFIRST
let tclTHENLAST      = tclTHENLAST
let tclTHENS         = tclTHENS
let tclTHENSV        = Refiner.tclTHENSV
let tclTHENSFIRSTn   = Refiner.tclTHENSFIRSTn
let tclTHENSLASTn    = Refiner.tclTHENSLASTn
let tclTHENFIRSTn    = Refiner.tclTHENFIRSTn
let tclTHENLASTn     = Refiner.tclTHENLASTn
let tclREPEAT        = Refiner.tclREPEAT
let tclREPEAT_MAIN   = tclREPEAT_MAIN
let tclFIRST         = Refiner.tclFIRST
let tclSOLVE         = Refiner.tclSOLVE
let tclTRY           = Refiner.tclTRY
let tclINFO          = Refiner.tclINFO
let tclCOMPLETE      = Refiner.tclCOMPLETE
let tclAT_LEAST_ONCE = Refiner.tclAT_LEAST_ONCE
let tclFAIL          = Refiner.tclFAIL
let tclDO            = Refiner.tclDO
let tclPROGRESS      = Refiner.tclPROGRESS
let tclWEAK_PROGRESS = Refiner.tclWEAK_PROGRESS
let tclNOTSAMEGOAL   = Refiner.tclNOTSAMEGOAL
let tclTHENTRY       = tclTHENTRY
let tclIFTHENELSE    = tclIFTHENELSE
let tclIFTHENSELSE   = tclIFTHENSELSE
let tclIFTHENSVELSE   = tclIFTHENSVELSE
let tclIFTHENTRYELSEMUST = tclIFTHENTRYELSEMUST

let unTAC            = unTAC

(* [rclTHENSEQ [t1;..;tn] is equivalent to t1;..;tn *)
let tclTHENSEQ = List.fold_left tclTHEN tclIDTAC

(* map_tactical f [x1..xn] = (f x1);(f x2);...(f xn) *)
(* tclMAP f [x1..xn] = (f x1);(f x2);...(f xn) *)
let tclMAP tacfun l = 
  List.fold_right (fun x -> (tclTHEN (tacfun x))) l tclIDTAC

(* apply a tactic to the nth element of the signature  *)

let tclNTH_HYP m (tac : constr->tactic) gl =
  tac (try mkVar(let (id,_,_) = List.nth (pf_hyps gl) (m-1) in id) 
       with Failure _ -> error "No such assumption") gl

(* apply a tactic to the last element of the signature  *)

let tclLAST_HYP = tclNTH_HYP 1

let tclLAST_NHYPS n tac gl =
  tac (try list_firstn n (pf_ids_of_hyps gl)
       with Failure _ -> error "No such assumptions") gl

let tclTRY_sign (tac : constr->tactic) sign gl =
  let rec arec = function
    | []      -> tclFAIL 0 (str "no applicable hypothesis")
    | [s]     -> tac (mkVar s) (*added in order to get useful error messages *)
    | (s::sl) -> tclORELSE (tac (mkVar s)) (arec sl) 
  in 
  arec (ids_of_named_context sign) gl

let tclTRY_HYPS (tac : constr->tactic) gl = 
  tclTRY_sign tac (pf_hyps gl) gl

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

type simple_clause = identifier gsimple_clause
type clause = identifier gclause

let allClauses = { onhyps=None; concl_occs=all_occurrences_expr }
let allHyps = { onhyps=None; concl_occs=no_occurrences_expr }
let onConcl = { onhyps=Some[]; concl_occs=all_occurrences_expr }
let onHyp id =
  { onhyps=Some[((all_occurrences_expr,id),InHyp)]; concl_occs=no_occurrences_expr }

let simple_clause_list_of cl gls =
  let hyps =
    match cl.onhyps with 
    | None ->
	let f id = Some((all_occurrences_expr,id),InHyp) in
	List.map f (pf_ids_of_hyps gls)
    | Some l ->
	List.map (fun h -> Some h) l in
  if cl.concl_occs = all_occurrences_expr then None::hyps else hyps


(* OR-branch *)
let tryClauses tac cl gls = 
  let rec firstrec = function
    | []      -> tclFAIL 0 (str "no applicable hypothesis")
    | [cls]   -> tac cls (* added in order to get a useful error message *)
    | cls::tl -> (tclORELSE (tac cls) (firstrec tl))
  in
  let hyps = simple_clause_list_of cl gls in
  firstrec hyps gls

(* AND-branch *)
let onClauses tac cl gls = 
  let hyps = simple_clause_list_of cl gls in
  tclMAP tac hyps gls

(* AND-branch reverse order*)
let onClausesLR tac cl gls = 
  let hyps = simple_clause_list_of cl gls in
  tclMAP tac (List.rev hyps) gls

(* A clause corresponding to the |n|-th hypothesis or None *)

let nth_clause n gl =
  if n = 0 then 
    onConcl
  else if n < 0 then 
    let id = List.nth (List.rev (pf_ids_of_hyps gl)) (-n-1) in 
    onHyp id
  else 
    let id = List.nth (pf_ids_of_hyps gl) (n-1) in 
    onHyp id

(* Gets the conclusion or the type of a given hypothesis *)

let clause_type cls gl =
  match simple_clause_of cls with
    | None    -> pf_concl gl
    | Some ((_,id),_) -> pf_get_hyp_typ gl id

(* Functions concerning matching of clausal environments *)

let pf_is_matching gls pat n =
  is_matching_conv (pf_env gls) (project gls) pat n

let pf_matches gls pat n =
  matches_conv (pf_env gls) (project gls) pat n

(* [OnCL clausefinder clausetac]
 * executes the clausefinder to find the clauses, and then executes the
 * clausetac on the clause so obtained. *)

let onCL cfind cltac gl = cltac (cfind gl) gl


(* [OnHyps hypsfinder hypstac]
 * idem [OnCL] but only for hypotheses, not for conclusion *)

let onHyps find tac gl = tac (find gl) gl



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


let onClause t cls gl  = t cls gl
let tryAllClauses  tac = tryClauses tac allClauses
let onAllClauses   tac = onClauses tac allClauses
let onAllClausesLR tac = onClausesLR tac allClauses
let onNthLastHyp n tac gls = tac (nth_clause n gls) gls

let tryAllHyps     tac =
  tryClauses (function Some((_,id),_) -> tac id | _ -> assert false) allHyps
let onNLastHyps n  tac     = onHyps (nLastHyps n) (tclMAP tac)
let onLastHyp      tac gls = tac (lastHyp gls) gls

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
  branchsign : bool list;   (* the signature of the branch.
                               true=recursive argument, false=constant *)
  branchnames : intro_pattern_expr list}

type branch_assumptions = {
  ba        : branch_args;     (* the branch args *)
  assums    : named_context}   (* the list of assumptions introduced *)

let compute_induction_names n = function
  | IntroAnonymous ->
      Array.make n []
  | IntroOrAndPattern names when List.length names = n ->
      Array.of_list names
  | _ ->
      errorlabstrm "" (str "Expects " ++ int n ++ str " lists of names")

let compute_construtor_signatures isrec (_,k as ity) =
  let rec analrec c recargs =
    match kind_of_term c, recargs with 
    | Prod (_,_,c), recarg::rest ->
	let b = match dest_recarg recarg with
	  | Norec | Imbr _  -> false
	  | Mrec j  -> isrec & j=k
	in b :: (analrec c rest)
    | LetIn (_,_,_,c), rest -> false :: (analrec c rest)
    | _, [] -> []
    | _ -> anomaly "compute_construtor_signatures"
  in 
  let (mib,mip) = Global.lookup_inductive ity in
  let n = mib.mind_nparams in
  let lc =
    Array.map (fun c -> snd (decompose_prod_n_assum n c)) mip.mind_nf_lc in
  let lrecargs = dest_subterms mip.mind_recargs in
  array_map2 analrec lc lrecargs

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

let general_elim_then_using mk_elim 
  isrec allnames tac predicate (indbindings,elimbindings) 
  ind indclause gl =
  let elim = mk_elim ind gl in
  (* applying elimination_scheme just a little modified *)
  let indclause' = clenv_match_args indbindings indclause in
  let elimclause = mk_clenv_from gl (elim,pf_type_of gl elim) in
  let indmv = 
    match kind_of_term (last_arg elimclause.templval.Evd.rebus) with
      | Meta mv -> mv
      | _         -> error "elimination"
  in
  let pmv =
    let p, _ = decompose_app elimclause.templtyp.Evd.rebus in
    match kind_of_term p with
      | Meta p -> p
      | _ ->
	  let name_elim =
	    match kind_of_term elim with
	      | Const kn -> string_of_con kn
	      | Var id -> string_of_id id
	      | _ -> "\b"
	  in
	  error ("The elimination combinator " ^ name_elim ^ " is not known") 
  in
  let elimclause' = clenv_fchain indmv elimclause indclause' in
  let elimclause' = clenv_match_args elimbindings elimclause' in
  let branchsigns = compute_construtor_signatures isrec ind in
  let brnames = compute_induction_names (Array.length branchsigns) allnames in
  let after_tac ce i gl =
    let (hd,largs) = decompose_app ce.templtyp.Evd.rebus in
    let ba = { branchsign = branchsigns.(i);
               branchnames = brnames.(i);
               nassums = 
		 List.fold_left 
                   (fun acc b -> if b then acc+2 else acc+1)
                   0 branchsigns.(i);
               branchnum = i+1;
               ity = ind;
               largs = List.map (clenv_nf_meta ce) largs;
               pred = clenv_nf_meta ce hd }
    in 
    tac ba gl
  in
  let branchtacs ce = Array.init (Array.length branchsigns) (after_tac ce) in
  let elimclause' =
    match predicate with
       | None   -> elimclause'
       | Some p ->
           clenv_unify true Reduction.CONV (mkMeta pmv) p elimclause'
  in 
  elim_res_pf_THEN_i elimclause' branchtacs gl

(* computing the case/elim combinators *)

let gl_make_elim ind gl =
  Indrec.lookup_eliminator ind (elimination_sort_of_goal gl)

let gl_make_case_dep ind gl =
  pf_apply Indrec.make_case_dep gl ind (elimination_sort_of_goal gl)

let gl_make_case_nodep ind gl =
  pf_apply Indrec.make_case_nodep gl ind (elimination_sort_of_goal gl)

let elimination_then_using tac predicate bindings c gl = 
  let (ind,t) = pf_reduce_to_quantified_ind gl (pf_type_of gl c) in
  let indclause  = mk_clenv_from gl (c,t) in
  general_elim_then_using gl_make_elim
    true IntroAnonymous tac predicate bindings ind indclause gl

let case_then_using =
  general_elim_then_using gl_make_case_dep false

let case_nodep_then_using =
  general_elim_then_using gl_make_case_nodep false

let elimination_then tac        = elimination_then_using tac None 
let simple_elimination_then tac = elimination_then tac ([],[])


let make_elim_branch_assumptions ba gl =   
  let rec makerec (assums,cargs,constargs,recargs,indargs) lb lc =
    match lb,lc with 
      | ([], _) -> 
          { ba = ba;
            assums    = assums}
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
            assums    = assums}
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

