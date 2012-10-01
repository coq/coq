(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Names
open Term
open Termops
open Sign
open Declarations
open Tacmach
open Clenv
open Clenvtac
open Misctypes

(************************************************************************)
(* Tacticals re-exported from the Refiner module                        *)
(************************************************************************)

let tclNORMEVAR      = Refiner.tclNORMEVAR
let tclIDTAC         = Refiner.tclIDTAC
let tclIDTAC_MESSAGE = Refiner.tclIDTAC_MESSAGE
let tclORELSE0       = Refiner.tclORELSE0
let tclORELSE        = Refiner.tclORELSE
let tclTHEN          = Refiner.tclTHEN
let tclTHENLIST      = Refiner.tclTHENLIST
let tclMAP           = Refiner.tclMAP
let tclTHEN_i        = Refiner.tclTHEN_i
let tclTHENFIRST     = Refiner.tclTHENFIRST
let tclTHENLAST      = Refiner.tclTHENLAST
let tclTHENS         = Refiner.tclTHENS
let tclTHENSV        = Refiner.tclTHENSV
let tclTHENSFIRSTn   = Refiner.tclTHENSFIRSTn
let tclTHENSLASTn    = Refiner.tclTHENSLASTn
let tclTHENFIRSTn    = Refiner.tclTHENFIRSTn
let tclTHENLASTn     = Refiner.tclTHENLASTn
let tclREPEAT        = Refiner.tclREPEAT
let tclREPEAT_MAIN   = Refiner.tclREPEAT_MAIN
let tclFIRST         = Refiner.tclFIRST
let tclSOLVE         = Refiner.tclSOLVE
let tclTRY           = Refiner.tclTRY
let tclCOMPLETE      = Refiner.tclCOMPLETE
let tclAT_LEAST_ONCE = Refiner.tclAT_LEAST_ONCE
let tclFAIL          = Refiner.tclFAIL
let tclFAIL_lazy     = Refiner.tclFAIL_lazy
let tclDO            = Refiner.tclDO
let tclTIMEOUT       = Refiner.tclTIMEOUT
let tclWEAK_PROGRESS = Refiner.tclWEAK_PROGRESS
let tclPROGRESS      = Refiner.tclPROGRESS
let tclSHOWHYPS      = Refiner.tclSHOWHYPS
let tclNOTSAMEGOAL   = Refiner.tclNOTSAMEGOAL
let tclTHENTRY       = Refiner.tclTHENTRY
let tclIFTHENELSE    = Refiner.tclIFTHENELSE
let tclIFTHENSELSE   = Refiner.tclIFTHENSELSE
let tclIFTHENSVELSE   = Refiner.tclIFTHENSVELSE
let tclIFTHENTRYELSEMUST = Refiner.tclIFTHENTRYELSEMUST

(* Synonyms *)

let tclTHENSEQ       = tclTHENLIST

(* Experimental *)

let rec tclFIRST_PROGRESS_ON tac = function
  | []    -> tclFAIL 0 (str "No applicable tactic")
  | [a]   -> tac a (* so that returned failure is the one from last item *)
  | a::tl -> tclORELSE (tac a) (tclFIRST_PROGRESS_ON tac tl)

(************************************************************************)
(* Tacticals applying on hypotheses                                     *)
(************************************************************************)

let nthDecl m gl =
  try List.nth (pf_hyps gl) (m-1)
  with Failure _ -> error "No such assumption."

let nthHypId m gl = pi1 (nthDecl m gl)
let nthHyp m gl   = mkVar (nthHypId m gl)

let lastDecl gl   = nthDecl 1 gl
let lastHypId gl  = nthHypId 1 gl
let lastHyp gl    = nthHyp 1 gl

let nLastDecls n gl =
  try List.firstn n (pf_hyps gl)
  with Failure _ -> error "Not enough hypotheses in the goal."

let nLastHypsId n gl = List.map pi1 (nLastDecls n gl)
let nLastHyps n gl   = List.map mkVar (nLastHypsId n gl)

let onNthDecl m tac gl  = tac (nthDecl m gl) gl
let onNthHypId m tac gl = tac (nthHypId m gl) gl
let onNthHyp m tac gl   = tac (nthHyp m gl) gl

let onLastDecl  = onNthDecl 1
let onLastHypId = onNthHypId 1
let onLastHyp   = onNthHyp 1

let onHyps find tac gl = tac (find gl) gl

let onNLastDecls n tac  = onHyps (nLastDecls n) tac
let onNLastHypsId n tac = onHyps (nLastHypsId n) tac
let onNLastHyps n tac   = onHyps (nLastHyps n) tac

let afterHyp id gl =
  fst (List.split_when (fun (hyp,_,_) -> hyp = id) (pf_hyps gl))

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

let fullGoal gl = None :: List.map Option.make (pf_ids_of_hyps gl)

let onAllHyps tac gl = tclMAP tac (pf_ids_of_hyps gl) gl
let onAllHypsAndConcl tac gl = tclMAP tac (fullGoal gl) gl

let tryAllHyps tac gl = tclFIRST_PROGRESS_ON tac (pf_ids_of_hyps gl) gl
let tryAllHypsAndConcl tac gl = tclFIRST_PROGRESS_ON tac (fullGoal gl) gl

let onClause tac cl gls =
  let hyps () = pf_ids_of_hyps gls in
  tclMAP tac (Locusops.simple_clause_of hyps cl) gls
let onClauseLR tac cl gls =
  let hyps () = pf_ids_of_hyps gls in
  tclMAP tac (List.rev (Locusops.simple_clause_of hyps cl)) gls

let ifOnHyp pred tac1 tac2 id gl =
  if pred (id,pf_get_hyp_typ gl id) then
    tac1 id gl
  else
    tac2 id gl

(************************************************************************)
(* Elimination Tacticals                                                *)
(************************************************************************)

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
  branchnames : intro_pattern_expr Loc.located list}

type branch_assumptions = {
  ba        : branch_args;     (* the branch args *)
  assums    : named_context}   (* the list of assumptions introduced *)

let fix_empty_or_and_pattern nv l =
  (* 1- The syntax does not distinguish between "[ ]" for one clause with no
     names and "[ ]" for no clause at all *)
  (* 2- More generally, we admit "[ ]" for any disjunctive pattern of
     arbitrary length *)
  if l = [[]] then List.make nv [] else l

let check_or_and_pattern_size loc names n =
  if List.length names <> n then
    if n = 1 then
      user_err_loc (loc,"",str "Expects a conjunctive pattern.")
    else
      user_err_loc (loc,"",str "Expects a disjunctive pattern with " ++ int n
	++ str " branches.")

let compute_induction_names n = function
  | None ->
      Array.make n []
  | Some (loc,IntroOrAndPattern names) ->
      let names = fix_empty_or_and_pattern n names in
      check_or_and_pattern_size loc names n;
      Array.of_list names
  | Some (loc,_) ->
      user_err_loc (loc,"",str "Disjunctive/conjunctive introduction pattern expected.")

let compute_construtor_signatures isrec (_,k as ity) =
  let rec analrec c recargs =
    match kind_of_term c, recargs with
    | Prod (_,_,c), recarg::rest ->
	let b = match dest_recarg recarg with
	  | Norec | Imbr _  -> false
	  | Mrec (_,j)  -> isrec & j=k
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
  Array.map2 analrec lc lrecargs

let elimination_sort_of_goal gl =
  pf_apply Retyping.get_sort_family_of gl (pf_concl gl)

let elimination_sort_of_hyp id gl =
  pf_apply Retyping.get_sort_family_of gl (pf_get_hyp_typ gl id)

let elimination_sort_of_clause = function
  | None -> elimination_sort_of_goal
  | Some id -> elimination_sort_of_hyp id

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
      | _         -> anomaly "elimination"
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
	  error ("The elimination combinator " ^ name_elim ^ " is unknown.")
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
           clenv_unify ~flags:Unification.elim_flags
             Reduction.CONV (mkMeta pmv) p elimclause'
  in
  elim_res_pf_THEN_i elimclause' branchtacs gl

(* computing the case/elim combinators *)

let gl_make_elim ind gl =
  Indrec.lookup_eliminator ind (elimination_sort_of_goal gl)

let gl_make_case_dep ind gl =
  pf_apply Indrec.build_case_analysis_scheme gl ind true
    (elimination_sort_of_goal gl)

let gl_make_case_nodep ind gl =
  pf_apply Indrec.build_case_analysis_scheme gl ind false
    (elimination_sort_of_goal gl)

let elimination_then_using tac predicate bindings c gl =
  let (ind,t) = pf_reduce_to_quantified_ind gl (pf_type_of gl c) in
  let indclause  = mk_clenv_from gl (c,t) in
  let isrec,mkelim =
    if (Global.lookup_mind (fst ind)).mind_record
    then false,gl_make_case_dep
    else true,gl_make_elim
  in
  general_elim_then_using mkelim isrec
    None tac predicate bindings ind indclause gl

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
      | (_, _) -> anomaly "make_elim_branch_assumptions"
  in
  makerec ([],[],[],[],[]) ba.branchsign
    (try List.firstn ba.nassums (pf_hyps gl)
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
      | (_, _) -> anomaly "make_case_branch_assumptions"
  in
  makerec ([],[],[],[]) ba.branchsign
    (try List.firstn ba.nassums (pf_hyps gl)
     with Failure _ -> anomaly "make_case_branch_assumptions")

let case_on_ba tac ba gl = tac (make_case_branch_assumptions ba gl) gl

