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
open Clenv
open Pattern
open Matching
open Genarg
open Tacexpr


(* arnaud: encore un truc factice*)

let pf_reduce_to_quantified_ind _ = Util.anomaly "Tacticals.pf_reduce_to_quantified_ing: fantome"

(*arnaud: /encore un truc factice*)


(*** Preliminary Definition, to avoid opening the whole Goal module *)
let (>>=) = Goal.bind


(******************************************)
(*         Basic Tacticals                *)
(******************************************)

(*************************************************)
(* Tacticals re-exported from the Refiner module.*)
(*************************************************)

let tclIDTAC         = Proofview.tclIDTAC () (* arnaud: restaurer?: tclIDTAC*)
let tclIDTAC_MESSAGE = fun _ -> Util.anomaly "Tacticals.tclIDTAC_MESSAGE: à restaurer" (* arnaud: restaurer: tclIDTAC_MESSAGE*)
let tclORELSE        = fun _ _ -> Util.anomaly "Tacticals.tclORELSE: à restaurer" (* arnaud: restaurer: tclORELSE*)
let tclTHEN          = fun _ _ -> Util.anomaly "Tacticals.tclTHEN: à restaurer" (* arnaud: restaurer: tclTHEN*)
let tclTHENLIST      = fun  _ -> Util.anomaly "Tacticals.tclTHENLIST: à restaurer" (* arnaud: restaurer: tclTHENLIST*)
let tclTHEN_i        = fun  _ _-> Util.anomaly "Tacticals.tclTHEN_i: à restaurer" (* arnaud: restaurer: tclTHEN_i*)
let tclTHENFIRST     = fun _ _ -> Util.anomaly "Tacticals.tclTHENFIRST: à restaurer" (* arnaud: restaurer: tclTHENFIRST*)
let tclTHENLAST      = fun _ _ -> Util.anomaly "Tacticals.tclTHENLAST: à restaurer" (* arnaud: restaurer: tclTHENLAST*)
let tclTHENS         = fun _ _ -> Util.anomaly "Tacticals.tclTHENS: à restaurer" (* arnaud: restaurer: tclTHENS*)
let tclTHENSV        = fun _ _ -> Util.anomaly "Tacticals.tclTHENSV: à restaurer" (* arnaud: restaurer: Refiner.tclTHENSV*)
let tclTHENSFIRSTn   = fun _ -> Util.anomaly "Tacticals.tclTHENSFIRSTn: à restaurer" (* arnaud: restaurer: Refiner.tclTHENSFIRSTn*)
let tclTHENSLASTn tac1 tac2 tacns = 
  Logic.tclTHENLIST
    [
      tac1;
      Proofview.tclEMPTY (Pp.str "tclTHENSLASTn");
      Logic.tclEXTENDARRAYS [||] tac2 tacns
    ]
let tclTHENFIRSTn    = fun _ -> Util.anomaly "Tacticals.tclTHENFIRSTn: à restaurer" (* arnaud: restaurer: Refiner.tclTHENFIRSTn*)
let tclTHENLASTn tac1 tacns = 
  tclTHENSLASTn tac1 (Proofview.tclIDTAC ()) tacns
let tclREPEAT        = fun _ -> Util.anomaly "Tacticals.tclREPEAT: à restaurer" (* arnaud: restaurer: Refiner.tclREPEAT*)
let tclREPEAT_MAIN   = fun _ -> Util.anomaly "Tacticals.tclREPEAT_MAIN: à restaurer" (* arnaud: restaurer: tclREPEAT_MAIN*)
let tclFIRST         = fun _ -> Util.anomaly "Tacticals.tclFIRST: à restaurer" (* arnaud: restaurer: Refiner.tclFIRST*)
let tclSOLVE         = fun _ -> Util.anomaly "Tacticals.tclSOLVE: à restaurer" (* arnaud: restaurer: Refiner.tclSOLVE*)
let tclTRY           = fun _ -> Util.anomaly "Tacticals.tclTRY: à restaurer" (* arnaud: restaurer: Refiner.tclTRY*)
let tclINFO          = fun _ -> Util.anomaly "Tacticals.tclINFO: à restaurer" (* arnaud: restaurer: Refiner.tclINFO*)
let tclCOMPLETE      = fun _ -> Util.anomaly "Tacticals.tclCOMPLETE: à restaurer" (* arnaud: restaurer: Refiner.tclCOMPLETE*)
let tclAT_LEAST_ONCE = fun _ -> Util.anomaly "Tacticals.tclAT_LEAST_ONCE: à restaurer" (* arnaud: restaurer: Refiner.tclAT_LEAST_ONCE*)
let tclFAIL          = fun _ -> Util.anomaly "Tacticals.tclFAIL: à restaurer" (* arnaud: restaurer: Refiner.tclFAIL*)
let tclDO            = fun _ -> Util.anomaly "Tacticals.tclDO: à restaurer" (* arnaud: restaurer: Refiner.tclDO*)
let tclPROGRESS      = fun _ -> Util.anomaly "Tacticals. tclPROGRESS: à restaurer" (* arnaud: restaurer: Refiner.tclPROGRESS *)
let tclWEAK_PROGRESS = fun _ -> Util.anomaly "Tacticals.tclWEAK_PROGRESS: à restaurer" (* arnaud: restaurer: Refiner.tclWEAK_PROGRESS *)
let tclNOTSAMEGOAL   = fun _ -> Util.anomaly "Tacticals.tclNOTSAMEGOAL: à restaurer" (* arnaud: restaurer: Refiner.tclNOTSAMEGOAL *)
let tclTHENTRY       = fun _ -> Util.anomaly "Tacticals.tclTHENTRY: à restaurer" (* arnaud: restaurer: tclTHENTRY *)
let tclIFTHENELSE    = fun _ -> Util.anomaly "Tacticals.tclIFTHENELSE: à restaurer" (* arnaud: restaurer: tclIFTHENELSE *)
let tclIFTHENSELSE   = fun _ -> Util.anomaly "Tacticals.tclIFTHENSELSE: à restaurer" (* arnaud: restaurer: tclIFTHENSELSE *)
let tclIFTHENSVELSE   = fun _ -> Util.anomaly "Tacticals.tclIFTHENSVELSE: à restaurer" (* arnaud: restaurer: tclIFTHENSVELSE *)
let tclIFTHENTRYELSEMUST = fun _ -> Util.anomaly "Tacticals.tclIFTHENTRYELSEMUST: à restaurer" (* arnaud: restaurer: tclIFTHENTRYELSEMUST *)

(* probablement mort
let unTAC            = fun _ -> Util.anomaly "Tacticals.unTAC: à restaurer" (* arnaud: restaurer: unTAC*)
*)

(* [rclTHENSEQ [t1;..;tn] is equivalent to t1;..;tn *)
(* arnaud: à vérifier *)
let tclTHENSEQ l = List.fold_left tclTHEN tclIDTAC l

(* map_tactical f [x1..xn] = (f x1);(f x2);...(f xn) *)
(* tclMAP f [x1..xn] = (f x1);(f x2);...(f xn) *)
let tclMAP tacfun l = 
  Util.anomaly "Tacticals.tclMAP: à restaurer"
  (* arnaud: à restaurer
  List.fold_right (fun x -> (tclTHEN (tacfun x))) l tclIDTAC
  *)

(* apply a tactic to the nth element of the signature  *)

let tclNTH_HYP m (tac : constr Goal.sensitive -> 'a Proofview.tactic) =
  let v =
    m >>= fun m ->
    Goal.hyps >>= fun hyps ->
    let (id,_,_) = List.nth (Environ.named_context_of_val hyps) (m-1) in
    try 
      Goal.return (mkVar id)
    with Failure _ ->
      error "No such assumption"
  in
  tac v

(* apply a tactic to the last element of the signature  *)

let tclLAST_HYP tac = tclNTH_HYP (Goal.return 1) tac

let tclTRY_sign ftac sign =
  let rec arec = function
    | []      -> tclFAIL 0 (str "no applicable hypothesis")
    | [s]     -> ftac (mkVar s) (*added in order to get useful error messages *)
    | (s::sl) -> tclORELSE (ftac (mkVar s)) (arec sl) 
  in 
  arec (ids_of_named_context sign)

let tclTRY_HYPS (tac : constr Goal.sensitive -> 'a Proofview.tactic) = 
  Util.anomaly "Ntacticals.tclTRY_HYPS: à restaurer"
  (* arnaud: à restaurer: conflit entre ce type et celui de tclTRY_sign...
  let h =
    Goal.hyps >>= fun hyps ->
    Goal.return (named_context_of_val hyps)
  in
  tclTRY_sign tac h
  *)

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

let allClauses = { onhyps=None; onconcl=true; concl_occs=[] }
let allHyps = { onhyps=None; onconcl=false; concl_occs=[] }
let onHyp id = { onhyps=Some[(([],id),InHyp)]; onconcl=false; concl_occs=[] }
let onConcl = { onhyps=Some[]; onconcl=true; concl_occs=[] }

(* arnaud: débranchement temporaire, restaurer tout ça
let simple_clause_list_of cl gls =
  let hyps =
    match cl.onhyps with 
        None -> List.map (fun id -> Some(([],id),InHyp)) (pf_ids_of_hyps gls)
      | Some l -> List.map (fun h -> Some h) l in
  if cl.onconcl then None::hyps else hyps


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

*)

(* Create a clause list with all the hypotheses from the context, occuring
   after id *)

let afterHyp id =
  Goal.hyps >>= fun hyps ->
  let sign = Environ.named_context_of_val hyps in
  Goal.return (fst (list_splitby (fun (hyp,_,_) -> hyp = id) sign))
  
(*  

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

fin du débranchement de cette section. *)

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

let elimination_sort_of_goal  =
  Goal.concl >>= fun concl ->
  Logic.hnf_type_of concl >>= fun typ -> 
  Goal.return (
    match kind_of_term typ with 
    | Sort s ->
	(match s with
	   | Prop Null -> InProp
	   | Prop Pos -> InSet
	   | Type _ -> InType)
    | _        -> anomaly "goal should be a type"
  )

let elimination_sort_of_hyp id = 
  Util.anomaly "Tacticals.elimination_sort_of_hyps: à restaurer"
  (* arnaud: à restaurer:
  match kind_of_term (hnf_type_of gl (pf_get_hyp_typ gl id)) with 
    | Sort s ->
	(match s with
	   | Prop Null -> InProp
	   | Prop Pos -> InSet
	   | Type _ -> InType)
    | _        -> anomaly "goal should be a type"
  *)


(* Find the right elimination suffix corresponding to the sort of the goal *)
(* c should be of type A1->.. An->B with B an inductive definition *)

let last_arg c = match kind_of_term c with
  | App (f,cl) -> array_last cl
  | _ -> anomaly "last_arg"

let general_elim_then_using 
  elim isrec allnames tac predicate (indbindings,elimbindings) c =
  Util.anomaly "general_elim_then_using: todo" (* arnaud: à restaurer
  let (ity,t) = pf_reduce_to_quantified_ind gl (pf_type_of gl c) in
  (* applying elimination_scheme just a little modified *)
  let indclause  = mk_clenv_from gl (c,t) in
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
  let branchsigns = compute_construtor_signatures isrec ity in
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
               ity = ity;
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
					       *)

let elimination_then_using tac predicate (indbindings,elimbindings) c = 
  Logic.type_of c >>= fun type_of_c -> 
  pf_reduce_to_quantified_ind type_of_c >>= fun (ind,t) ->
  elimination_sort_of_goal >>= fun s ->
  let elim = Indrec.lookup_eliminator ind s in
  general_elim_then_using
    elim true IntroAnonymous tac predicate (indbindings,elimbindings) c


let elimination_then tac        = elimination_then_using tac None 
let simple_elimination_then tac = elimination_then tac ([],[])

let case_then_using allnames tac predicate (indbindings,elimbindings) c =
  (* finding the case combinator *)
  Logic.type_of c >>= fun type_of_c ->
  pf_reduce_to_quantified_ind type_of_c >>= fun (ity,t) ->
  Goal.defs >>= fun defs ->
  let sigma = Evd.evars_of defs in 
  elimination_sort_of_goal >>= fun sort ->
  Goal.env >>= fun env ->
  let elim  = Indrec.make_case_dep env sigma ity sort in  
  general_elim_then_using 
    elim false allnames tac predicate (indbindings,elimbindings) c

let case_nodep_then_using allnames tac predicate (indbindings,elimbindings)
  c =
  (* finding the case combinator *)
  Logic.type_of c >>= fun type_of_c ->
  pf_reduce_to_quantified_ind type_of_c >>= fun (ity,t) ->
  Goal.defs >>= fun defs ->
  let sigma = Evd.evars_of defs in 
  elimination_sort_of_goal >>= fun sort ->
  Goal.env >>= fun env ->
  let elim  = Indrec.make_case_nodep env sigma ity sort in  
  general_elim_then_using 
    elim false allnames tac predicate (indbindings,elimbindings) c


let make_elim_branch_assumptions ba =
  Util.anomaly "Tacticals.make_elim_branch_assumption: à restaurer"
  (* arnaud: à restaurer:
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
  *)

let elim_on_ba tac ba = tac (make_elim_branch_assumptions ba)

let make_case_branch_assumptions ba  =
  Util.anomaly "Tacticals.make_case_branch_assumption: à restaurer"
  (* arnaud: à restaurer
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
  *)

let case_on_ba tac ba = tac (make_case_branch_assumptions ba)

