
(* $Id$ *)

open Pp
open Util
open Names
open Generic
open Term
open Sign
open Inductive
open Reduction
open Environ
open Declare
open Tacmach
open Proof_trees
open Clenv
open Pattern
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

(* map_tactical f [x1..xn] = (f x1);(f x2);...(f xn) *)
(* tclMAP f [x1..xn] = (f x1);(f x2);...(f xn) *)
let tclMAP tacfun l = 
  List.fold_right (fun x -> (tclTHEN (tacfun x))) l tclIDTAC

let dyn_tclIDTAC = function [] -> tclIDTAC |  _ -> anomaly "tclIDTAC"

let dyn_tclFAIL  = function [] -> tclFAIL |  _ -> anomaly "tclFAIL"

let tclTHEN_i1 tac1 tac2 = tclTHEN_i tac1 tac2 1

(* apply a tactic to the nth element of the signature  *)

let tclNTH_HYP m (tac:constr->tactic) gl =
  tac (try VAR(fst(nth_sign (pf_untyped_hyps gl) m)) 
       with Failure _ -> error "No such assumption") gl

(* apply a tactic to the last element of the signature  *)

let tclLAST_HYP = tclNTH_HYP 1

let tclTRY_sign (tac:constr->tactic) sign gl =
  let rec arec = function
    | []      -> tclFAIL
    | [s]     -> tac (VAR(s)) (* added in order to get useful error messages *)
    | (s::sl) -> tclORELSE (tac (VAR(s))) (arec sl) 
  in 
  arec (fst sign) gl

let tclTRY_HYPS (tac:constr->tactic) gl = 
  tclTRY_sign tac (pf_untyped_hyps gl) gl

(* OR-branch *)
let tryClauses tac = 
  let rec firstrec = function
    | []      -> tclFAIL
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
    let id = List.nth (ids_of_sign (pf_untyped_hyps gl)) (-n-1) in 
    Some id
  else 
    let id = List.nth (ids_of_sign (pf_untyped_hyps gl)) (n-1) in 
    Some id

(* Gets the conclusion or the type of a given hypothesis *)

let clause_type cls gl =
  match cls with
    | None    -> pf_concl gl
    | Some id -> pf_get_hyp gl id

(* Functions concerning matching of clausal environments *)

let matches gls n pat =
  let m = get_pat pat in
  let (wc,_) = startWalk gls in 
  try let _ = Clenv.unify_0 [] wc m n in true with UserError _ -> false

let dest_match gls n pat =
  let m       = get_pat pat in
  let mvs     = collect_metas m in
  let (wc,_)  = startWalk gls in
  let (mvb,_) = Clenv.unify_0 [] wc m n in 
  List.map (fun x -> List.assoc x mvb) mvs


(* [OnCL clausefinder clausetac]
 * executes the clausefinder to find the clauses, and then executes the
 * clausetac on the list so obtained. *)

let onCL cfind cltac gl = cltac (cfind gl) gl


(* Create a clause list with all the hypotheses from the context *)

let allHyps gl = (List.map in_some (ids_of_sign (pf_untyped_hyps gl)))


(* Create a clause list with all the hypotheses from the context, occuring
   after id *)

let afterHyp id gl =
  List.map in_some
    (fst (list_splitby (fun hyp -> hyp = id) 
	    (ids_of_sign (pf_untyped_hyps gl))))
    

(* Create a singleton clause list with the last hypothesis from then context *)

let lastHyp gl = 
  let (id,_) = hd_sign (pf_untyped_hyps gl) in [(Some id)]

(* Create a clause list with the n last hypothesis from then context *)

let nLastHyps n gl =
  let ids =
    try list_firstn n (ids_of_sign (pf_untyped_hyps gl))
    with Failure "firstn" -> error "Not enough hypotheses in the goal"
  in 
  List.map in_some ids


(* A clause list with the conclusion and all the hypotheses *)

let allClauses gl = 
  let ids = ids_of_sign(pf_untyped_hyps gl) in  
  (None::(List.map in_some ids))

let onClause t cls gl  = t cls gl
let tryAllHyps     tac = onCL allHyps (tryClauses tac)
let tryAllClauses  tac = onCL allClauses (tryClauses tac)
let onAllClauses   tac = onCL allClauses (tclMAP tac)
let onAllClausesLR tac = onCL (compose List.rev allClauses) (tclMAP tac)
let onLastHyp      tac = onCL lastHyp (tclMAP tac)
let onNLastHyps n  tac = onCL (nLastHyps n) (tclMAP tac)
let onNthLastHyp n tac gls = tac (nth_clause n gls) gls

(* Serait-ce possible de compiler d'abord la tactique puis de faire la
   substitution sans passer par bdize dont l'objectif est de préparer un
   terme pour l'affichage ? (HH) *)

(* Si on enlève le dernier argument (gl) conclPattern est calculé une
fois pour toutes : en particulier si Pattern.somatch produit une UserError 
Ce qui fait que si la conclusion ne matche pas le pattern, Auto échoue, même
si après Intros la conclusion matche le pattern.
*)
(***TODO
let conclPattern concl pat tacast gl = 
  let constr_bindings = Pattern.somatch None pat concl in
  let ast_bindings = 
    List.map 
      (fun (i,c) -> (i, Termast.bdize false (assumptions_for_print []) c))
      constr_bindings in 
  let tacast' = CoqAst.subst_meta ast_bindings tacast in
    Tacinterp.interp tacast' gl
***)

let clauseTacThen tac continuation =
  (fun cls -> (tclTHEN (tac cls) continuation))

let if_tac pred tac1 tac2 gl =
  if pred gl then tac1 gl else tac2 gl

let ifOnClause pred tac1 tac2 cls gl =
  if pred (cls,clause_type cls gl) then
    tac1 cls gl
  else 
    tac2 cls gl

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
  ity        : constr;      (* the type we were eliminating on *)
  largs      : constr list; (* its arguments *)
  branchnum  : int;         (* the branch number *)
  pred       : constr;      (* the predicate we used *)
  nassums    : int;         (* the number of assumptions to be introduced *)
  branchsign : bool list}   (* the signature of the branch.
                               true=recursive argument, false=constant *)

type branch_assumptions = {
  ba        : branch_args;     (* the branch args *)
  assums    : identifier list; (* the list of assumptions introduced *)
  cargs     : identifier list; (* the constructor arguments *)
  constargs : identifier list; (* the CONSTANT constructor arguments *)
  recargs   : identifier list; (* the RECURSIVE constructor arguments *)
  indargs   : identifier list} (* the inductive arguments *)


(* Hum ... the following function looks quite similar to the one 
 * defined with the same name in Tactics.ml. 
 *  --Eduardo (11/8/97) *)

let reduce_to_ind gl t = 
  let rec elimrec t l = 
    match decomp_app(t) with
      | (DOPN(MutInd (sp,_),_) as mind,_) -> 
	  (mind,mind_path mind,t,prod_it t l)
      | (DOPN(Const _,_),_) -> 
	  elimrec (pf_nf_betaiota gl (pf_one_step_reduce gl t)) l
      | (DOP2(Cast,c,_),[]) -> elimrec c l
      | (DOP2(Prod,ty,DLAM(n,t')),[]) -> elimrec t' ((n,ty)::l)
      | _ -> error "Not an inductive product"
  in 
  elimrec t []

let case_sign ity i = 
  let rec analrec acc = function 
    | [] -> acc 
    | (c::rest) -> analrec (false::acc) rest
  in
  let recarg = mis_recarg (lookup_mind_specif ity (Global.unsafe_env())) in 
  analrec [] recarg.(i-1)

let elim_sign ity i =
  let (_,j,_) = destMutInd ity in
  let rec analrec acc = function 
    | (Param(_)::rest) -> analrec (false::acc) rest
    | (Norec::rest)    -> analrec (false::acc) rest
    | (Imbr(_)::rest)  -> analrec (false::acc) rest
    | (Mrec k::rest)   -> analrec ((j=k)::acc) rest
    | []               -> List.rev acc 
  in 
  let recarg = mis_recarg (lookup_mind_specif ity (Global.unsafe_env())) in
  analrec [] recarg.(i-1)

let sort_of_goal gl = 
  match hnf_type_of gl (pf_concl gl) with 
    | DOP0(Sort s) -> s
    | _            -> anomaly "goal should be a type"


(* Find the right elimination suffix corresponding to the sort of the goal *)
(* c should be of type A1->.. An->B with B an inductive definition *)

let suff gl cl = match hnf_type_of gl cl with
  | DOP0(Sort(Type(_)))    -> "_rect"
  | DOP0(Sort(Prop(Null))) -> "_ind"
  | DOP0(Sort(Prop(Pos)))  -> "_rec"
  | _                      -> anomaly "goal should be a type"

(* Look up function for the default elimination constant *)

let lookup_eliminator sign path suff =
  let name = id_of_string ((string_of_id (basename path)) ^ suff) in
  try 
    Declare.global_reference (kind_of_path path) name
  with UserError _ -> 
    VAR(fst(lookup_glob name (gLOB sign)))

let last_arg = function
  | DOPN(AppL,cl) -> cl.(Array.length cl - 1)
  | _ -> anomaly "last_arg"

let general_elim_then_using 
  elim elim_sign_fun tac predicate (indbindings,elimbindings) c gl =
  let (ity,_,_,t) = reduce_to_ind gl (pf_type_of gl c) in
  let name_elim =
    (match elim with
       | DOPN(Const sp,_) -> id_of_string(string_of_path sp)
       | VAR id -> id
       | _ -> id_of_string " ") 
  in
  (* applying elimination_scheme just a little modified *)
  let (wc,kONT)  = startWalk gl in
  let indclause  = mk_clenv_from wc (c,t) in
  let indclause' = clenv_constrain_with_bindings indbindings indclause in
  let elimclause = mk_clenv_from () (elim,w_type_of wc elim) in
  let indmv  = 
    match last_arg (clenv_template elimclause).rebus with
      | DOP0(Meta mv) -> mv
      | _            -> error "elimination"
  in
  let pmv = 
    match decomp_app (clenv_template_type elimclause).rebus with
      | (DOP0(Meta(p)),oplist) -> p
      | _ -> error ("The elimination combinator " ^
                    (string_of_id name_elim) ^ " is not known") 
  in
  let elimclause' = clenv_fchain indmv elimclause indclause' in
  let elimclause' = clenv_constrain_with_bindings elimbindings elimclause' in
  let after_tac ce i gl =
    let (hd,largs) = decomp_app (clenv_template_type ce).rebus in
    let branchsign =  elim_sign_fun ity i in
    let ba = { branchsign = branchsign;
               nassums = 
		 List.fold_left 
                   (fun acc b -> if b then acc+2 else acc+1) 0 branchsign;
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
  elim_res_pf_THEN_i kONT elimclause' after_tac 1 gl


let elimination_then_using tac predicate (indbindings,elimbindings) c gl = 
  let (ity,path_name,_,t) = reduce_to_ind gl (pf_type_of gl c) in
  let elim = 
    lookup_eliminator (pf_hyps gl) path_name (suff gl (pf_concl gl))
  in
  general_elim_then_using
    elim elim_sign tac predicate (indbindings,elimbindings) c gl


let elimination_then tac        = elimination_then_using tac None 
let simple_elimination_then tac = elimination_then tac ([],[])

let case_then_using tac predicate (indbindings,elimbindings) c gl =
  (* finding the case combinator *)
  let (ity,_,_,t) = reduce_to_ind gl (pf_type_of gl c) in
  let sigma = project gl in 
  let sort  = sort_of_goal gl  in
  let elim  = Indrec.make_case_gen (pf_env gl) sigma ity sort in  
  general_elim_then_using 
    elim case_sign tac predicate (indbindings,elimbindings) c gl

let case_nodep_then_using tac predicate (indbindings,elimbindings) c gl =
  (* finding the case combinator *)
  let (ity,_,_,t) = reduce_to_ind gl (pf_type_of gl c) in
  let sigma = project gl in 
  let sort  = sort_of_goal gl  in
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
      | ((true::tl), (recarg::indarg::idtl)) ->
	  makerec (recarg::indarg::assums,
		   recarg::cargs,
		   recarg::recargs,
		   constargs,
		   indarg::indargs) tl idtl
      | ((false::tl), (constarg::idtl))      ->
	  makerec (constarg::assums,
		   constarg::cargs,
		   constarg::constargs,
		   recargs,
		   indargs) tl idtl
      | (_, _) -> error "make_elim_branch_assumptions"
  in 
  makerec ([],[],[],[],[]) ba.branchsign
    (try list_firstn ba.nassums (ids_of_sign (pf_untyped_hyps gl))
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
      | ((true::tl), (recarg::idtl)) ->
	  makerec (recarg::assums,
		   recarg::cargs,
		   recarg::recargs,
		   constargs) tl idtl
      | ((false::tl), (constarg::idtl)) ->
	  makerec (constarg::assums,
		   constarg::cargs,
		   recargs,
		   constarg::constargs) tl idtl
      | (_, _) -> error "make_case_branch_assumptions"
  in 
  makerec ([],[],[],[]) ba.branchsign
    (try list_firstn ba.nassums (ids_of_sign (pf_untyped_hyps gl))
     with Failure _ -> anomaly "make_case_branch_assumptions")

let case_on_ba tac ba gl = tac (make_case_branch_assumptions ba gl) gl
