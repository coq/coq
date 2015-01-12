(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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
open Context
open Declarations
open Tacmach
open Clenv
open Misctypes

(************************************************************************)
(* Tacticals re-exported from the Refiner module                        *)
(************************************************************************)

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
  fst (List.split_when (fun (hyp,_,_) -> Id.equal hyp id) (pf_hyps gl))

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
  ity        : pinductive;   (* the type we were eliminating on *)
  largs      : constr list; (* its arguments *)
  branchnum  : int;         (* the branch number *)
  pred       : constr;      (* the predicate we used *)
  nassums    : int;         (* the number of assumptions to be introduced *)
  branchsign : bool list;   (* the signature of the branch.
                               true=recursive argument, false=constant *)
  branchnames : Tacexpr.intro_patterns}

type branch_assumptions = {
  ba        : branch_args;     (* the branch args *)
  assums    : named_context}   (* the list of assumptions introduced *)

let fix_empty_or_and_pattern nv l =
  (* 1- The syntax does not distinguish between "[ ]" for one clause with no
     names and "[ ]" for no clause at all *)
  (* 2- More generally, we admit "[ ]" for any disjunctive pattern of
     arbitrary length *)
  match l with
  | [[]] -> List.make nv []
  | _ -> l

let check_or_and_pattern_size loc names n =
  if not (Int.equal (List.length names) n) then
    if Int.equal n 1 then
      user_err_loc (loc,"",str "Expects a conjunctive pattern.")
    else
      user_err_loc (loc,"",str "Expects a disjunctive pattern with " ++ int n
	++ str " branches.")

let compute_induction_names n = function
  | None ->
      Array.make n []
  | Some (loc,names) ->
      let names = fix_empty_or_and_pattern n names in
      check_or_and_pattern_size loc names n;
      Array.of_list names

let compute_construtor_signatures isrec ((_,k as ity),u) =
  let rec analrec c recargs =
    match kind_of_term c, recargs with
    | Prod (_,_,c), recarg::rest ->
	let b = match Declareops.dest_recarg recarg with
	  | Norec | Imbr _  -> false
	  | Mrec (_,j)  -> isrec && Int.equal j k
	in b :: (analrec c rest)
    | LetIn (_,_,_,c), rest -> false :: (analrec c rest)
    | _, [] -> []
    | _ -> anomaly (Pp.str "compute_construtor_signatures")
  in
  let (mib,mip) = Global.lookup_inductive ity in
  let n = mib.mind_nparams in
  let lc =
    Array.map (fun c -> snd (decompose_prod_n_assum n c)) mip.mind_nf_lc in
  let lrecargs = Declareops.dest_subterms mip.mind_recargs in
  Array.map2 analrec lc lrecargs

let elimination_sort_of_goal gl =
  pf_apply Retyping.get_sort_family_of gl (pf_concl gl)

let elimination_sort_of_hyp id gl =
  pf_apply Retyping.get_sort_family_of gl (pf_get_hyp_typ gl id)

let elimination_sort_of_clause = function
  | None -> elimination_sort_of_goal
  | Some id -> elimination_sort_of_hyp id


let pf_with_evars glsev k gls = 
  let evd, a = glsev gls in
    tclTHEN (Refiner.tclEVARS evd) (k a) gls

let pf_constr_of_global gr k =
  pf_with_evars (fun gls -> pf_apply Evd.fresh_global gls gr) k

(* computing the case/elim combinators *)

let gl_make_elim ind gl =
  let gr = Indrec.lookup_eliminator (fst ind) (elimination_sort_of_goal gl) in
    pf_apply Evd.fresh_global gl gr

let gl_make_case_dep ind gl =
  pf_apply Indrec.build_case_analysis_scheme gl ind true
    (elimination_sort_of_goal gl)

let gl_make_case_nodep ind gl =
  pf_apply Indrec.build_case_analysis_scheme gl ind false
    (elimination_sort_of_goal gl)

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
      | (_, _) -> anomaly (Pp.str "make_elim_branch_assumptions")
  in
  makerec ([],[],[],[],[]) ba.branchsign
    (try List.firstn ba.nassums (pf_hyps gl)
     with Failure _ -> anomaly (Pp.str "make_elim_branch_assumptions"))

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
      | (_, _) -> anomaly (Pp.str "make_case_branch_assumptions")
  in
  makerec ([],[],[],[]) ba.branchsign
    (try List.firstn ba.nassums (pf_hyps gl)
     with Failure _ -> anomaly (Pp.str "make_case_branch_assumptions"))

let case_on_ba tac ba gl = tac (make_case_branch_assumptions ba gl) gl


(** Tacticals of Ltac defined directly in term of Proofview *)
module New = struct
  open Proofview
  open Proofview.Notations
  open Tacmach.New

  let tclIDTAC = tclUNIT ()

  let tclTHEN t1 t2 =
    t1 <*> t2

  let tclFAIL lvl msg =
    tclZERO (Refiner.FailError (lvl,lazy msg))

  let tclZEROMSG ?loc msg =
    let err = UserError ("", msg) in
    let info = match loc with
    | None -> Exninfo.null
    | Some loc -> Loc.add_loc Exninfo.null loc
    in
    tclZERO ~info err

  let catch_failerror e =
    try
      Refiner.catch_failerror e;
      tclUNIT ()
    with e -> tclZERO e

  (* spiwack: I chose to give the Ltac + the same semantics as
     [Proofview.tclOR], however, for consistency with the or-else
     tactical, we may consider wrapping the first argument with
     [tclPROGRESS]. It strikes me as a bad idea, but consistency can be
     considered valuable. *)
  let tclOR t1 t2 =
    tclINDEPENDENT begin
      Proofview.tclOR
        t1
        begin fun e ->
          catch_failerror e <*> t2
        end
    end

  let tclORD t1 t2 =
    tclINDEPENDENT begin
      Proofview.tclOR
        t1
        begin fun e ->
          catch_failerror e <*> t2 ()
        end
    end

  let tclONCE = Proofview.tclONCE

  let tclEXACTLY_ONCE t = Proofview.tclEXACTLY_ONCE (Refiner.FailError(0,lazy (assert false))) t

  let tclIFCATCH t tt te =
    tclINDEPENDENT begin
      Proofview.tclIFCATCH t
        tt
        (fun e -> catch_failerror e <*> te ())
    end

  let tclORELSE0 t1 t2 =
    tclINDEPENDENT begin
      tclORELSE
        t1
        begin fun e ->
          catch_failerror e <*> t2
        end
    end
  let tclORELSE t1 t2 =
    tclORELSE0 (tclPROGRESS t1) t2

  let tclTHENS3PARTS t1 l1 repeat l2 =
    tclINDEPENDENT begin
      t1 <*>
        Proofview.tclORELSE (* converts the [SizeMismatch] error into an ltac error *)
          begin tclEXTEND (Array.to_list l1) repeat (Array.to_list l2) end
          begin function (e, info) -> match e with
            | SizeMismatch (i,_)->
                let errmsg =
                  str"Incorrect number of goals" ++ spc() ++
                  str"(expected "++int i++str(String.plural i " tactic") ++ str")"
                in
                tclFAIL 0 errmsg
            | reraise -> tclZERO ~info reraise
          end
    end
  let tclTHENSFIRSTn t1 l repeat =
    tclTHENS3PARTS t1 l repeat [||]
  let tclTHENFIRSTn t1 l =
    tclTHENSFIRSTn t1 l (tclUNIT())
  let tclTHENFIRST t1 t2 =
    tclTHENFIRSTn t1 [|t2|]
  let tclTHENLASTn t1 l =
    tclTHENS3PARTS t1 [||] (tclUNIT()) l
  let tclTHENLAST t1 t2 = tclTHENLASTn t1 [|t2|]
  let tclTHENS t l =
    tclINDEPENDENT begin
      t <*>Proofview.tclORELSE (* converts the [SizeMismatch] error into an ltac error *)
          begin tclDISPATCH l end
          begin function (e, info) -> match e with
            | SizeMismatch (i,_)->
                let errmsg =
                  str"Incorrect number of goals" ++ spc() ++
                  str"(expected "++int i++str(String.plural i " tactic") ++ str")"
                in
                tclFAIL 0 errmsg
            | reraise -> tclZERO ~info reraise
          end
    end
  let tclTHENLIST l =
    List.fold_left tclTHEN (tclUNIT()) l


  (* [tclMAP f [x1..xn]] builds [(f x1);(f x2);...(f xn)] *)
  let tclMAP tacfun l =
    List.fold_right (fun x -> (tclTHEN (tacfun x))) l (tclUNIT())

  let tclTRY t =
    tclORELSE0 t (tclUNIT ())

  let tclIFTHENELSE t1 t2 t3 =
    tclINDEPENDENT begin
      Proofview.tclIFCATCH t1
        (fun () -> t2)
        (fun (e, info) -> Proofview.tclORELSE t3 (fun e' -> tclZERO ~info e))
    end
  let tclIFTHENSVELSE t1 a t3 =
    Proofview.tclIFCATCH t1
      (fun () -> tclDISPATCH (Array.to_list a))
      (fun _ -> t3)
  let tclIFTHENTRYELSEMUST t1 t2 =
    tclIFTHENELSE t1 (tclTRY t2) t2

  (* Try the first tactic that does not fail in a list of tactics *)
  let rec tclFIRST = function
    | [] -> tclZERO (Errors.UserError ("Tacticals.New.tclFIRST",str"No applicable tactic."))
    |  t::rest -> tclORELSE0 t (tclFIRST rest)

  let rec tclFIRST_PROGRESS_ON tac = function
    | []    -> tclFAIL 0 (str "No applicable tactic")
    | [a]   -> tac a (* so that returned failure is the one from last item *)
    | a::tl -> tclORELSE (tac a) (tclFIRST_PROGRESS_ON tac tl)

  let rec tclDO n t =
    if n < 0 then
      tclZERO (Errors.UserError (
        "Refiner.tclDO",
        str"Wrong argument : Do needs a positive integer.")
      )
    else if n = 0 then tclUNIT ()
    else if n = 1 then t
    else tclTHEN t (tclDO (n-1) t)

  let rec tclREPEAT0 t =
    tclINDEPENDENT begin
      Proofview.tclIFCATCH t
        (fun () -> tclCHECKINTERRUPT <*> tclREPEAT0 t)
        (fun e -> catch_failerror e <*> tclUNIT ())
    end
  let tclREPEAT t =
    tclREPEAT0 (tclPROGRESS t)
  let rec tclREPEAT_MAIN0 t =
    Proofview.tclIFCATCH t
      (fun () -> tclTRYFOCUS 1 1 (tclREPEAT_MAIN0 t))
      (fun e -> catch_failerror e <*> tclUNIT ())
  let tclREPEAT_MAIN t =
    tclREPEAT_MAIN0 (tclPROGRESS t)

  let tclCOMPLETE t =
    t >>= fun res ->
      (tclINDEPENDENT
         (tclZERO (Errors.UserError ("",str"Proof is not complete.")))
      ) <*>
        tclUNIT res

  (* Try the first thats solves the current goal *)
  let tclSOLVE tacl = tclFIRST (List.map tclCOMPLETE tacl)

  let tclPROGRESS t =
    Proofview.tclINDEPENDENT (Proofview.tclPROGRESS t)

  (* Check that holes in arguments have been resolved *)

  let check_evars env sigma extsigma origsigma =
    let rec is_undefined_up_to_restriction sigma evk =
      let evi = Evd.find sigma evk in
      match Evd.evar_body evi with
      | Evd.Evar_empty -> Some (evk,evi)
      | Evd.Evar_defined c -> match Term.kind_of_term c with
        | Term.Evar (evk,l) -> is_undefined_up_to_restriction sigma evk
        | _ -> 
          (* We make the assumption that there is no way to refine an
            evar remaining after typing from the initial term given to
            apply/elim and co tactics, is it correct? *)
          None in
    let rest =
      Evd.fold_undefined (fun evk evi acc ->
        match is_undefined_up_to_restriction sigma evk with
        | Some (evk',evi) when not (Evd.mem origsigma evk) -> (evk',evi)::acc
        | _ -> acc)
        extsigma []
    in
    match rest with
    | [] -> ()
    | (evk,evi) :: _ ->
      let (loc,_) = evi.Evd.evar_source in
      Pretype_errors.error_unsolvable_implicit loc env sigma evk None

  let tclWITHHOLES accept_unresolved_holes tac sigma x =
    tclEVARMAP >>= fun sigma_initial ->
      if sigma == sigma_initial then tac x
      else
        let check_evars env new_sigma sigma initial_sigma =
          try
            check_evars env new_sigma sigma initial_sigma;
            tclUNIT ()
          with e when Errors.noncritical e ->
            tclZERO e
        in
        let check_evars_if =
          if not accept_unresolved_holes then
            tclEVARMAP >>= fun sigma_final ->
              tclENV >>= fun env ->
                check_evars env sigma_final sigma sigma_initial
          else
            tclUNIT ()
        in
        Proofview.Unsafe.tclEVARS sigma <*> tac x <*> check_evars_if

  let tclTIMEOUT n t =
    Proofview.tclOR
      (Proofview.tclTIMEOUT n t)
      begin function (e, info) -> match e with
        | Proofview.Timeout as e -> Proofview.tclZERO (Refiner.FailError (0,lazy (Errors.print e)))
        | e -> Proofview.tclZERO ~info e
      end

  let tclTIME s t =
    Proofview.tclTIME s t

  let nthDecl m gl =
    let hyps = Proofview.Goal.hyps gl in
    try
      List.nth hyps (m-1)
    with Failure _ -> Errors.error "No such assumption."

  let nLastDecls gl n =
    try List.firstn n (Proofview.Goal.hyps gl)
    with Failure _ -> error "Not enough hypotheses in the goal."

  let nthHypId m gl =
    (** We only use [id] *)
    let gl = Proofview.Goal.assume gl in
    let (id,_,_) = nthDecl m gl in
    id
  let nthHyp m gl = 
    mkVar (nthHypId m gl)

  let onNthHypId m tac =
    Proofview.Goal.enter begin fun gl -> tac (nthHypId m gl) end
  let onNthHyp m tac =
    Proofview.Goal.enter begin fun gl -> tac (nthHyp m gl) end

  let onLastHypId = onNthHypId 1
  let onLastHyp   = onNthHyp 1

  let onNthDecl m tac =
    Proofview.Goal.nf_enter begin fun gl ->
      Proofview.tclUNIT (nthDecl m gl) >>= tac
    end
  let onLastDecl  = onNthDecl 1

  let ifOnHyp pred tac1 tac2 id =
    Proofview.Goal.nf_enter begin fun gl ->
    let typ = Tacmach.New.pf_get_hyp_typ id gl in
    if pred (id,typ) then
      tac1 id
    else
      tac2 id
    end

  let onHyps find tac = Proofview.Goal.nf_enter (fun gl -> tac (find gl))

  let afterHyp id tac =
    Proofview.Goal.nf_enter begin fun gl ->
    let hyps = Proofview.Goal.hyps gl in
    let rem, _ = List.split_when (fun (hyp,_,_) -> Id.equal hyp id) hyps in
    tac rem
    end

  let fullGoal gl =
    let hyps = Tacmach.New.pf_ids_of_hyps gl in
    None :: List.map Option.make hyps

  let tryAllHyps tac =
    Proofview.Goal.enter begin fun gl ->
    let hyps = Tacmach.New.pf_ids_of_hyps gl in
    tclFIRST_PROGRESS_ON tac hyps
    end
  let tryAllHypsAndConcl tac =
    Proofview.Goal.enter begin fun gl ->
      tclFIRST_PROGRESS_ON tac (fullGoal gl)
    end

  let onClause tac cl =
    Proofview.Goal.enter begin fun gl ->
    let hyps = Tacmach.New.pf_ids_of_hyps gl in
    tclMAP tac (Locusops.simple_clause_of (fun () -> hyps) cl)
    end

  (* Find the right elimination suffix corresponding to the sort of the goal *)
  (* c should be of type A1->.. An->B with B an inductive definition *)
  let general_elim_then_using mk_elim
      isrec allnames tac predicate ind (c, t) =
    Proofview.Goal.nf_enter begin fun gl ->
    let indclause = Tacmach.New.of_old (fun gl -> mk_clenv_from gl (c, t)) gl in
    (** FIXME: evar leak. *)
    let sigma, elim = Tacmach.New.of_old (mk_elim ind) gl in
    (* applying elimination_scheme just a little modified *)
    let elimclause = Tacmach.New.of_old (fun gls -> mk_clenv_from gls (elim,Tacmach.New.pf_type_of gl elim)) gl in
    let indmv =
      match kind_of_term (last_arg elimclause.templval.Evd.rebus) with
      | Meta mv -> mv
      | _         -> anomaly (str"elimination")
    in
    let pmv =
      let p, _ = decompose_app elimclause.templtyp.Evd.rebus in
      match kind_of_term p with
      | Meta p -> p
      | _ ->
	  let name_elim =
	    match kind_of_term elim with
	    | Const (kn, _) -> string_of_con kn
	    | Var id -> string_of_id id
	    | _ -> "\b"
	  in
	  error ("The elimination combinator " ^ name_elim ^ " is unknown.")
    in
    let elimclause' = clenv_fchain indmv elimclause indclause in
    let branchsigns = compute_construtor_signatures isrec ind in
    let brnames = compute_induction_names (Array.length branchsigns) allnames in
    let flags = Unification.elim_flags () in
    let elimclause' =
      match predicate with
      | None   -> elimclause'
      | Some p -> clenv_unify ~flags Reduction.CONV (mkMeta pmv) p elimclause'
    in
    let clenv' = Tacmach.New.of_old (clenv_unique_resolver ~flags elimclause') gl in
    let after_tac i =
      let (hd,largs) = decompose_app clenv'.templtyp.Evd.rebus in
      let ba = { branchsign = branchsigns.(i);
                 branchnames = brnames.(i);
                 nassums =
          List.fold_left
            (fun acc b -> if b then acc+2 else acc+1)
            0 branchsigns.(i);
                 branchnum = i+1;
                 ity = ind;
                 largs = List.map (clenv_nf_meta clenv') largs;
                 pred = clenv_nf_meta clenv' hd }
      in
      tac ba
    in
    let branchtacs = List.init (Array.length branchsigns) after_tac in
    Proofview.tclTHEN
      (Clenvtac.clenv_refine false clenv')
      (Proofview.tclEXTEND [] tclIDTAC branchtacs)
    end

  let elimination_then tac c =
    Proofview.Goal.nf_enter begin fun gl ->
    let (ind,t) = pf_reduce_to_quantified_ind gl (pf_type_of gl c) in
    let isrec,mkelim =
      match (Global.lookup_mind (fst (fst ind))).mind_record with
      | None -> true,gl_make_elim
      | Some _ -> false,gl_make_case_dep
    in
    general_elim_then_using mkelim isrec None tac None ind (c, t)
    end

  let case_then_using =
    general_elim_then_using gl_make_case_dep false

  let case_nodep_then_using =
    general_elim_then_using gl_make_case_nodep false

  let elim_on_ba tac ba =
    Proofview.Goal.nf_enter begin fun gl ->
    let branches = Tacmach.New.of_old (make_elim_branch_assumptions ba) gl in
    tac branches
    end

  let case_on_ba tac ba = 
    Proofview.Goal.nf_enter begin fun gl ->
    let branches = Tacmach.New.of_old (make_case_branch_assumptions ba) gl in
    tac branches
    end

  let elimination_sort_of_goal gl =
    (** Retyping will expand evars anyway. *)
    let c = Proofview.Goal.concl (Goal.assume gl) in
    pf_apply Retyping.get_sort_family_of gl c

  let elimination_sort_of_hyp id gl =
    (** Retyping will expand evars anyway. *)
    let c = pf_get_hyp_typ id (Goal.assume gl) in
    pf_apply Retyping.get_sort_family_of gl c

  let elimination_sort_of_clause id gl = match id with
  | None -> elimination_sort_of_goal gl
  | Some id -> elimination_sort_of_hyp id gl

  let pf_constr_of_global ref tac =
    Proofview.Goal.nf_enter begin fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      let (sigma, c) = Evd.fresh_global env sigma ref in
      Proofview.Unsafe.tclEVARS sigma <*> (tac c)
    end

end
