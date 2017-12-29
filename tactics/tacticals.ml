(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names
open Constr
open EConstr
open Termops
open Declarations
open Tacmach
open Clenv
open Tactypes

module NamedDecl = Context.Named.Declaration

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
let tclPROGRESS      = Refiner.tclPROGRESS
let tclSHOWHYPS      = Refiner.tclSHOWHYPS
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
  with Failure _ -> user_err Pp.(str "No such assumption.")

let nthHypId m gl = nthDecl m gl |> NamedDecl.get_id
let nthHyp m gl   = mkVar (nthHypId m gl)

let lastDecl gl   = nthDecl 1 gl
let lastHypId gl  = nthHypId 1 gl
let lastHyp gl    = nthHyp 1 gl

let nLastDecls n gl =
  try List.firstn n (pf_hyps gl)
  with Failure _ -> user_err Pp.(str "Not enough hypotheses in the goal.")

let nLastHypsId n gl = List.map (NamedDecl.get_id) (nLastDecls n gl)
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
  fst (List.split_when (NamedDecl.get_id %> Id.equal id) (pf_hyps gl))

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
  nassums    : int;         (* number of assumptions/letin to be introduced *)
  branchsign : bool list;   (* the signature of the branch.
                               true=assumption, false=let-in *)
  branchnames : intro_patterns}

type branch_assumptions = {
  ba        : branch_args;       (* the branch args *)
  assums    : named_context}   (* the list of assumptions introduced *)

let fix_empty_or_and_pattern nv l =
  (* 1- The syntax does not distinguish between "[ ]" for one clause with no
     names and "[ ]" for no clause at all *)
  (* 2- More generally, we admit "[ ]" for any disjunctive pattern of
     arbitrary length *)
  match l with
  | IntroOrPattern [[]] -> IntroOrPattern (List.make nv [])
  | _ -> l

let check_or_and_pattern_size ?loc check_and names branchsigns =
  let n = Array.length branchsigns in
  let msg p1 p2 = strbrk "a conjunctive pattern made of " ++ int p1 ++ (if p1 == p2 then mt () else str " or " ++ int p2) ++ str " patterns" in
  let err1 p1 p2 =
    user_err ?loc  (str "Expects " ++ msg p1 p2 ++ str ".") in
  let errn n =
    user_err ?loc  (str "Expects a disjunctive pattern with " ++ int n
	++ str " branches.") in
  let err1' p1 p2 =
    user_err ?loc  (strbrk "Expects a disjunctive pattern with 1 branch or " ++ msg p1 p2 ++ str ".") in
  let errforthcoming ?loc =
    user_err ?loc  (strbrk "Unexpected non atomic pattern.") in
  match names with
  | IntroAndPattern l ->
      if not (Int.equal n 1) then errn n;
      let l' = List.filter CAst.(function {v=IntroForthcoming _} -> true | {v=IntroNaming _} | {v=IntroAction _} -> false) l in
      if l' != [] then errforthcoming ?loc:(List.hd l').CAst.loc;
      if check_and then
        let p1 = List.count (fun x -> x) branchsigns.(0) in
        let p2 = List.length branchsigns.(0) in
        let p = List.length l in
        if not (Int.equal p p1 || Int.equal p p2) then err1 p1 p2;
        if Int.equal p p1 then
          IntroAndPattern
            (List.extend branchsigns.(0) (CAst.make @@ IntroNaming Namegen.IntroAnonymous) l)
        else
          names
      else
        names
  | IntroOrPattern ll ->
      if not (Int.equal n (List.length ll)) then
        if Int.equal n 1 then
          let p1 = List.count (fun x -> x) branchsigns.(0) in
          let p2 = List.length branchsigns.(0) in
          err1' p1 p2 else errn n;
      names

let get_and_check_or_and_pattern_gen ?loc check_and names branchsigns =
  let names = check_or_and_pattern_size ?loc check_and names branchsigns in
  match names with
  | IntroAndPattern l -> [|l|]
  | IntroOrPattern l -> Array.of_list l

let get_and_check_or_and_pattern ?loc = get_and_check_or_and_pattern_gen ?loc true

let compute_induction_names_gen check_and branchletsigns = function
  | None ->
      Array.make (Array.length branchletsigns) []
  | Some {CAst.loc;v=names} ->
      let names = fix_empty_or_and_pattern (Array.length branchletsigns) names in
      get_and_check_or_and_pattern_gen check_and ?loc names branchletsigns

let compute_induction_names = compute_induction_names_gen true

(* Compute the let-in signature of case analysis or standard induction scheme *)
let compute_constructor_signatures ~rec_flag ((_,k as ity),u) =
  let rec analrec c recargs =
    match Constr.kind c, recargs with
    | Prod (_,_,c), recarg::rest ->
        let rest = analrec c rest in
        begin match Declareops.dest_recarg recarg with
        | Norec | Imbr _  -> true :: rest
        | Mrec (_,j)  ->
            if rec_flag && Int.equal j k then true :: true :: rest
            else true :: rest
        end
    | LetIn (_,_,_,c), rest -> false :: analrec c rest
    | _, [] -> []
    | _ -> anomaly (Pp.str "compute_constructor_signatures.")
  in
  let (mib,mip) = Global.lookup_inductive ity in
  let n = mib.mind_nparams in
  let lc =
    Array.map (fun c -> snd (Term.decompose_prod_n_assum n c)) mip.mind_nf_lc in
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
    let err = UserError (None, msg) in
    let info = match loc with
    | None -> Exninfo.null
    | Some loc -> Loc.add_loc Exninfo.null loc
    in
    tclZERO ~info err

  let catch_failerror e =
    try
      Refiner.catch_failerror e;
      tclUNIT ()
    with e when CErrors.noncritical e -> tclZERO e

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

  let tclORELSE0L t1 t2 =
    tclINDEPENDENTL begin
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

  let tclBINDFIRST t1 t2 =
    t1 >>= fun ans ->
    Proofview.Unsafe.tclGETGOALS >>= fun gls ->
    match gls with
    | [] -> tclFAIL 0 (str "Expect at least one goal.")
    | hd::tl ->
    Proofview.Unsafe.tclSETGOALS [hd] <*> t2 ans >>= fun ans ->
    Proofview.Unsafe.tclNEWGOALS tl <*>
    Proofview.tclUNIT ans

  let tclTHENLASTn t1 l =
    tclTHENS3PARTS t1 [||] (tclUNIT()) l
  let tclTHENLAST t1 t2 = tclTHENLASTn t1 [|t2|]

  let option_of_failure f x = try Some (f x) with Failure _ -> None

  let tclBINDLAST t1 t2 =
    t1 >>= fun ans ->
    Proofview.Unsafe.tclGETGOALS >>= fun gls ->
    match option_of_failure List.sep_last gls with
    | None -> tclFAIL 0 (str "Expect at least one goal.")
    | Some (last,firstn) ->
    Proofview.Unsafe.tclSETGOALS [last] <*> t2 ans >>= fun ans ->
    Proofview.Unsafe.tclGETGOALS >>= fun newgls ->
    tclEVARMAP >>= fun sigma ->
    let firstn = Proofview.Unsafe.undefined sigma firstn in
    Proofview.Unsafe.tclSETGOALS (firstn@newgls) <*>
    Proofview.tclUNIT ans

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
  
  let tclTRYb t =
    tclORELSE0L (t <*> tclUNIT true) (tclUNIT false)

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
  let tclIFTHENFIRSTELSE t1 t2 t3 =
    Proofview.tclIFCATCH t1
      (fun () -> tclEXTEND [t2] (tclUNIT ()) [])
      (fun _ -> t3)
  let tclIFTHENTRYELSEMUST t1 t2 =
    tclIFTHENELSE t1 (tclTRY t2) t2
  let tclIFTHENFIRSTTRYELSEMUST t1 t2 =
    tclIFTHENFIRSTELSE t1 (tclTRY t2) t2

  (* Try the first tactic that does not fail in a list of tactics *)
  let rec tclFIRST = function
    | [] -> tclZEROMSG (str"No applicable tactic.")
    |  t::rest -> tclORELSE0 t (tclFIRST rest)

  let rec tclFIRST_PROGRESS_ON tac = function
    | []    -> tclFAIL 0 (str "No applicable tactic")
    | [a]   -> tac a (* so that returned failure is the one from last item *)
    | a::tl -> tclORELSE (tac a) (tclFIRST_PROGRESS_ON tac tl)

  let rec tclDO n t =
    if n < 0 then
      tclZEROMSG (str"Wrong argument : Do needs a positive integer.")
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
         (tclZEROMSG (str"Proof is not complete."))
      ) <*>
        tclUNIT res

  (* Try the first thats solves the current goal *)
  let tclSOLVE tacl = tclFIRST (List.map tclCOMPLETE tacl)

  let tclPROGRESS t =
    Proofview.tclINDEPENDENT (Proofview.tclPROGRESS t)

  (* Select a subset of the goals *)
  let tclSELECT = let open Goal_select in function
    | SelectNth i -> Proofview.tclFOCUS i i
    | SelectList l -> Proofview.tclFOCUSLIST l
    | SelectId id -> Proofview.tclFOCUSID id
    | SelectAll -> anomaly ~label:"tclSELECT" Pp.(str "SelectAll not allowed here")
    | SelectAlreadyFocused ->
      anomaly ~label:"tclSELECT" Pp.(str "SelectAlreadyFocused not allowed here")

  (* Check that holes in arguments have been resolved *)

  let check_evars env sigma extsigma origsigma =
    let rec is_undefined_up_to_restriction sigma evk =
      if Evd.mem origsigma evk then None else
      let evi = Evd.find sigma evk in
      match Evd.evar_body evi with
      | Evd.Evar_empty -> Some (evk,evi)
      | Evd.Evar_defined c -> match Constr.kind (EConstr.Unsafe.to_constr c) with
        | Evar (evk,l) -> is_undefined_up_to_restriction sigma evk
        | _ -> 
          (* We make the assumption that there is no way to refine an
            evar remaining after typing from the initial term given to
            apply/elim and co tactics, is it correct? *)
          None in
    let rest =
      Evd.fold_undefined (fun evk evi acc ->
        match is_undefined_up_to_restriction sigma evk with
        | Some (evk',evi) -> (evk',evi)::acc
        | _ -> acc)
        extsigma []
    in
    match rest with
    | [] -> ()
    | (evk,evi) :: _ ->
      let (loc,_) = evi.Evd.evar_source in
      Pretype_errors.error_unsolvable_implicit ?loc env sigma evk None

  let tclWITHHOLES accept_unresolved_holes tac sigma =
    tclEVARMAP >>= fun sigma_initial ->
      if sigma == sigma_initial then tac
      else
        let check_evars_if x =
          if not accept_unresolved_holes then
            tclEVARMAP >>= fun sigma_final ->
              tclENV >>= fun env ->
                try
                  let () = check_evars env sigma_final sigma sigma_initial in
                  tclUNIT x
                with e when CErrors.noncritical e ->
                  tclZERO e
          else
            tclUNIT x
        in
        Proofview.Unsafe.tclEVARS sigma <*> tac >>= check_evars_if

  let tclDELAYEDWITHHOLES check x tac =
    Proofview.Goal.enter begin fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      let (sigma, x) = x env sigma in
      tclWITHHOLES check (tac x) sigma
    end

  let tclTIMEOUT n t =
    Proofview.tclOR
      (Proofview.tclTIMEOUT n t)
      begin function (e, info) -> match e with
        | Proofview.Timeout as e -> Proofview.tclZERO (Refiner.FailError (0,lazy (CErrors.print e)))
        | e -> Proofview.tclZERO ~info e
      end

  let tclTIME s t =
    Proofview.tclTIME s t

  let nthDecl m gl =
    let hyps = Proofview.Goal.hyps gl in
    try
      List.nth hyps (m-1)
    with Failure _ -> CErrors.user_err Pp.(str "No such assumption.")

  let nLastDecls gl n =
    try List.firstn n (Proofview.Goal.hyps gl)
    with Failure _ -> CErrors.user_err Pp.(str "Not enough hypotheses in the goal.")

  let nthHypId m gl =
    (** We only use [id] *)
    nthDecl m gl |> NamedDecl.get_id
  let nthHyp m gl = 
    mkVar (nthHypId m gl)

  let onNthHypId m tac =
    Proofview.Goal.enter begin fun gl -> tac (nthHypId m gl) end 
  let onNthHyp m tac =
    Proofview.Goal.enter begin fun gl -> tac (nthHyp m gl) end

  let onLastHypId = onNthHypId 1
  let onLastHyp   = onNthHyp 1

  let onNthDecl m tac =
    Proofview.Goal.enter begin fun gl ->
      Proofview.tclUNIT (nthDecl m gl) >>= tac
    end
  let onLastDecl  = onNthDecl 1

  let ifOnHyp pred tac1 tac2 id =
    Proofview.Goal.enter begin fun gl ->
    let typ = Tacmach.New.pf_get_hyp_typ id gl in
    if pred (id,typ) then
      tac1 id
    else
      tac2 id
    end

  let onHyps find tac = Proofview.Goal.enter begin fun gl -> tac (find gl) end

  let afterHyp id tac =
    Proofview.Goal.enter begin fun gl ->
    let hyps = Proofview.Goal.hyps gl in
    let rem, _ = List.split_when (NamedDecl.get_id %> Id.equal id) hyps in
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
      rec_flag allnames tac predicate ind (c, t) =
    Proofview.Goal.enter begin fun gl ->
    let sigma, elim = mk_elim ind gl in
    let ind = on_snd (fun u -> EInstance.kind sigma u) ind in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
    (Proofview.Goal.enter begin fun gl ->
    let indclause = mk_clenv_from gl (c, t) in
    (* applying elimination_scheme just a little modified *)
    let elimclause = mk_clenv_from gl (elim,Tacmach.New.pf_unsafe_type_of gl elim)  in
    let indmv =
      match EConstr.kind elimclause.evd (last_arg elimclause.evd elimclause.templval.Evd.rebus) with
      | Meta mv -> mv
      | _         -> anomaly (str"elimination.")
    in
    let pmv =
      let p, _ = decompose_app elimclause.evd elimclause.templtyp.Evd.rebus in
      match EConstr.kind elimclause.evd p with
      | Meta p -> p
      | _ ->
	  let name_elim =
	    match EConstr.kind sigma elim with
            | Const _ | Var _ -> str " " ++ Printer.pr_econstr_env (pf_env gl) sigma elim
            | _ -> mt ()
	  in
	  user_err ~hdr:"Tacticals.general_elim_then_using"
            (str "The elimination combinator " ++ name_elim ++ str " is unknown.")
    in
    let elimclause' = clenv_fchain ~with_univs:false indmv elimclause indclause in
    let branchsigns = compute_constructor_signatures ~rec_flag ind in
    let brnames = compute_induction_names_gen false branchsigns allnames in
    let flags = Unification.elim_flags () in
    let elimclause' =
      match predicate with
      | None   -> elimclause'
      | Some p -> clenv_unify ~flags Reduction.CONV (mkMeta pmv) p elimclause'
    in
    let clenv' = clenv_unique_resolver ~flags elimclause' gl in
    let after_tac i =
      let (hd,largs) = decompose_app clenv'.evd clenv'.templtyp.Evd.rebus in
      let ba = { branchsign = branchsigns.(i);
                 branchnames = brnames.(i);
                 nassums = List.length branchsigns.(i);
                 branchnum = i+1;
                 ity = ind;
                 largs = List.map (clenv_nf_meta clenv') largs;
                 pred = clenv_nf_meta clenv' hd }
      in
      tac ba
    in
    let branchtacs = List.init (Array.length branchsigns) after_tac in
    Proofview.tclTHEN
      (Clenvtac.clenv_refine clenv')
      (Proofview.tclEXTEND [] tclIDTAC branchtacs)
    end) end

  let elimination_sort_of_goal gl =
    (** Retyping will expand evars anyway. *)
    let c = Proofview.Goal.concl gl in
    pf_apply Retyping.get_sort_family_of gl c

  let elimination_sort_of_hyp id gl =
    (** Retyping will expand evars anyway. *)
    let c = pf_get_hyp_typ id gl in
    pf_apply Retyping.get_sort_family_of gl c

  let elimination_sort_of_clause id gl = match id with
  | None -> elimination_sort_of_goal gl
  | Some id -> elimination_sort_of_hyp id gl

  (* computing the case/elim combinators *)

  let gl_make_elim ind = begin fun gl ->
    let gr = Indrec.lookup_eliminator (fst ind) (elimination_sort_of_goal gl) in
    let (sigma, c) = pf_apply Evd.fresh_global gl gr in
    (sigma, c)
  end

  let gl_make_case_dep (ind, u) = begin fun gl ->
    let sigma = project gl in
    let u = EInstance.kind (project gl) u in
    let (sigma, r) = Indrec.build_case_analysis_scheme (pf_env gl) sigma (ind, u) true
      (elimination_sort_of_goal gl)
    in
    (sigma, EConstr.of_constr r)
  end

  let gl_make_case_nodep (ind, u) = begin fun gl ->
    let sigma = project gl in
    let u = EInstance.kind sigma u in
    let (sigma, r) = Indrec.build_case_analysis_scheme (pf_env gl) sigma (ind, u) false
      (elimination_sort_of_goal gl)
    in
    (sigma, EConstr.of_constr r)
  end

  let make_elim_branch_assumptions ba hyps =
    let assums =
      try List.rev (List.firstn ba.nassums hyps)
      with Failure _ -> anomaly (Pp.str "make_elim_branch_assumptions.") in
    { ba = ba; assums = assums }

  let elim_on_ba tac ba =
    Proofview.Goal.enter begin fun gl ->
    let branches = make_elim_branch_assumptions ba (Proofview.Goal.hyps gl) in
    tac branches
    end

  let case_on_ba tac ba = 
    Proofview.Goal.enter begin fun gl ->
    let branches = make_elim_branch_assumptions ba (Proofview.Goal.hyps gl) in
    tac branches
    end

  let elimination_then tac c =
    Proofview.Goal.enter begin fun gl ->
    let (ind,t) = pf_reduce_to_quantified_ind gl (pf_unsafe_type_of gl c) in
    let isrec,mkelim =
      match (Global.lookup_mind (fst (fst ind))).mind_record with
      | NotRecord -> true,gl_make_elim
      | FakeRecord | PrimRecord _ -> false,gl_make_case_dep
    in
    general_elim_then_using mkelim isrec None tac None ind (c, t)
    end

  let case_then_using =
    general_elim_then_using gl_make_case_dep false

  let case_nodep_then_using =
    general_elim_then_using gl_make_case_nodep false

  let pf_constr_of_global ref =
    Proofview.tclEVARMAP >>= fun sigma ->
    Proofview.tclENV >>= fun env ->
    let (sigma, c) = Evd.fresh_global env sigma ref in
    Proofview.Unsafe.tclEVARS sigma <*> Proofview.tclUNIT c

end
