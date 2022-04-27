(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
open Declarations
open Tactypes

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

(*********************)
(*   Tacticals       *)
(*********************)

open Evd

exception FailError of int * Pp.t Lazy.t

let catch_failerror (e, info) =
  match e with
  | FailError (lvl,s) when lvl > 0 ->
    Exninfo.iraise (FailError (lvl - 1, s), info)
  | e -> Control.check_for_interrupt ()

module Old =
struct

[@@@ocaml.warning "-3"]
open Tacmach.Old
type tactic = Proofview.V82.tac
[@@@ocaml.warning "+3"]

let catch_failerror = catch_failerror

let unpackage glsig = (ref (glsig.sigma)), glsig.it

let repackage r v = {it = v; sigma = !r; }

let apply_sig_tac r tac g =
  Control.check_for_interrupt (); (* Breakpoint *)
  let glsigma = tac (repackage r g) in
  r := glsigma.sigma;
  glsigma.it

(* [goal_goal_list : goal sigma -> goal list sigma] *)
let goal_goal_list gls = {it=[gls.it]; sigma=gls.sigma; }

(* identity tactic without any message *)
let tclIDTAC gls = goal_goal_list gls

(* the message printing identity tactic *)
let tclIDTAC_MESSAGE s gls =
  Feedback.msg_info (hov 0 s); tclIDTAC gls

(* General failure tactic *)
let tclFAIL_s s gls = user_err (str s)

(* The Fail tactic *)
let tclFAIL lvl s g = raise (FailError (lvl,lazy s))

let tclFAIL_lazy lvl s g = raise (FailError (lvl,s))

let start_tac gls =
  let sigr, g = unpackage gls in
  (sigr, [g])

let finish_tac (sigr,gl) = repackage sigr gl

(* Apply [tacfi.(i)] on the first n subgoals, [tacli.(i)] on the last
   m subgoals, and [tac] on the others *)
let thens3parts_tac tacfi tac tacli (sigr,gs) =
  let nf = Array.length tacfi in
  let nl = Array.length tacli in
  let ng = List.length gs in
  if ng<nf+nl then user_err (str "Not enough subgoals.");
  let gll =
      (List.map_i (fun i ->
        apply_sig_tac sigr (if i<nf then tacfi.(i) else if i>=ng-nl then tacli.(nl-ng+i) else tac))
        0 gs) in
    (sigr,List.flatten gll)

(* Apply [taci.(i)] on the first n subgoals and [tac] on the others *)
let thensf_tac taci tac = thens3parts_tac taci tac [||]

(* Apply [tac i] on the ith subgoal (no subgoals number check) *)
let thensi_tac tac (sigr,gs) =
  let gll =
    List.map_i (fun i -> apply_sig_tac sigr (tac i)) 1 gs in
  (sigr, List.flatten gll)

let then_tac tac = thensf_tac [||] tac

(* [tclTHENS3PARTS tac1 [|t1 ; ... ; tn|] tac2 [|t'1 ; ... ; t'm|] gls]
   applies the tactic [tac1] to [gls] then, applies [t1], ..., [tn] to
   the first [n] resulting subgoals, [t'1], ..., [t'm] to the last [m]
   subgoals and [tac2] to the rest of the subgoals in the middle. Raises an
   error if the number of resulting subgoals is strictly less than [n+m] *)
let tclTHENS3PARTS tac1 tacfi tac tacli gls =
  finish_tac (thens3parts_tac tacfi tac tacli (then_tac tac1 (start_tac gls)))

(* [tclTHENSFIRSTn tac1 [|t1 ; ... ; tn|] tac2 gls] applies the tactic [tac1]
   to [gls] and applies [t1], ..., [tn] to the first [n] resulting
   subgoals, and [tac2] to the others subgoals. Raises an error if
   the number of resulting subgoals is strictly less than [n] *)
let tclTHENSFIRSTn tac1 taci tac = tclTHENS3PARTS tac1 taci tac [||]

(* [tclTHENSLASTn tac1 tac2 [|t1 ;...; tn|] gls] applies the tactic [tac1]
   to [gls] and applies [t1], ..., [tn] to the last [n] resulting
   subgoals, and [tac2] to the other subgoals. Raises an error if the
   number of resulting subgoals is strictly less than [n] *)
let tclTHENSLASTn tac1 tac taci = tclTHENS3PARTS tac1 [||] tac taci

(* [tclTHEN_i tac taci gls] applies the tactic [tac] to [gls] and applies
   [(taci i)] to the i_th resulting subgoal (starting from 1), whatever the
   number of subgoals is *)
let tclTHEN_i tac taci gls =
  finish_tac (thensi_tac taci (then_tac tac (start_tac gls)))

(* [tclTHEN tac1 tac2 gls] applies the tactic [tac1] to [gls] and applies
   [tac2] to every resulting subgoals *)
let tclTHEN tac1 tac2 = tclTHENS3PARTS tac1 [||] tac2 [||]

(* [tclTHENSV tac1 [t1 ; ... ; tn] gls] applies the tactic [tac1] to
   [gls] and applies [t1],..., [tn] to the [n] resulting subgoals. Raises
   an error if the number of resulting subgoals is not [n] *)
let tclTHENSV tac1 tac2v =
  tclTHENS3PARTS tac1 tac2v (tclFAIL_s "Wrong number of tactics.") [||]

let tclTHENS tac1 tac2l = tclTHENSV tac1 (Array.of_list tac2l)

(* [tclTHENLAST tac1 tac2 gls] applies the tactic [tac1] to [gls] and [tac2]
   to the last resulting subgoal *)
let tclTHENLAST tac1 tac2 = tclTHENSLASTn tac1 tclIDTAC [|tac2|]

(* [tclTHENFIRST tac1 tac2 gls] applies the tactic [tac1] to [gls] and [tac2]
   to the first resulting subgoal *)
let tclTHENFIRST tac1 tac2 = tclTHENSFIRSTn tac1 [|tac2|] tclIDTAC

(* [tclTHENLIST [t1;..;tn]] applies [t1] then [t2] ... then [tn]. More
   convenient than [tclTHEN] when [n] is large. *)
let rec tclTHENLIST = function
    [] -> tclIDTAC
  | t1::tacl -> tclTHEN t1 (tclTHENLIST tacl)

(* [tclMAP f [x1..xn]] builds [(f x1);(f x2);...(f xn)] *)
let tclMAP tacfun l =
  List.fold_right (fun x -> (tclTHEN (tacfun x))) l tclIDTAC

let weak_progress glss gls =
match glss.Evd.it with
| [ g ] -> not (Proofview.Progress.goal_equal ~evd:gls.Evd.sigma
                  ~extended_evd:glss.Evd.sigma gls.Evd.it g)
| _ -> true

(* PROGRESS tac ptree applies tac to the goal ptree and fails if tac leaves
the goal unchanged *)
let tclPROGRESS tac ptree =
  let rslt = tac ptree in
  if weak_progress rslt ptree then rslt
(* spiwack: progress normally goes like this:
(Evd.progress_evar_map gls.Evd.sigma glss.Evd.sigma) || (weak_progress glss gls)
    This is immensly slow in the current implementation. Maybe we could
    reimplement progress_evar_map with restricted folds like "fold_undefined",
    with a good implementation of them.
*)
  else user_err (str"Failed to progress.")

(* ORELSE0 t1 t2 tries to apply t1 and if it fails, applies t2 *)
let tclORELSE0 t1 t2 g =
  try
    t1 g
  with (* Breakpoint *)
    | e when CErrors.noncritical e ->
      let e = Exninfo.capture e in catch_failerror e; t2 g

(* ORELSE t1 t2 tries to apply t1 and if it fails or does not progress,
   then applies t2 *)
let tclORELSE t1 t2 = tclORELSE0 (tclPROGRESS t1) t2

(* applies t1;t2then if t1 succeeds or t2else if t1 fails
   t2* are called in terminal position (unless t1 produces more than
   1 subgoal!) *)
let tclORELSE_THEN t1 t2then t2else gls =
  match
    try Some(tclPROGRESS t1 gls)
    with e when CErrors.noncritical e ->
      let e = Exninfo.capture e in catch_failerror e; None
  with
    | None -> t2else gls
    | Some sgl ->
        let sigr, gl = unpackage sgl in
        finish_tac (then_tac t2then  (sigr,gl))

(* TRY f tries to apply f, and if it fails, leave the goal unchanged *)
let tclTRY f = (tclORELSE0 f tclIDTAC)

let tclTHENTRY f g = (tclTHEN f (tclTRY g))

(* Try the first tactic that does not fail in a list of tactics *)

let rec tclFIRST = function
  | [] -> tclFAIL_s "No applicable tactic."
  |  t::rest -> tclORELSE0 t (tclFIRST rest)

(* Fails if a tactic did not solve the goal *)
let tclCOMPLETE tac = tclTHEN tac (tclFAIL_s "Proof is not complete.")

(* Iteration tacticals *)

let tclDO n t =
  let rec dorec k =
    if k < 0 then user_err
      (str"Wrong argument : Do needs a positive integer.");
    if Int.equal k 0 then tclIDTAC
    else if Int.equal k 1 then t
    else
      (* Thunk to avoid stack overflow with large n *)
      tclTHEN t (fun gl -> dorec (k-1) gl)
  in
  dorec n


(* Beware: call by need of CAML, g is needed *)
let rec tclREPEAT t g =
  tclORELSE_THEN t (tclREPEAT t) tclIDTAC g

let tclAT_LEAST_ONCE t = (tclTHEN t (tclREPEAT t))

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

let elimination_sort_of_goal gl =
  pf_apply Retyping.get_sort_family_of gl (pf_concl gl)

let elimination_sort_of_hyp id gl =
  pf_apply Retyping.get_sort_family_of gl (pf_get_hyp_typ gl id)

let elimination_sort_of_clause = function
  | None -> elimination_sort_of_goal
  | Some id -> elimination_sort_of_hyp id

(* Change evars *)
let tclEVARS sigma gls = tclIDTAC {gls with Evd.sigma=sigma}

let pf_with_evars glsev k gls =
  let evd, a = glsev gls in
    tclTHEN (tclEVARS evd) (k a) gls

let pf_constr_of_global gr k =
  pf_with_evars (fun gls -> pf_apply Evd.fresh_global gls gr) k

end

(************************************************************************)
(* Elimination Tacticals                                                *)
(************************************************************************)

(* The following tacticals allow to apply a tactic to the
   branches generated by the application of an elimination
  tactic.

  Two auxiliary types --branch_args and branch_assumptions-- are
  used to keep track of some information about the ``branches'' of
  the elimination. *)

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

let compute_induction_names check_and branchletsigns = function
  | None ->
      Array.make (Array.length branchletsigns) []
  | Some {CAst.loc;v=names} ->
      let names = fix_empty_or_and_pattern (Array.length branchletsigns) names in
      get_and_check_or_and_pattern_gen check_and ?loc names branchletsigns

(* Compute the let-in signature of case analysis or standard induction scheme *)
let compute_constructor_signatures env ~rec_flag ((_,k as ity),u) =
  let rec analrec c recargs =
    match c, recargs with
    | RelDecl.LocalAssum _ :: c, recarg::rest ->
        let rest = analrec c rest in
        begin match Declareops.dest_recarg recarg with
        | Norec | Nested _  -> true :: rest
        | Mrec (_,j)  ->
            if rec_flag && Int.equal j k then true :: true :: rest
            else true :: rest
        end
    | RelDecl.LocalDef _ :: c, rest -> false :: analrec c rest
    | [], [] -> []
    | _ -> anomaly (Pp.str "compute_constructor_signatures.")
  in
  let (mib,mip) = Inductive.lookup_mind_specif env ity in
  let map (ctx, _) = List.skipn (Context.Rel.length mib.mind_params_ctxt) (List.rev ctx) in
  let lc = Array.map map mip.mind_nf_lc in
  let lrecargs = Declareops.dest_subterms mip.mind_recargs in
  Array.map2 analrec lc lrecargs

open Proofview
open Proofview.Notations
open Tacmach

let tclIDTAC = tclUNIT ()

let tclTHEN t1 t2 =
  t1 <*> t2

let tclFAILn ?info lvl msg =
  let info = match info with
    (* If the backtrace points here it means the caller didn't save
        the backtrace correctly *)
    | None -> Exninfo.reify ()
    | Some info -> info
  in
  tclZERO ~info (FailError (lvl,lazy msg))

let tclFAIL ?info msg = tclFAILn ?info 0 msg

let tclZEROMSG ?info ?loc msg =
  let info = match info with
    (* If the backtrace points here it means the caller didn't save
        the backtrace correctly *)
    | None -> Exninfo.reify ()
    | Some info -> info
  in
  let info = match loc with
  | None -> info
  | Some loc -> Loc.add_loc info loc
  in
  let err = UserError msg in
  tclZERO ~info err

let catch_failerror e =
  try
    catch_failerror e;
    tclUNIT ()
  with e when CErrors.noncritical e ->
    let _, info = Exninfo.capture e in
    tclZERO ~info e

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

let tclEXACTLY_ONCE t = Proofview.tclEXACTLY_ONCE (FailError(0,lazy (assert false))) t

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
              tclFAIL errmsg
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
  | [] -> tclFAIL (str "Expect at least one goal.")
  | hd::tl ->
  Proofview.Unsafe.tclSETGOALS [hd] <*> t2 ans >>= fun ans ->
  Proofview.Unsafe.tclNEWGOALS tl <*>
  Proofview.tclUNIT ans

let tclTHENSLASTn t1 repeat l =
  tclTHENS3PARTS t1 [||] repeat l

let tclTHENLASTn t1 l =
  tclTHENS3PARTS t1 [||] (tclUNIT()) l
let tclTHENLAST t1 t2 = tclTHENLASTn t1 [|t2|]

let option_of_failure f x = try Some (f x) with Failure _ -> None

let tclBINDLAST t1 t2 =
  t1 >>= fun ans ->
  Proofview.Unsafe.tclGETGOALS >>= fun gls ->
  match option_of_failure List.sep_last gls with
  | None -> tclFAIL (str "Expect at least one goal.")
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
              tclFAIL errmsg
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
  | [] ->
    let info = Exninfo.reify () in
    tclZEROMSG ~info (str"No applicable tactic.")
  | t::rest -> tclORELSE0 t (tclFIRST rest)

let rec tclFIRST_PROGRESS_ON tac = function
  | []    -> tclFAIL (str "No applicable tactic")
  | [a]   -> tac a (* so that returned failure is the one from last item *)
  | a::tl -> tclORELSE (tac a) (tclFIRST_PROGRESS_ON tac tl)

let rec tclDO n t =
  if n < 0 then
    let info = Exninfo.reify () in
    tclZEROMSG ~info (str"Wrong argument : Do needs a positive integer.")
  else if n = 0 then tclUNIT ()
  else if n = 1 then t
  else
    (* Thunk to avoid stack overflow with large n *)
    tclTHEN t (tclUNIT () >>= fun () -> (tclDO (n-1) t))

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
        (let info = Exninfo.reify () in
        tclZEROMSG ~info (str"Proof is not complete."))
    ) <*>
      tclUNIT res

(* Try the first that solves the current goal *)
let tclSOLVE tacl = tclFIRST (List.map tclCOMPLETE tacl)

let tclPROGRESS t =
  Proofview.tclINDEPENDENT (Proofview.tclPROGRESS t)

(* Check that holes in arguments have been resolved *)

let check_evars env sigma extsigma origsigma =
  let reachable = lazy (Evarutil.reachable_from_evars sigma
                          (Evar.Map.domain (Evd.undefined_map origsigma))) in
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
      | Some (evk',evi) ->
          (* If [evk'] descends from [evk] which descends itself from
            an originally undefined evar in [origsigma], it is a not
            a fresh undefined hole from [sigma]. *)
          if Evar.Set.mem evk (Lazy.force reachable) then acc
          else (evk',evi)::acc
      | _ -> acc)
      extsigma []
  in
  match rest with
  | [] -> ()
  | (evk,evi) :: _ ->
    let (loc,_) = evi.Evd.evar_source in
    Pretype_errors.error_unsolvable_implicit ?loc env sigma evk None

let tclMAPDELAYEDWITHHOLES accept_unresolved_holes l tac =
  let rec aux = function
    | [] -> tclUNIT ()
    | x :: l ->
      Proofview.Goal.enter begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma_initial = Proofview.Goal.sigma gl in
        let (sigma, x) = x env sigma_initial in
        Proofview.Unsafe.tclEVARS sigma <*> tac x >>= fun () -> aux l >>= fun () ->
        if accept_unresolved_holes then
          tclUNIT ()
        else
          tclEVARMAP >>= fun sigma_final ->
          try
            let () = check_evars env sigma_final sigma sigma_initial in
            tclUNIT ()
          with e when CErrors.noncritical e ->
            let e, info = Exninfo.capture e in
            tclZERO ~info e
        end in
  aux l

(* The following is basically
  tclMAPDELAYEDWITHHOLES accept_unresolved_holes [fun _ _ -> (sigma,())] (fun () -> tac)
  but with value not necessarily in unit *)

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
                let e, info = Exninfo.capture e in
                tclZERO ~info e
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
      | Logic_monad.Tac_Timeout as e ->
        let info = Exninfo.reify () in
        Proofview.tclZERO ~info (FailError (0,lazy (CErrors.print e)))
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
  (* We only use [id] *)
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

let nLastHypsId gl n = List.map (NamedDecl.get_id) (nLastDecls gl n)
let nLastHyps gl n = List.map mkVar (nLastHypsId gl n)

let ifOnHyp pred tac1 tac2 id =
  Proofview.Goal.enter begin fun gl ->
  let typ = Tacmach.pf_get_hyp_typ id gl in
  if pf_apply pred gl (id,typ) then
    tac1 id
  else
    tac2 id
  end

let onHyps find tac = Proofview.Goal.enter begin fun gl -> tac (find gl) end

let onNLastDecls n tac  = onHyps (fun gl -> nLastDecls gl n) tac
let onNLastHypsId n tac = onHyps (fun gl -> nLastHypsId gl n) tac
let onNLastHyps n tac   = onHyps (fun gl -> nLastHyps gl n) tac

let afterHyp id tac =
  Proofview.Goal.enter begin fun gl ->
  let hyps = Proofview.Goal.hyps gl in
  let rem, _ = List.split_when (NamedDecl.get_id %> Id.equal id) hyps in
  tac rem
  end

let fullGoal gl =
  let hyps = Tacmach.pf_ids_of_hyps gl in
  None :: List.map Option.make hyps

let tryAllHyps tac =
  Proofview.Goal.enter begin fun gl ->
  let hyps = Tacmach.pf_ids_of_hyps gl in
  tclFIRST_PROGRESS_ON tac hyps
  end
let tryAllHypsAndConcl tac =
  Proofview.Goal.enter begin fun gl ->
    tclFIRST_PROGRESS_ON tac (fullGoal gl)
  end

let onClause tac cl =
  Proofview.Goal.enter begin fun gl ->
  let hyps = Tacmach.pf_ids_of_hyps gl in
  tclMAP tac (Locusops.simple_clause_of (fun () -> hyps) cl)
  end

let fullGoal gl = None :: List.map Option.make (Tacmach.pf_ids_of_hyps gl)
let onAllHyps tac =
  Proofview.Goal.enter begin fun gl ->
    tclMAP tac (Tacmach.pf_ids_of_hyps gl)
    end
let onAllHypsAndConcl tac =
  Proofview.Goal.enter begin fun gl ->
    tclMAP tac (fullGoal gl)
    end

let elimination_sort_of_goal gl =
  (* Retyping will expand evars anyway. *)
  let c = Proofview.Goal.concl gl in
  pf_apply Retyping.get_sort_family_of gl c

let elimination_sort_of_hyp id gl =
  (* Retyping will expand evars anyway. *)
  let c = pf_get_hyp_typ id gl in
  pf_apply Retyping.get_sort_family_of gl c

let elimination_sort_of_clause id gl = match id with
| None -> elimination_sort_of_goal gl
| Some id -> elimination_sort_of_hyp id gl

let pf_constr_of_global ref =
  Proofview.tclEVARMAP >>= fun sigma ->
  Proofview.tclENV >>= fun env ->
  let (sigma, c) = Evd.fresh_global env sigma ref in
  Proofview.Unsafe.tclEVARS sigma <*> Proofview.tclUNIT c

let tclTYPEOFTHEN ?refresh c tac =
  Proofview.Goal.enter (fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let (sigma, t) = Typing.type_of ?refresh env sigma c in
    Proofview.Unsafe.tclEVARS sigma <*> tac sigma t)

let tclSELECT = Goal_select.tclSELECT
