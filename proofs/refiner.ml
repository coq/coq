(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Compat
open Pp
open Util
open Term
open Termops
open Sign
open Evd
open Sign
open Environ
open Reductionops
open Type_errors
open Proof_type
open Logic


let sig_it x = x.it
let project x = x.sigma

(* Getting env *)

let pf_env gls = Global.env_of_context (Goal.V82.hyps (project gls) (sig_it gls))
let pf_hyps gls = named_context_of_val (Goal.V82.hyps (project gls) (sig_it gls))

let abstract_operation syntax semantics =
  semantics

let abstract_tactic_expr ?(dflt=false) te tacfun gls =
  abstract_operation (Tactic(te,dflt)) tacfun gls

let abstract_tactic ?(dflt=false) te =
  !abstract_tactic_box := Some te;
  abstract_tactic_expr ~dflt (Tacexpr.TacAtom (dummy_loc,te))

let abstract_extended_tactic ?(dflt=false) s args =
  abstract_tactic ~dflt (Tacexpr.TacExtend (dummy_loc, s, args))

let refiner = function
  | Prim pr ->
      let prim_fun = prim_refiner pr in
	(fun goal_sigma ->
          let (sgl,sigma') = prim_fun goal_sigma.sigma goal_sigma.it in
	  {it=sgl; sigma = sigma'})


  | Nested (_,_) | Decl_proof _ ->
      failwith "Refiner: should not occur"

	(* Daimon is a canonical unfinished proof *)

  | Daimon ->
      fun gls ->
	{it=[];sigma=gls.sigma}


let norm_evar_tac gl = refiner (Prim Change_evars) gl

(*********************)
(*   Tacticals       *)
(*********************)


let unpackage glsig = (ref (glsig.sigma)),glsig.it

let repackage r v = {it=v;sigma = !r}

let apply_sig_tac r tac g =
  check_for_interrupt (); (* Breakpoint *)
  let glsigma = tac (repackage r g) in
  r := glsigma.sigma;
  glsigma.it

(* [goal_goal_list : goal sigma -> goal list sigma] *)
let goal_goal_list gls = {it=[gls.it];sigma=gls.sigma}

(* forces propagation of evar constraints *)
let tclNORMEVAR = norm_evar_tac

(* identity tactic without any message *)
let tclIDTAC gls = goal_goal_list gls

(* the message printing identity tactic *)
let tclIDTAC_MESSAGE s gls =
  msg (hov 0 s); tclIDTAC gls

(* General failure tactic *)
let tclFAIL_s s gls = errorlabstrm "Refiner.tclFAIL_s" (str s)

(* A special exception for levels for the Fail tactic *)
exception FailError of int * std_ppcmds Lazy.t

(* The Fail tactic *)
let tclFAIL lvl s g = raise (FailError (lvl,lazy s))

let tclFAIL_lazy lvl s g = raise (FailError (lvl,s))

let start_tac gls =
  let (sigr,g) = unpackage gls in
  (sigr,[g])

let finish_tac (sigr,gl) = repackage sigr gl

(* Apply [tacfi.(i)] on the first n subgoals, [tacli.(i)] on the last
   m subgoals, and [tac] on the others *)
let thens3parts_tac tacfi tac tacli (sigr,gs) =
  let nf = Array.length tacfi in
  let nl = Array.length tacli in
  let ng = List.length gs in
  if ng<nf+nl then errorlabstrm "Refiner.thensn_tac" (str "Not enough subgoals.");
  let gll =
      (list_map_i (fun i ->
        apply_sig_tac sigr (if i<nf then tacfi.(i) else if i>=ng-nl then tacli.(nl-ng+i) else tac))
	0 gs) in
    (sigr,List.flatten gll)

(* Apply [taci.(i)] on the first n subgoals and [tac] on the others *)
let thensf_tac taci tac = thens3parts_tac taci tac [||]

(* Apply [taci.(i)] on the last n subgoals and [tac] on the others *)
let thensl_tac tac taci = thens3parts_tac [||] tac taci

(* Apply [tac i] on the ith subgoal (no subgoals number check) *)
let thensi_tac tac (sigr,gs) =
  let gll =
    list_map_i (fun i -> apply_sig_tac sigr (tac i)) 1 gs in
  (sigr, List.flatten gll)

let then_tac tac = thensf_tac [||] tac

let non_existent_goal n =
  errorlabstrm ("No such goal: "^(string_of_int n))
    (str"Trying to apply a tactic to a non existent goal")

(* Apply tac on the i-th goal (if i>0). If i<0, then start counting from
   the last goal (i=-1). *)
let theni_tac i tac ((_,gl) as subgoals) =
  let nsg = List.length gl in
  let k = if i < 0 then nsg + i + 1 else i in
  if nsg < 1 then errorlabstrm "theni_tac" (str"No more subgoals.")
  else if k >= 1 & k <= nsg then
    thensf_tac
      (Array.init k (fun i -> if i+1 = k then tac else tclIDTAC)) tclIDTAC
      subgoals
  else non_existent_goal k

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

let tclTHENLASTn tac1 taci = tclTHENSLASTn tac1 tclIDTAC taci
let tclTHENFIRSTn tac1 taci = tclTHENSFIRSTn tac1 taci tclIDTAC

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

(* PROGRESS tac ptree applies tac to the goal ptree and fails if tac leaves
the goal unchanged *)
let tclWEAK_PROGRESS tac ptree =
  let rslt = tac ptree in
  if Goal.V82.weak_progress rslt ptree then rslt
  else errorlabstrm "Refiner.WEAK_PROGRESS" (str"Failed to progress.")

(* PROGRESS tac ptree applies tac to the goal ptree and fails if tac leaves
the goal unchanged *)
let tclPROGRESS tac ptree =
  let rslt = tac ptree in
  if Goal.V82.progress rslt ptree then rslt
  else errorlabstrm "Refiner.PROGRESS" (str"Failed to progress.")

(* Same as tclWEAK_PROGRESS but fails also if tactics generates several goals,
   one of them being identical to the original goal *)
let tclNOTSAMEGOAL (tac : tactic) goal =
  let same_goal gls1 evd2 gl2 =
    Goal.V82.same_goal gls1.sigma gls1.it evd2 gl2
  in
  let rslt = tac goal in
  let {it=gls;sigma=sigma} = rslt in
  if List.exists (same_goal goal sigma) gls
  then errorlabstrm "Refiner.tclNOTSAMEGOAL"
      (str"Tactic generated a subgoal identical to the original goal.")
  else rslt

let catch_failerror e =
  if catchable_exception e then check_for_interrupt ()
  else match e with
  | FailError (0,_) | Loc.Exc_located(_, FailError (0,_))
  | Loc.Exc_located(_, LtacLocated (_,FailError (0,_)))  ->
      check_for_interrupt ()
  | FailError (lvl,s) -> raise (FailError (lvl - 1, s))
  | Loc.Exc_located(s,FailError (lvl,s')) ->
      raise (Loc.Exc_located(s,FailError (lvl - 1, s')))
  | Loc.Exc_located(s,LtacLocated (s'',FailError (lvl,s')))  ->
      raise
       (Loc.Exc_located(s,LtacLocated (s'',FailError (lvl - 1,s'))))
  | e -> raise e

(* ORELSE0 t1 t2 tries to apply t1 and if it fails, applies t2 *)
let tclORELSE0 t1 t2 g =
  try
    t1 g
  with (* Breakpoint *)
    | e -> catch_failerror e; t2 g

(* ORELSE t1 t2 tries to apply t1 and if it fails or does not progress,
   then applies t2 *)
let tclORELSE t1 t2 = tclORELSE0 (tclPROGRESS t1) t2

(* applies t1;t2then if t1 succeeds or t2else if t1 fails
   t2* are called in terminal position (unless t1 produces more than
   1 subgoal!) *)
let tclORELSE_THEN t1 t2then t2else gls =
  match
    try Some(tclPROGRESS t1 gls)
    with e -> catch_failerror e; None
  with
    | None -> t2else gls
    | Some sgl ->
        let (sigr,gl) = unpackage sgl in
        finish_tac (then_tac t2then  (sigr,gl))

(* TRY f tries to apply f, and if it fails, leave the goal unchanged *)
let tclTRY f = (tclORELSE0 f tclIDTAC)

let tclTHENTRY f g = (tclTHEN f (tclTRY g))

(* Try the first tactic that does not fail in a list of tactics *)

let rec tclFIRST = function
  | [] -> tclFAIL_s "No applicable tactic."
  |  t::rest -> tclORELSE0 t (tclFIRST rest)

let ite_gen tcal tac_if continue tac_else gl=
  let success=ref false in
  let tac_if0 gl=
    let result=tac_if gl in
      success:=true;result in
  let tac_else0 e gl=
    if !success then
      raise e
    else
      tac_else gl in
    try
      tcal tac_if0 continue gl
    with (* Breakpoint *)
      | e -> catch_failerror e; tac_else0 e gl

(* Try the first tactic and, if it succeeds, continue with
   the second one, and if it fails, use the third one *)

let tclIFTHENELSE=ite_gen tclTHEN

(* Idem with tclTHENS and tclTHENSV *)

let tclIFTHENSELSE=ite_gen tclTHENS

let tclIFTHENSVELSE=ite_gen tclTHENSV

let tclIFTHENTRYELSEMUST tac1 tac2 gl =
  tclIFTHENELSE tac1 (tclTRY tac2) tac2 gl

(* Fails if a tactic did not solve the goal *)
let tclCOMPLETE tac = tclTHEN tac (tclFAIL_s "Proof is not complete.")

(* Try the first thats solves the current goal *)
let tclSOLVE tacl = tclFIRST (List.map tclCOMPLETE tacl)


(* Iteration tacticals *)

let tclDO n t =
  let rec dorec k =
    if k < 0 then errorlabstrm "Refiner.tclDO"
      (str"Wrong argument : Do needs a positive integer.");
    if k = 0 then tclIDTAC
    else if k = 1 then t else (tclTHEN t (dorec (k-1)))
  in
  dorec n

(* Fails if a tactic hasn't finished after a certain amount of time *)

exception TacTimeout

let tclTIMEOUT n t g =
  let timeout_handler _ = raise TacTimeout in
  let psh = Sys.signal Sys.sigalrm (Sys.Signal_handle timeout_handler) in
  ignore (Unix.alarm n);
  let restore_timeout () =
    ignore (Unix.alarm 0);
    Sys.set_signal Sys.sigalrm psh
  in
  try
    let res = t g in
    restore_timeout ();
    res
  with
    | TacTimeout | Loc.Exc_located(_,TacTimeout) ->
      restore_timeout ();
      errorlabstrm "Refiner.tclTIMEOUT" (str"Timeout!")
    | e -> restore_timeout (); raise e

(* Beware: call by need of CAML, g is needed *)
let rec tclREPEAT t g =
  tclORELSE_THEN t (tclREPEAT t) tclIDTAC g

let tclAT_LEAST_ONCE t = (tclTHEN t (tclREPEAT t))

(* Repeat on the first subgoal (no failure if no more subgoal) *)
let rec tclREPEAT_MAIN t g =
  (tclORELSE (tclTHEN_i t (fun i -> if i = 1 then (tclREPEAT_MAIN t) else
    tclIDTAC)) tclIDTAC) g

(*s Tactics handling a list of goals. *)

type tactic_list = (goal list sigma) -> (goal list sigma)

(* Functions working on goal list for correct backtracking in Prolog *)

let tclFIRSTLIST = tclFIRST
let tclIDTAC_list gls = gls

(* first_goal : goal list sigma -> goal sigma *)

let first_goal gls =
  let gl = gls.it and sig_0 = gls.sigma in
  if gl = [] then error "first_goal";
  { it = List.hd gl; sigma = sig_0 }

(* goal_goal_list : goal sigma -> goal list sigma *)

let goal_goal_list gls =
  let gl = gls.it and sig_0 = gls.sigma in { it = [gl]; sigma = sig_0 }

(* tactic -> tactic_list : Apply a tactic to the first goal in the list *)

let apply_tac_list tac glls =
  let (sigr,lg) = unpackage glls in
  match lg with
  | (g1::rest) ->
      let gl = apply_sig_tac sigr tac g1 in
      repackage sigr (gl@rest)
  | _ -> error "apply_tac_list"

let then_tactic_list tacl1 tacl2 glls =
  let glls1 = tacl1 glls in
  let glls2 = tacl2 glls1 in
  glls2

(* Transform a tactic_list into a tactic *)

let tactic_list_tactic tac gls =
    let glres = tac (goal_goal_list gls) in
    glres

(* Change evars *)
let tclEVARS sigma gls = tclIDTAC {gls with sigma=sigma}

(* Pretty-printers. *)

let pp_info = ref (fun _ _ _ -> assert false)
let set_info_printer f = pp_info := f

let tclINFO (tac : tactic) gls =
  msgnl (hov 0 (str "Warning: info is currently not working"));
  tac gls

(* Check that holes in arguments have been resolved *)

let check_evars env sigma extsigma gl =
  let origsigma = gl.sigma in
  let rest =
    Evd.fold_undefined (fun evk evi acc ->
      if Evd.is_undefined extsigma evk & not (Evd.mem origsigma evk) then
	evi::acc
      else
	acc)
      sigma []
  in
  if rest <> [] then
    let evi = List.hd rest in
    let (loc,k) = evi.evar_source in
    let evi = Evarutil.nf_evar_info sigma evi in
    Pretype_errors.error_unsolvable_implicit loc env sigma evi k None

let tclWITHHOLES accept_unresolved_holes tac sigma c gl =
  if sigma == project gl then tac c gl
  else
    let res = tclTHEN (tclEVARS sigma) (tac c) gl in
    if not accept_unresolved_holes then
      check_evars (pf_env gl) (res).sigma sigma gl;
    res
