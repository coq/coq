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
open Evd
open Proof_type
open Logic

module NamedDecl = Context.Named.Declaration

let sig_it x = x.it
let project x = x.sigma

(* Getting env *)

let pf_env gls = Global.env_of_context (Goal.V82.hyps (project gls) (sig_it gls))
let pf_hyps gls = EConstr.named_context_of_val (Goal.V82.hyps (project gls) (sig_it gls))

let refiner pr goal_sigma =
  let (sgl,sigma') = prim_refiner pr goal_sigma.sigma goal_sigma.it in
  { it = sgl; sigma = sigma'; }

(* Profiling refiner *)
let refiner = 
  if Flags.profile then
    let refiner_key = CProfile.declare_profile "refiner" in
      CProfile.profile2 refiner_key refiner
  else refiner

(*********************)
(*   Tacticals       *)
(*********************)


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
let tclFAIL_s s gls = user_err ~hdr:"Refiner.tclFAIL_s" (str s)

(* A special exception for levels for the Fail tactic *)
exception FailError of int * Pp.t Lazy.t

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
  if ng<nf+nl then user_err ~hdr:"Refiner.thensn_tac" (str "Not enough subgoals.");
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
let tclPROGRESS tac ptree =
  let rslt = tac ptree in
  if Goal.V82.progress rslt ptree then rslt
  else user_err ~hdr:"Refiner.PROGRESS" (str"Failed to progress.")

(* Execute tac, show the names of new hypothesis names created by tac
   in the "as" format and then forget everything. From the logical
   point of view [tclSHOWHYPS tac] is therefore equivalent to idtac,
   except that it takes the time and memory of tac and prints "as"
   information). The resulting (unchanged) goals are printed *after*
   the as-expression, which forces pg to some gymnastic.
   TODO: Have something similar (better?) in the xml protocol.
   NOTE: some tactics delete hypothesis and reuse names (induction,
   destruct), this is not detected by this tactical. *)
let tclSHOWHYPS (tac : tactic) (goal: Goal.goal Evd.sigma)
    :Proof_type.goal list Evd.sigma =
  let oldhyps = pf_hyps goal in
  let rslt:Proof_type.goal list Evd.sigma = tac goal in
  let { it = gls; sigma = sigma; } = rslt in
  let hyps =
    List.map (fun gl -> pf_hyps { it = gl; sigma=sigma; }) gls in
  let cmp d1 d2 = Names.Id.equal (NamedDecl.get_id d1) (NamedDecl.get_id d2) in
  let newhyps =
    List.map
      (fun hypl -> List.subtract cmp hypl oldhyps)
      hyps
  in
  let s = 
    let frst = ref true in
    List.fold_left
    (fun acc lh -> acc ^ (if !frst then (frst:=false;"") else " | ")
      ^ (List.fold_left
	   (fun acc d -> (Names.Id.to_string (NamedDecl.get_id d)) ^ " " ^ acc)
	   "" lh))
    "" newhyps in
  Feedback.msg_notice
    (str "<infoH>"
      ++  (hov 0 (str s))
      ++  (str "</infoH>"));
  tclIDTAC goal;;


let catch_failerror (e, info) =
  if catchable_exception e then Control.check_for_interrupt ()
  else match e with
  | FailError (0,_) ->
      Control.check_for_interrupt ()
  | FailError (lvl,s) ->
    iraise (FailError (lvl - 1, s), info)
  | e -> iraise (e, info)
  (** FIXME: do we need to add a [Errors.push] here? *)

(* ORELSE0 t1 t2 tries to apply t1 and if it fails, applies t2 *)
let tclORELSE0 t1 t2 g =
  try
    t1 g
  with (* Breakpoint *)
    | e when CErrors.noncritical e ->
      let e = CErrors.push e in catch_failerror e; t2 g

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
      let e = CErrors.push e in catch_failerror e; None
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

let ite_gen tcal tac_if continue tac_else gl=
  let success=ref false in
  let tac_if0 gl=
    let result=tac_if gl in
      success:=true;result in
  let tac_else0 e gl=
    if !success then
      iraise e
    else
      try
        tac_else gl
      with
        e' when CErrors.noncritical e' -> iraise e in
  try
    tcal tac_if0 continue gl
  with (* Breakpoint *)
  | e when CErrors.noncritical e ->
    let e = CErrors.push e in catch_failerror e; tac_else0 e gl

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
    if k < 0 then user_err ~hdr:"Refiner.tclDO"
      (str"Wrong argument : Do needs a positive integer.");
    if Int.equal k 0 then tclIDTAC
    else if Int.equal k 1 then t else (tclTHEN t (dorec (k-1)))
  in
  dorec n


(* Beware: call by need of CAML, g is needed *)
let rec tclREPEAT t g =
  tclORELSE_THEN t (tclREPEAT t) tclIDTAC g

let tclAT_LEAST_ONCE t = (tclTHEN t (tclREPEAT t))

(* Repeat on the first subgoal (no failure if no more subgoal) *)
let rec tclREPEAT_MAIN t g =
  (tclORELSE (tclTHEN_i t (fun i -> if Int.equal i 1 then (tclREPEAT_MAIN t) else
    tclIDTAC)) tclIDTAC) g

(* Change evars *)
let tclEVARS sigma gls = tclIDTAC {gls with sigma=sigma}

let tclEVARUNIVCONTEXT ctx gls = tclIDTAC {gls with sigma= Evd.set_universe_context gls.sigma ctx}

(* Push universe context *)
let tclPUSHCONTEXT rigid ctx tac gl = 
  tclTHEN (tclEVARS (Evd.merge_context_set rigid (project gl) ctx)) tac gl

let tclPUSHEVARUNIVCONTEXT ctx gl = 
  tclEVARS (Evd.merge_universe_context (project gl) ctx) gl

let tclPUSHCONSTRAINTS cst gl = 
  tclEVARS (Evd.add_constraints (project gl) cst) gl
