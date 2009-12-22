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
open Term
open Termops
open Sign
open Evd
open Sign
open Environ
open Reductionops
open Type_errors
open Proof_trees
open Proof_type
open Logic

type transformation_tactic = proof_tree -> (goal list * validation)

let hypotheses gl = gl.evar_hyps
let conclusion gl = gl.evar_concl

let sig_it x = x.it
let project x = x.sigma

let pf_status pf = pf.open_subgoals

let is_complete pf = (0 = (pf_status pf))

let on_open_proofs f pf = if is_complete pf then pf else f pf

let and_status = List.fold_left (+) 0

(* Getting env *)

let pf_env gls = Global.env_of_context (sig_it gls).evar_hyps
let pf_hyps gls = named_context_of_val (sig_it gls).evar_hyps


let descend n p =
  match p.ref with
    | None        -> error "It is a leaf."
    | Some(r,pfl) ->
    	if List.length pfl >= n then
	  (match list_chop (n-1) pfl with
	     | left,(wanted::right) ->
		 (wanted,
		  (fun pfl' ->
		    if false (* debug *) then assert
		      (List.length pfl'=1 & (List.hd pfl').goal = wanted.goal);
                    let pf'       = List.hd pfl' in
                    let spfl      = left@(pf'::right) in
                    let newstatus = and_status (List.map pf_status spfl) in
                    { p with
			open_subgoals = newstatus;
			ref           = Some(r,spfl) }))
	     | _ -> assert false)
    	else
	  error "Too few subproofs"


(* [mapshape [ l1 ; ... ; lk ] [ v1 ; ... ; vk ] [ p_1 ; .... ; p_(l1+...+lk) ]]
   gives
   [ (v1 [p_1 ... p_l1]) ; (v2 [ p_(l1+1) ... p_(l1+l2) ]) ; ... ;
   (vk [ p_(l1+...+l(k-1)+1) ... p_(l1+...lk) ]) ]
 *)

let rec mapshape nl (fl : (proof_tree list -> proof_tree) list)
                    (l : proof_tree list) =
  match nl with
    | [] -> []
    | h::t ->
	let m,l = list_chop h l in
	(List.hd fl m) :: (mapshape t (List.tl fl) l)

(* [frontier : proof_tree -> goal list * validation]
   given a proof [p], [frontier p] gives [(l,v)] where [l] is the list of goals
   to be solved to complete the proof, and [v] is the corresponding
   validation *)

let rec frontier p =
  match p.ref with
    | None ->
	([p.goal],
	 (fun lp' ->
	    let p' = List.hd lp' in
            if Evd.eq_evar_info p'.goal p.goal then
	      p'
            else
	      errorlabstrm "Refiner.frontier"
                (str"frontier was handed back a ill-formed proof.")))
    | Some(r,pfl) ->
    	let gll,vl = List.split(List.map frontier pfl) in
    	(List.flatten gll,
         (fun retpfl ->
            let pfl' = mapshape (List.map List.length gll) vl retpfl in
              { p with
		  open_subgoals = and_status (List.map pf_status pfl');
		  ref = Some(r,pfl')}))

(* TODO LEM: I might have to make sure that these hooks are called
   only when called from solve_nth_pftreestate; I can build the hook
   call into the "f", then.
 *)
let solve_hook = ref ignore
let set_solve_hook = (:=) solve_hook

let rec frontier_map_rec f n p =
  if n < 1 || n > p.open_subgoals then p else
  match p.ref with
    | None ->
        let p' = f p in
        if Evd.eq_evar_info p'.goal p.goal then
	  begin
	    !solve_hook p';
	    p'
	  end
        else
	  errorlabstrm "Refiner.frontier_map"
            (str"frontier_map was handed back a ill-formed proof.")
    | Some(r,pfl) ->
        let (_,rpfl') =
          List.fold_left
            (fun (n,acc) p -> (n-p.open_subgoals,frontier_map_rec f n p::acc))
            (n,[]) pfl in
        let pfl' = List.rev rpfl' in
        { p with
	    open_subgoals = and_status (List.map pf_status pfl');
            ref = Some(r,pfl')}

let frontier_map f n p =
  let nmax = p.open_subgoals in
  let n = if n < 0 then nmax + n + 1 else n in
  if n < 1 || n > nmax then
    errorlabstrm "Refiner.frontier_map" (str "No such subgoal");
  frontier_map_rec f n p

let rec frontier_mapi_rec f i p =
  if p.open_subgoals = 0 then p else
  match p.ref with
    | None ->
        let p' = f i p in
        if Evd.eq_evar_info p'.goal p.goal then
	  begin
	    !solve_hook p';
	    p'
	  end
        else
	  errorlabstrm "Refiner.frontier_mapi"
            (str"frontier_mapi was handed back a ill-formed proof.")
    | Some(r,pfl) ->
        let (_,rpfl') =
          List.fold_left
            (fun (n,acc) p -> (n+p.open_subgoals,frontier_mapi_rec f n p::acc))
            (i,[]) pfl in
        let pfl' = List.rev rpfl' in
        { p with
	    open_subgoals = and_status (List.map pf_status pfl');
            ref = Some(r,pfl')}

let frontier_mapi f p = frontier_mapi_rec f 1 p

(* [list_pf p] is the lists of goals to be solved in order to complete the
   proof [p] *)

let list_pf p = fst (frontier p)

let rec nb_unsolved_goals pf = pf.open_subgoals

(* leaf g is the canonical incomplete proof of a goal g *)

let leaf g =
  { open_subgoals = 1;
    goal = g;
    ref = None }

(* refiner r is a tactic applying the rule r *)

let check_subproof_connection gl spfl =
  list_for_all2eq (fun g pf -> Evd.eq_evar_info g pf.goal) gl spfl

let abstract_operation syntax semantics gls =
  let (sgl_sigma,validation) = semantics gls in
  let hidden_proof = validation (List.map leaf sgl_sigma.it) in
  (sgl_sigma,
  fun spfl ->
    assert (check_subproof_connection sgl_sigma.it spfl);
    { open_subgoals = and_status (List.map pf_status spfl);
      goal = gls.it;
      ref = Some(Nested(syntax,hidden_proof),spfl)})

let abstract_tactic_expr ?(dflt=false) te tacfun gls =
  abstract_operation (Tactic(te,dflt)) tacfun gls

let abstract_tactic ?(dflt=false) te =
  !abstract_tactic_box := Some te;
  abstract_tactic_expr ~dflt (Tacexpr.TacAtom (dummy_loc,te))

let abstract_extended_tactic ?(dflt=false) s args =
  abstract_tactic ~dflt (Tacexpr.TacExtend (dummy_loc, s, args))

let refiner = function
  | Prim pr as r ->
      let prim_fun = prim_refiner pr in
	(fun goal_sigma ->
          let (sgl,sigma') = prim_fun goal_sigma.sigma goal_sigma.it in
	    ({it=sgl; sigma = sigma'},
            (fun spfl ->
	      assert (check_subproof_connection sgl spfl);
              { open_subgoals = and_status (List.map pf_status spfl);
		goal = goal_sigma.it;
		ref = Some(r,spfl) })))


  | Nested (_,_) | Decl_proof _ ->
      failwith "Refiner: should not occur"

	(* Daimon is a canonical unfinished proof *)

  | Daimon ->
      fun gls ->
	({it=[];sigma=gls.sigma},
	 fun spfl ->
	   assert (spfl=[]);
	   { open_subgoals = 0;
             goal = gls.it;
             ref = Some(Daimon,[])})


let norm_evar_tac gl = refiner (Prim Change_evars) gl

let norm_evar_proof sigma pf =
  let nf_subgoal i sgl =
    let (gll,v) = norm_evar_tac {it=sgl.goal;sigma=sigma} in
      v (List.map leaf gll.it) in
    frontier_mapi nf_subgoal pf

(* [extract_open_proof : proof_tree -> constr * (int * constr) list]
   takes a (not necessarly complete) proof and gives a pair (pfterm,obl)
   where pfterm is the constr corresponding to the proof
   and [obl] is an [int*constr list] [ (m1,c1) ; ... ; (mn,cn)]
   where the mi are metavariables numbers, and ci are their types.
   Their proof should be completed in order to complete the initial proof *)

let extract_open_proof sigma pf =
  let next_meta =
    let meta_cnt = ref 0 in
    let rec f () =
      incr meta_cnt;
      if Evd.mem sigma (existential_of_int !meta_cnt) then f ()
      else !meta_cnt
    in f
  in
  let open_obligations = ref [] in
  let rec proof_extractor vl = function
    | {ref=Some(Prim _,_)} as pf -> prim_extractor proof_extractor vl pf

    | {ref=Some(Nested(_,hidden_proof),spfl)} ->
	let sgl,v = frontier hidden_proof in
	let flat_proof = v spfl in
	proof_extractor vl flat_proof

    | {ref=Some(Decl_proof _,[pf])} -> (proof_extractor vl) pf

    | {ref=(None|Some(Daimon,[]));goal=goal} ->
	let visible_rels =
          map_succeed
            (fun id ->
               try let n = proof_variable_index id vl in (n,id)
	       with Not_found -> failwith "caught")
            (ids_of_named_context (named_context_of_val goal.evar_hyps)) in
	let sorted_rels =
	  Sort.list (fun (n1,_) (n2,_) -> n1 > n2 ) visible_rels in
        let sorted_env =
          List.map (fun (n,id) -> (n,lookup_named_val id goal.evar_hyps))
            sorted_rels in
	let abs_concl =
          List.fold_right (fun (_,decl) c -> mkNamedProd_or_LetIn decl c)
            sorted_env goal.evar_concl	in
        let inst = List.filter (fun (_,(_,b,_)) -> b = None) sorted_env in
        let meta = next_meta () in
	open_obligations := (meta,abs_concl):: !open_obligations;
	applist (mkMeta meta, List.map (fun (n,_) -> mkRel n) inst)

    | _ -> anomaly "Bug: a case has been forgotten in proof_extractor"
  in
  let pfterm = proof_extractor [] pf in
  (pfterm, List.rev !open_obligations)

(*********************)
(*   Tacticals       *)
(*********************)

(* unTAC : tactic -> goal sigma -> proof sigma *)

let unTAC tac g =
  let (gl_sigma,v) = tac g in
  { it = v (List.map leaf gl_sigma.it); sigma = gl_sigma.sigma }

let unpackage glsig = (ref (glsig.sigma)),glsig.it

let repackage r v = {it=v;sigma = !r}

let apply_sig_tac r tac g =
  check_for_interrupt (); (* Breakpoint *)
  let glsigma,v = tac (repackage r g) in
  r := glsigma.sigma;
  (glsigma.it,v)

let idtac_valid = function
    [pf] -> pf
  | _ -> anomaly "Refiner.idtac_valid"

(* [goal_goal_list : goal sigma -> goal list sigma] *)
let goal_goal_list gls = {it=[gls.it];sigma=gls.sigma}

(* forces propagation of evar constraints *)
let tclNORMEVAR = norm_evar_tac

(* identity tactic without any message *)
let tclIDTAC gls = (goal_goal_list gls, idtac_valid)

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
  (sigr,[g],idtac_valid)

let finish_tac (sigr,gl,p) = (repackage sigr gl, p)

(* Apply [taci.(i)] on the first n subgoals and [tac] on the others *)
let thens3parts_tac tacfi tac tacli (sigr,gs,p) =
  let nf = Array.length tacfi in
  let nl = Array.length tacli in
  let ng = List.length gs in
  if ng<nf+nl then errorlabstrm "Refiner.thensn_tac" (str "Not enough subgoals.");
  let gll,pl =
    List.split
      (list_map_i (fun i ->
        apply_sig_tac sigr (if i<nf then tacfi.(i) else if i>=ng-nl then tacli.(nl-ng+i) else tac))
	0 gs) in
  (sigr, List.flatten gll,
   compose p (mapshape (List.map List.length gll) pl))

(* Apply [taci.(i)] on the first n subgoals and [tac] on the others *)
let thensf_tac taci tac = thens3parts_tac taci tac [||]

(* Apply [taci.(i)] on the last n subgoals and [tac] on the others *)
let thensl_tac tac taci = thens3parts_tac [||] tac taci

(* Apply [tac i] on the ith subgoal (no subgoals number check) *)
let thensi_tac tac (sigr,gs,p) =
  let gll,pl =
    List.split (list_map_i (fun i -> apply_sig_tac sigr (tac i)) 1 gs) in
  (sigr, List.flatten gll, compose p (mapshape (List.map List.length gll) pl))

let then_tac tac = thensf_tac [||] tac

let non_existent_goal n =
  errorlabstrm ("No such goal: "^(string_of_int n))
    (str"Trying to apply a tactic to a non existent goal")

(* Apply tac on the i-th goal (if i>0). If i<0, then start counting from
   the last goal (i=-1). *)
let theni_tac i tac ((_,gl,_) as subgoals) =
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

(* various progress criterions *)
let same_goal gl subgoal =
  eq_constr (conclusion subgoal) (conclusion gl) &&
  eq_named_context_val (hypotheses subgoal) (hypotheses gl)


let weak_progress gls ptree =
  (List.length gls.it <> 1) ||
  (not (same_goal (List.hd gls.it) ptree.it))

let progress gls ptree =
  (progress_evar_map ptree.sigma gls.sigma) ||
  (weak_progress gls ptree)


(* PROGRESS tac ptree applies tac to the goal ptree and fails if tac leaves
the goal unchanged *)
let tclPROGRESS tac ptree =
  let rslt = tac ptree in
  if progress (fst rslt) ptree then rslt
  else errorlabstrm "Refiner.PROGRESS" (str"Failed to progress.")

(* weak_PROGRESS tac ptree applies tac to the goal ptree and fails
   if tac leaves the goal unchanged, possibly modifying sigma *)
let tclWEAK_PROGRESS tac ptree =
  let rslt = tac ptree in
  if weak_progress (fst rslt) ptree then rslt
  else errorlabstrm "Refiner.tclWEAK_PROGRESS" (str"Failed to progress.")


(* Same as tclWEAK_PROGRESS but fails also if tactics generates several goals,
   one of them being identical to the original goal *)
let tclNOTSAMEGOAL (tac : tactic) goal =
  let rslt = tac goal in
  let gls = (fst rslt).it in
  if List.exists (same_goal goal.it) gls
  then errorlabstrm "Refiner.tclNOTSAMEGOAL"
      (str"Tactic generated a subgoal identical to the original goal.")
  else rslt

let catch_failerror e =
  if catchable_exception e then check_for_interrupt ()
  else match e with
  | FailError (0,_) | Stdpp.Exc_located(_, FailError (0,_))
  | Stdpp.Exc_located(_, LtacLocated (_,FailError (0,_)))  ->
      check_for_interrupt ()
  | FailError (lvl,s) -> raise (FailError (lvl - 1, s))
  | Stdpp.Exc_located(s,FailError (lvl,s')) ->
      raise (Stdpp.Exc_located(s,FailError (lvl - 1, s')))
  | Stdpp.Exc_located(s,LtacLocated (s'',FailError (lvl,s')))  ->
      raise
       (Stdpp.Exc_located(s,LtacLocated (s'',FailError (lvl - 1,s'))))
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
    | Some (sgl,v) ->
        let (sigr,gl) = unpackage sgl in
        finish_tac (then_tac t2then  (sigr,gl,v))

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


(* Beware: call by need of CAML, g is needed *)
let rec tclREPEAT t g =
  tclORELSE_THEN t (tclREPEAT t) tclIDTAC g

let tclAT_LEAST_ONCE t = (tclTHEN t (tclREPEAT t))

(* Repeat on the first subgoal (no failure if no more subgoal) *)
let rec tclREPEAT_MAIN t g =
  (tclORELSE (tclTHEN_i t (fun i -> if i = 1 then (tclREPEAT_MAIN t) else
    tclIDTAC)) tclIDTAC) g

(*s Tactics handling a list of goals. *)

type validation_list = proof_tree list -> proof_tree list

type tactic_list = (goal list sigma) -> (goal list sigma) * validation_list

(* Functions working on goal list for correct backtracking in Prolog *)

let tclFIRSTLIST = tclFIRST
let tclIDTAC_list gls = (gls, fun x -> x)

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
      let (gl,p) = apply_sig_tac sigr tac g1 in
      let n = List.length gl in
      (repackage sigr (gl@rest),
       fun pfl -> let (pfg,pfrest) = list_chop n pfl in (p pfg)::pfrest)
  | _ -> error "apply_tac_list"

let then_tactic_list tacl1 tacl2 glls =
  let (glls1,pl1) = tacl1 glls in
  let (glls2,pl2) = tacl2 glls1 in
  (glls2, compose pl1 pl2)

(* Transform a tactic_list into a tactic *)

let tactic_list_tactic tac gls =
    let (glres,vl) = tac (goal_goal_list gls) in
    (glres, compose idtac_valid vl)



(* The type of proof-trees state and a few utilities
   A proof-tree state is built from a proof-tree, a set of global
   constraints, and a stack which allows to navigate inside the
   proof-tree remembering how to rebuild the global proof-tree
   possibly after modification of one of the focused children proof-tree.
   The number in the stack corresponds to
   either the selected subtree and the validation is a function from a
   proof-tree list consisting only of one proof-tree to the global
   proof-tree
   or -1 when the move is done behind a registered tactic in which
   case the validation corresponds to a constant function giving back
   the original proof-tree. *)

type pftreestate = {
  tpf      : proof_tree ;
  tpfsigma : evar_map;
  tstack   : (int * validation) list }

let proof_of_pftreestate pts = pts.tpf
let is_top_pftreestate pts = pts.tstack = []
let cursor_of_pftreestate pts = List.map fst pts.tstack
let evc_of_pftreestate pts = pts.tpfsigma

let top_goal_of_pftreestate pts =
  { it = goal_of_proof pts.tpf; sigma = pts.tpfsigma }

let nth_goal_of_pftreestate n pts =
  let goals = fst (frontier pts.tpf) in
  try {it = List.nth goals (n-1); sigma = pts.tpfsigma }
  with Invalid_argument _ | Failure _ -> non_existent_goal n

let traverse n pts = match n with
  | 0 -> (* go to the parent *)
      (match  pts.tstack with
	 | [] -> error "traverse: no ancestors"
	 | (_,v)::tl ->
             let pf = v [pts.tpf] in
             let pf = norm_evar_proof pts.tpfsigma pf in
	     { tpf = pf;
	       tstack = tl;
	       tpfsigma = pts.tpfsigma })
  | -1 -> (* go to the hidden tactic-proof, if any, otherwise fail *)
      (match pts.tpf.ref with
	 | Some (Nested (_,spf),_) ->
	     let v = (fun pfl -> pts.tpf) in
	     { tpf = spf;
               tstack = (-1,v)::pts.tstack;
               tpfsigma = pts.tpfsigma }
	 | _ -> error "traverse: not a tactic-node")
  | n -> (* when n>0, go to the nth child *)
      let (npf,v) = descend n pts.tpf in
      { tpf = npf;
        tpfsigma = pts.tpfsigma;
        tstack = (n,v):: pts.tstack }

let change_constraints_pftreestate newgc pts = { pts with tpfsigma = newgc }

let app_tac sigr tac p =
  let (gll,v) = tac {it=p.goal;sigma= !sigr} in
  sigr := gll.sigma;
  v (List.map leaf gll.it)

(* modify proof state at current position *)

let map_pftreestate f pts =
  let sigr = ref pts.tpfsigma in
  let tpf' = f sigr pts.tpf in
  let tpf'' =
    if !sigr == pts.tpfsigma then tpf' else norm_evar_proof !sigr tpf' in
  { tpf      = tpf'';
    tpfsigma = !sigr;
    tstack   = pts.tstack }

(* solve the nth subgoal with tactic tac *)

let solve_nth_pftreestate n tac =
  map_pftreestate
    (fun sigr pt -> frontier_map (app_tac sigr tac) n pt)

let solve_pftreestate = solve_nth_pftreestate 1

(* This function implements a poor man's undo at the current goal.
   This is a gross approximation as it does not attempt to clean correctly
   the global constraints given in tpfsigma. *)

let weak_undo_pftreestate pts =
  let pf = leaf pts.tpf.goal in
  { tpf = pf;
    tpfsigma = pts.tpfsigma;
    tstack = pts.tstack }

(* Gives a new proof (a leaf) of a goal gl *)
let mk_pftreestate g =
  { tpf      = leaf g;
    tstack   = [];
    tpfsigma = Evd.empty }

(* Extracts a constr from a proof-tree state ; raises an error if the
   proof is not complete or the state does not correspond to the head
   of the proof-tree *)

let extract_open_pftreestate pts =
  extract_open_proof pts.tpfsigma pts.tpf

let extract_pftreestate pts =
  if pts.tstack <> [] then
    errorlabstrm "extract_pftreestate" (str"Proof blocks need to be closed");
  let pfterm,subgoals = extract_open_pftreestate pts in
  let exl = Evarutil.non_instantiated pts.tpfsigma in
  if subgoals <> [] or exl <> [] then
    errorlabstrm "extract_proof"
      (if subgoals <> [] then
        str "Attempt to save an incomplete proof"
      else
        str "Attempt to save a proof with existential variables still non-instantiated");
  let env = Global.env_of_context pts.tpf.goal.evar_hyps in
  nf_betaiota_preserving_vm_cast env pts.tpfsigma pfterm
  (* strong whd_betaiotaevar env pts.tpfsigma pfterm *)
  (***
  local_strong (Evarutil.whd_ise (ts_it pts.tpfsigma)) pfterm
  ***)
(* Focus on the first leaf proof in a proof-tree state *)

let rec first_unproven pts =
  let pf = (proof_of_pftreestate pts) in
  if is_complete_proof pf then
    errorlabstrm "first_unproven" (str"No unproven subgoals");
  if is_leaf_proof pf then
    pts
  else
    let childnum =
      list_try_find_i
	(fun n pf ->
	   if not(is_complete_proof pf) then n else failwith "caught")
	1 (children_of_proof pf)
    in
    first_unproven (traverse childnum pts)

(* Focus on the last leaf proof in a proof-tree state *)

let rec last_unproven pts =
  let pf = proof_of_pftreestate pts in
  if is_complete_proof pf then
    errorlabstrm "last_unproven" (str"No unproven subgoals");
  if is_leaf_proof pf then
    pts
  else
    let children = (children_of_proof pf) in
    let nchilds = List.length children in
    let childnum =
      list_try_find_i
        (fun n pf ->
           if not(is_complete_proof pf) then n else failwith "caught")
        1 (List.rev children)
    in
    last_unproven (traverse (nchilds-childnum+1) pts)

let rec nth_unproven n pts =
  let pf = proof_of_pftreestate pts in
  if is_complete_proof pf then
    errorlabstrm "nth_unproven" (str"No unproven subgoals");
  if is_leaf_proof pf then
    if n = 1 then
      pts
    else
      errorlabstrm "nth_unproven" (str"Not enough unproven subgoals")
  else
    let children = children_of_proof pf in
    let rec process i k = function
      | [] ->
	  errorlabstrm "nth_unproven" (str"Not enough unproven subgoals")
      | pf1::rest ->
	  let k1 = nb_unsolved_goals pf1 in
	  if k1 < k then
	    process (i+1) (k-k1) rest
	  else
	    nth_unproven k (traverse i pts)
    in
    process 1 n children

let rec node_prev_unproven loc pts =
  let pf = proof_of_pftreestate pts in
  match cursor_of_pftreestate pts with
    | [] -> last_unproven pts
    | n::l ->
	if is_complete_proof pf or loc = 1 then
          node_prev_unproven n (traverse 0 pts)
	else
	  let child = List.nth (children_of_proof pf) (loc - 2) in
	  if is_complete_proof child then
	    node_prev_unproven (loc - 1) pts
	  else
	    first_unproven (traverse (loc - 1) pts)

let rec node_next_unproven loc pts =
  let pf = proof_of_pftreestate pts in
  match cursor_of_pftreestate pts with
    | [] -> first_unproven pts
    | n::l ->
	if is_complete_proof pf ||
           loc = (List.length (children_of_proof pf)) then
             node_next_unproven n (traverse 0 pts)
	else if is_complete_proof (List.nth (children_of_proof pf) loc) then
	  node_next_unproven (loc + 1) pts
	else
	  last_unproven(traverse (loc + 1) pts)

let next_unproven pts =
  let pf = proof_of_pftreestate pts in
  if is_leaf_proof pf then
    match cursor_of_pftreestate pts with
      | [] -> error "next_unproven"
      | n::_ -> node_next_unproven n (traverse 0 pts)
  else
    node_next_unproven (List.length (children_of_proof pf)) pts

let prev_unproven pts =
  let pf = proof_of_pftreestate pts in
  if is_leaf_proof pf then
    match cursor_of_pftreestate pts with
      | [] -> error "prev_unproven"
      | n::_ -> node_prev_unproven n (traverse 0 pts)
  else
    node_prev_unproven 1 pts

let rec top_of_tree pts =
  if is_top_pftreestate pts then pts else top_of_tree(traverse 0 pts)

(* FIXME: cette fonction n'est (as of October 2007) appelée nulle part *)
let change_rule f pts =
  let mark_top _ pt =
    match pt.ref with
	Some (oldrule,l) ->
	  {pt with ref=Some (f oldrule,l)}
      | _ -> invalid_arg "change_rule" in
    map_pftreestate mark_top pts

let match_rule p pts =
  match (proof_of_pftreestate pts).ref with
      Some (r,_) -> p r
    | None -> false

let rec up_until_matching_rule p pts =
  if is_top_pftreestate pts then
    raise Not_found
  else
    let one_up = traverse 0 pts in
      if match_rule p one_up then
	pts
      else
	up_until_matching_rule p one_up

let rec up_to_matching_rule p pts =
  if match_rule p pts then
    pts
  else
    if is_top_pftreestate pts then
      raise Not_found
    else
      let one_up = traverse 0 pts in
      	up_to_matching_rule p one_up

(* Change evars *)
let tclEVARS sigma gls = tclIDTAC {gls with sigma=sigma}

(* Pretty-printers. *)

let pp_info = ref (fun _ _ _ -> assert false)
let set_info_printer f = pp_info := f

let tclINFO (tac : tactic) gls =
  let (sgl,v) as res = tac gls in
  begin try
    let pf = v (List.map leaf (sig_it sgl)) in
    let sign = named_context_of_val (sig_it gls).evar_hyps in
    msgnl (hov 0 (str" == " ++
                  !pp_info (project gls) sign pf))
  with e when catchable_exception e ->
    msgnl (hov 0 (str "Info failed to apply validation"))
  end;
  res

let pp_proof = ref (fun _ _ _ -> assert false)
let set_proof_printer f = pp_proof := f

let print_pftreestate {tpf = pf; tpfsigma = sigma; tstack = stack } =
  (if stack = []
   then str "Rooted proof tree is:"
   else (str "Proof tree at occurrence [" ++
         prlist_with_sep (fun () -> str ";") (fun (n,_) -> int n)
           (List.rev stack) ++ str "] is:")) ++ fnl() ++
  !pp_proof sigma (Global.named_context()) pf ++
  Evd.pr_evar_map sigma

(* Check that holes in arguments have been resolved *)

let check_evars env sigma evm gl =
  let origsigma = gl.sigma in
  let rest =
    Evd.fold (fun ev evi acc ->
      if not (Evd.mem origsigma ev) && not (Evd.is_defined sigma ev)
      then Evd.add acc ev evi else acc)
      evm Evd.empty
  in
  if rest <> Evd.empty then
    let (evk,evi) = List.hd (Evd.to_list rest) in
    let (loc,k) = evar_source evk rest in
    let evi = Evarutil.nf_evar_info sigma evi in
    Pretype_errors.error_unsolvable_implicit loc env sigma evi k None

let tclWITHHOLES accept_unresolved_holes tac sigma c gl =
  if sigma == project gl then tac c gl
  else
    let res = tclTHEN (tclEVARS sigma) (tac c) gl in
    if not accept_unresolved_holes then
      check_evars (pf_env gl) (fst res).sigma sigma gl;
    res
