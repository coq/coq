(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util
open Stamps
open Term
open Sign
open Evd
open Sign
open Environ
open Reduction
open Instantiate
open Type_errors
open Proof_trees
open Proof_type
open Logic

type transformation_tactic = proof_tree -> (goal list * validation)

let hypotheses gl = gl.evar_hyps
let conclusion gl = gl.evar_concl

let sig_it x = x.it
let sig_sig x = x.sigma


let project_with_focus gls = rc_of_gc (gls.sigma) (gls.it)

let pf_status pf = pf.status

let is_complete pf = (Complete_proof = (pf_status pf))

let on_open_proofs f pf = if is_complete pf then pf else f pf

let rec and_status = function
  | [] -> Complete_proof
  | Complete_proof :: l -> and_status l
  | _ -> Incomplete_proof

(* Normalizing evars in a goal. Called by tactic Local_constraints
   (i.e. when the sigma of the proof tree changes) *)

let norm_goal sigma gl =
  let red_fun = Evarutil.nf_evar sigma in
  let ncl = red_fun gl.evar_concl in
  { evar_concl = ncl;
    evar_hyps = map_named_context red_fun gl.evar_hyps;
    evar_body = gl.evar_body;
    evar_info = gl.evar_info }


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
            if p'.goal = p.goal then 
	      p'
            else 
	      errorlabstrm "Refiner.frontier"
                [< 'sTR"frontier was handed back a ill-formed proof." >]))
    | Some(r,pfl) ->
    	let gll,vl = List.split(List.map frontier pfl) in
    	(List.flatten gll,
         (fun retpfl ->
            let pfl' = mapshape (List.map List.length gll) vl retpfl in
            { status = and_status (List.map pf_status pfl');
              subproof = p.subproof;
              goal = p.goal;
              ref = Some(r,pfl')}))

(* [list_pf p] is the lists of goals to be solved in order to complete the
   proof [p] *)

let list_pf p = fst (frontier p)

let rec nb_unsolved_goals pf = 
  if is_complete pf then 
    0 
  else if is_leaf_proof pf then 
    1 
  else 
    let lpf = children_of_proof pf in 
    List.fold_left (fun n pf1 -> n + nb_unsolved_goals pf1) 0 lpf

(* leaf g is the canonical incomplete proof of a goal g *)

let leaf g = {
  status = Incomplete_proof;
  subproof = None;
  goal = g;
  ref = None }

(* Tactics table. *)

let tac_tab = Hashtbl.create 17

let add_tactic s t =
  if Hashtbl.mem tac_tab s then
    errorlabstrm ("Refiner.add_tactic: "^s) 
      [<'sTR "Cannot redeclare a tactic.">];
  Hashtbl.add tac_tab s t

let overwriting_add_tactic s t =
  if Hashtbl.mem tac_tab s then begin
    Hashtbl.remove tac_tab s;
    warning ("Overwriting definition of tactic "^s)
  end;
  Hashtbl.add tac_tab s t

let lookup_tactic s =
  try 
    Hashtbl.find tac_tab s
  with Not_found -> 
    errorlabstrm "Refiner.lookup_tactic"
      [< 'sTR"The tactic " ; 'sTR s ; 'sTR" is not installed" >]


(* refiner r is a tactic applying the rule r *)

let bad_subproof () =
  anomalylabstrm "Refiner.refiner" [< 'sTR"Bad subproof in validation.">]

let check_subproof_connection gl spfl =
  if not (list_for_all2eq (fun g pf -> g=pf.goal) gl spfl)
  then (bad_subproof (); false) else true

let refiner = function
  | Prim pr as r ->
      let prim_fun = prim_refiner pr in
      (fun goal_sigma ->
         let sgl = prim_fun (ts_it goal_sigma.sigma) goal_sigma.it in 
	 ({it=sgl; sigma = goal_sigma.sigma},
          (fun spfl ->
	     assert (check_subproof_connection sgl spfl);
             { status = and_status (List.map pf_status spfl);
               goal = goal_sigma.it;
               subproof = None;
               ref = Some(r,spfl) })))
      
  | Tactic(s,targs) as r ->
      let tacfun = lookup_tactic s targs in
      (fun goal_sigma ->
         let (sgl_sigma,v) = tacfun goal_sigma in
         let hidden_proof = v (List.map leaf sgl_sigma.it) in
         (sgl_sigma,
          fun spfl ->
	    assert (check_subproof_connection sgl_sigma.it spfl);
            { status = and_status (List.map pf_status spfl);
              goal = goal_sigma.it;
              subproof = Some hidden_proof;
              ref = Some(r,spfl) }))
      
  | (Context ctxt) as r ->
      (fun goal_sigma ->
         let gl = goal_sigma.it in
         let sg = mk_goal ctxt gl.evar_hyps gl.evar_concl in
         ({it=[sg];sigma=goal_sigma.sigma},
          (fun spfl -> 
	     assert (check_subproof_connection [sg] spfl);
             { status = (List.hd spfl).status;
               goal = gl;
               subproof = None;
               ref = Some(r,spfl) })))

   (* [Local_constraints lc] makes the local constraints be [lc] and
      normalizes evars *)

  | (Local_constraints lc) as r ->
      (fun goal_sigma ->
         let gl = goal_sigma.it in
         let ctxt = set_lc lc (out_some gl.evar_info) in 
         let sg = mk_goal ctxt gl.evar_hyps gl.evar_concl in
	 let sgl = [norm_goal (ts_it goal_sigma.sigma) sg] in
	 ({it=sgl;sigma=goal_sigma.sigma},
          (fun spfl -> 
	    assert (check_subproof_connection sgl spfl);
             { status = (List.hd spfl).status;
               goal = gl;
               subproof = None;
               ref = Some(r,spfl) })))

let context ctxt = refiner (Context ctxt)
let vernac_tactic texp = refiner (Tactic texp)
let norm_evar_tac gl = refiner (Local_constraints (get_lc gl.it)) gl

(* [rc_of_pfsigma : proof sigma -> readable_constraints] *)
let rc_of_pfsigma sigma = rc_of_gc sigma.sigma sigma.it.goal

(* [rc_of_glsigma : proof sigma -> readable_constraints] *)
let rc_of_glsigma sigma = rc_of_gc sigma.sigma sigma.it

(* [extract_open_proof : proof_tree -> constr * (int * constr) list]
  takes a (not necessarly complete) proof and gives a pair (pfterm,obl)
  where pfterm is the constr corresponding to the proof
  and [obl] is an [int*constr list] [ (m1,c1) ; ... ; (mn,cn)]
  where the mi are metavariables numbers, and ci are their types.
  Their proof should be completed in order to complete the initial proof *)

let extract_open_proof sigma pf =
  let meta_cnt = ref 0 in
  let open_obligations = ref [] in
  let rec proof_extractor vl = function
    | {ref=Some(Prim _,_)} as pf -> prim_extractor proof_extractor vl pf
	  
    | {ref=Some(Tactic _,spfl); subproof=Some hidden_proof} ->
	let sgl,v = frontier hidden_proof in
	let flat_proof = v spfl in
	proof_extractor vl flat_proof
	  
    | {ref=Some(Context ctxt,[pf])} -> (proof_extractor vl) pf
	  
    | {ref=Some(Local_constraints lc,[pf])} -> (proof_extractor vl) pf
	  
    | {ref=None;goal=goal} ->
	let visible_rels =
          map_succeed
            (fun id ->
               try let n = list_index id vl in (n,id)
	       with Not_found -> failwith "caught")
            (ids_of_named_context goal.evar_hyps) in
	let sorted_rels =
	  Sort.list (fun (n1,_) (n2,_) -> n1 > n2 ) visible_rels in
	let abs_concl =
          List.fold_right
            (fun (_,id) concl ->
	       let (c,ty) = lookup_id id goal.evar_hyps in
	       mkNamedProd_or_LetIn (id,c,ty) concl)
            sorted_rels goal.evar_concl	in
        incr meta_cnt;
	open_obligations := (!meta_cnt,abs_concl):: !open_obligations;
	applist
          (mkMeta !meta_cnt, List.map (fun (n,_) -> mkRel n) sorted_rels) 
	  
    | _ -> anomaly "Bug : a case has been forgotten in proof_extractor"
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
  let glsigma,v = tac (repackage r g) in 
  r := glsigma.sigma;
  (glsigma.it,v)

let idtac_valid = function
    [pf] -> pf
  | _ -> anomaly "Refiner.idtac_valid"

(* [goal_goal_list : goal sigma -> goal list sigma] *)
let goal_goal_list gls = {it=[gls.it];sigma=gls.sigma}

(* the identity tactic *)
let tclIDTAC gls = (goal_goal_list gls, idtac_valid)

(* General failure tactic *)
let tclFAIL_s s gls = errorlabstrm "Refiner.tclFAIL_s" [< 'sTR s>]

(* A special exception for levels for the Fail tactic *)
exception FailError of int

(* The Fail tactic *)
let tclFAIL lvl g = raise (FailError lvl)

let start_tac gls =
  let (sigr,g) = unpackage gls in
  (sigr,[g],idtac_valid)

let finish_tac (sigr,gl,p) = (repackage sigr gl, p)

let thens_tac tac2l taci (sigr,gs,p) =
  let (gl,gi) =
    try list_chop (List.length tac2l) gs
    with Failure _ -> errorlabstrm "Refiner.combine_tactics"
        [<'sTR "Wrong number of tactics.">] in
  let tac2gl =
    List.combine gl tac2l @ list_map_i (fun i g -> (g, taci i)) 1 gi in
  let gll,pl =
    List.split(List.map (fun (g,tac2) -> apply_sig_tac sigr tac2 g) tac2gl) in
  (sigr, List.flatten gll,
   compose p (mapshape (List.map List.length gll) pl))

let then_tac tac = thens_tac [] (fun _ -> tac)


let non_existent_goal n =
  errorlabstrm ("No such goal: "^(string_of_int n))
    [< 'sTR"Trying to apply a tactic to a non existent goal" >]

(* Apply tac on the i-th goal (if i>0). If i<0, then start counting from
   the last goal (i=-1). *)
let theni_tac i tac ((_,gl,_) as subgoals) =
  let nsg = List.length gl in
  let k = if i < 0 then nsg + i + 1 else i in
  if nsg < 1 then errorlabstrm "theni_tac" [< 'sTR"No more subgoals.">]
  else if k >= 1 & k <= nsg then
    thens_tac [] (fun i -> if i = k then tac else tclIDTAC) subgoals
  else non_existent_goal k 

(* [tclTHENSi tac1 [t1 ; ... ; tn] taci gls] applies the tactic [tac1]
   to [gls] and applies [t1], ..., [tn] to the [n] first resulting
   subgoals, and [(taci i)] to the (i+n)-th goal. Raises an error if
   the number of resulting subgoals is less than [n] *)
let tclTHENSi tac1 tac2l taci gls =
  finish_tac (thens_tac tac2l taci (then_tac tac1 (start_tac gls)))


(* [tclTHEN tac1 tac2 gls] applies the tactic [tac1] to [gls] and applies
   [tac2] to every resulting subgoals *)
let tclTHEN tac1 tac2 = tclTHENSi tac1 [] (fun _ -> tac2)

(* [tclTHEN_i tac1 tac2 gls] applies the tactic [tac1] to [gls] and applies
   [(tac2 i)] to the i_th resulting subgoal (starting from 1) *)
let tclTHEN_i tac1 tac2 = tclTHENSi tac1 [] tac2

(* [tclTHENS tac1 [t1 ; ... ; tn] gls] applies the tactic [tac1] to
   [gls] and applies [t1],..., [tn] to the [n] resulting subgoals. Raises
   an error if the number of resulting subgoals is not [n] *)
let tclTHENS tac1 tac2l =
  tclTHENSi tac1 tac2l (fun _ -> tclFAIL_s "Wrong number of tactics.")

(* Same as [tclTHENS] but completes with [tac3] if the number resulting 
   subgoals is strictly less than [n] *)
let tclTHENST tac1 tac2l tac3 = tclTHENSi tac1 tac2l (fun _ -> tac3)

(* Same as tclTHENST but completes with [Idtac] *)
let tclTHENSI tac1 tac2l = tclTHENST tac1 tac2l tclIDTAC

(* [tclTHENL tac1 tac2 gls] applies the tactic [tac1] to [gls] and [tac2]
   to the last resulting subgoal *)
let tclTHENL (tac1 : tactic) (tac2 : tactic) (gls : goal sigma) =
  finish_tac (theni_tac (-1) tac2 (then_tac tac1 (start_tac gls)))


(* [tclTHENLIST [t1;..;tn]] applies [t1] then [t2] ... then [tn]. More
   convenient than [tclTHEN] when [n] is large. *)
let rec tclTHENLIST = function
    [] -> tclIDTAC
  | t1::tacl -> tclTHEN t1 (tclTHENLIST tacl)




(* various progress criterions *)
let same_goal gl subgoal = 
  (hypotheses subgoal) = (hypotheses gl) &
  eq_constr (conclusion subgoal) (conclusion gl) &
  (subgoal.evar_info = gl.evar_info)


let weak_progress gls ptree =
  (List.length gls.it <> 1) or 
  (not (same_goal (List.hd gls.it) ptree.it))


let progress gls ptree =
  (weak_progress gls ptree) or
  (not (ts_eq ptree.sigma gls.sigma))


(* PROGRESS tac ptree applies tac to the goal ptree and fails if tac leaves
the goal unchanged *)
let tclPROGRESS tac ptree =
  let rslt = tac ptree in
  if progress (fst rslt) ptree then rslt
  else errorlabstrm "Refiner.PROGRESS" [< 'sTR"Failed to progress.">]

(* weak_PROGRESS tac ptree applies tac to the goal ptree and fails 
   if tac leaves the goal unchanged, possibly modifying sigma *)
let tclWEAK_PROGRESS tac ptree =
  let rslt = tac ptree in
  if weak_progress (fst rslt) ptree then rslt
  else errorlabstrm "Refiner.tclWEAK_PROGRESS" [< 'sTR"Failed to progress.">]


(* Same as tclWEAK_PROGRESS but fails also if tactics generates several goals,
   one of them being identical to the original goal *)
let tclNOTSAMEGOAL (tac : tactic) goal =
  let rslt = tac goal in
  let gls = (fst rslt).it in
  if List.exists (same_goal goal.it) gls
  then errorlabstrm "Refiner.tclNOTSAMEGOAL" 
      [< 'sTR"Tactic generated a subgoal identical to the original goal.">]
  else rslt



(* ORELSE0 t1 t2 tries to apply t1 and if it fails, applies t2 *)
let tclORELSE0 t1 t2 g =
  try 
    t1 g
  with
  | e when catchable_exception e -> t2 g
  | FailError lvl ->
    if lvl = 0 then
      t2 g
    else
      raise (FailError (lvl - 1))

(* ORELSE t1 t2 tries to apply t1 and if it fails or does not progress, 
   then applies t2 *)
let tclORELSE t1 t2 = tclORELSE0 (tclPROGRESS t1) t2

(* TRY f tries to apply f, and if it fails, leave the goal unchanged *)
let tclTRY f = (tclORELSE0 f tclIDTAC)

let tclTHENTRY f g = (tclTHEN f (tclTRY g))

(* Try the first tactic that does not fail in a list of tactics *)

let rec tclFIRST = function
  | [] -> tclFAIL_s "No applicable tactic."
  |  t::rest -> tclORELSE0 t (tclFIRST rest)



(* Fails if a tactic did not solve the goal *)
let tclCOMPLETE tac = tclTHEN tac (tclFAIL_s "Proof is not complete.")

(* Try the first thats solves the current goal *)
let tclSOLVE tacl = tclFIRST (List.map tclCOMPLETE tacl)

			   
(* Iteration tacticals *)

let tclDO n t = 
  let rec dorec k = 
    if k < 0 then errorlabstrm "Refiner.tclDO"
      [<'sTR"Wrong argument : Do needs a positive integer.">];
    if k = 0 then tclIDTAC
    else if k = 1 then t else (tclTHEN t (dorec (k-1)))
  in 
  dorec n 

(* Beware: call by need of CAML, g is needed *)
let rec tclREPEAT t g =
  (tclORELSE (tclTHEN t (tclREPEAT t)) tclIDTAC) g

let tclAT_LEAST_ONCE t = (tclTHEN t (tclREPEAT t))

(* Repeat on the first subgoal *)
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




(* solve_subgoal :
     (global_constraints ref * goal list * validation -> 
         global_constraints ref * goal list * validation) -> 
      (proof_tree sigma -> proof_tree sigma)
   solve_subgoal tac pf_sigma applies the tactic tac at the nth subgoal of
   pf_sigma *)
let solve_subgoal tacl pf_sigma =
  let (sigr,pf) = unpackage pf_sigma in
  let gl,p = frontier pf in
  let r = tacl (sigr,gl,p) in
  let (sigr,gll,pl) =
    if (ts_it !sigr) == (ts_it pf_sigma.sigma) then r
    else then_tac norm_evar_tac r in
  repackage sigr (pl (List.map leaf gll))

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
  tpfsigma : global_constraints;
  tstack   : (int * validation) list }

let proof_of_pftreestate pts = pts.tpf
let is_top_pftreestate pts = pts.tstack = [] 
let cursor_of_pftreestate pts = List.map fst pts.tstack
let evc_of_pftreestate pts = ts_it pts.tpfsigma

let top_goal_of_pftreestate pts = 
  { it = goal_of_proof pts.tpf; sigma = pts.tpfsigma }

let nth_goal_of_pftreestate n pts =
  let goals = fst (frontier pts.tpf) in
  try {it = List.nth goals (n-1); sigma = pts.tpfsigma }
  with Failure "nth" -> non_existent_goal n

let descend n p =
  match p.ref with
    | None        -> error "It is a leaf."
    | Some(r,pfl) ->
    	if List.length pfl >= n then
	  (match list_chop (n-1) pfl with 
	     | left,(wanted::right) ->
		 (wanted,
		  (fun pfl' ->
                     if (List.length pfl' = 1) 
		       & (List.hd pfl').goal = wanted.goal 
		     then
                       let pf'       = List.hd pfl' in
                       let spfl      = left@(pf'::right) in
                       let newstatus = and_status (List.map pf_status spfl) in
                       { status   = newstatus;
			 goal     = p.goal;
			 subproof = p.subproof;
			 ref      = Some(r,spfl) }
                     else 
		       error "descend: validation"))
	     | _ -> assert false)
    	else 
	  error "Too few subproofs"

let traverse n pts = match n with 
  | 0 -> (* go to the parent *)
      (match  pts.tstack with
	 | [] -> error "traverse: no ancestors"
	 | (_,v)::tl ->
	     { tpf = v [pts.tpf];
	       tstack = tl;
	       tpfsigma = pts.tpfsigma })
  | -1 -> (* go to the hidden tactic-proof, if any, otherwise fail *)
      (match pts.tpf.subproof with
	 | None -> error "traverse: not a tactic-node"
	 | Some spf ->
	     let v = (fun pfl -> pts.tpf) in 
	     { tpf = spf;
               tstack = (-1,v)::pts.tstack;
               tpfsigma = pts.tpfsigma })
  | n -> (* when n>0, go to the nth child *)
      let (npf,v) = descend n pts.tpf in 
      { tpf = npf;
        tpfsigma = pts.tpfsigma;
        tstack = (n,v):: pts.tstack }

let change_constraints_pftreestate newgc pts = 
  { tpf = pts.tpf; tpfsigma = newgc; tstack = pts.tstack }

(* solve the nth subgoal with tactic tac *)
let solve_nth_pftreestate n tac pts =
 let rslts =
   solve_subgoal (theni_tac n tac) {it = pts.tpf;sigma = pts.tpfsigma}
 in
 { tpf      = rslts.it;
   tpfsigma = rslts.sigma;
   tstack   = pts.tstack }

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
    tpfsigma = ts_mk Evd.empty }

(* Extracts a constr from a proof-tree state ; raises an error if the
   proof is not complete or the state does not correspond to the head
   of the proof-tree *)

let extract_open_pftreestate pts =
  extract_open_proof (ts_it pts.tpfsigma) pts.tpf

let extract_pftreestate pts =
  if pts.tstack <> [] then
    errorlabstrm "extract_pftreestate"
      [< 'sTR"Cannot extract from a proof-tree in which we have descended;" ;
         'sPC; 'sTR"Please ascend to the root" >];
  let pfterm,subgoals = extract_open_pftreestate pts in
  if subgoals <> [] then
   errorlabstrm "extract_proof"
   [< 'sTR "Attempt to save an incomplete proof" >];
  let env = Global.env_of_context pts.tpf.goal.evar_hyps in
  strong whd_betaiotaevar env (ts_it pts.tpfsigma) pfterm
  (***  
  local_strong (whd_ise (ts_it pts.tpfsigma)) pfterm
  ***)
(* Focus on the first leaf proof in a proof-tree state *)

let rec first_unproven pts =
  let pf = (proof_of_pftreestate pts) in 
  if is_complete_proof pf then
    errorlabstrm "first_unproven" [< 'sTR"No unproven subgoals" >];
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
    errorlabstrm "last_unproven" [< 'sTR"No unproven subgoals" >];
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
    errorlabstrm "nth_unproven" [< 'sTR"No unproven subgoals" >];
  if is_leaf_proof pf then
    if n = 1 then 
      pts 
    else
      errorlabstrm "nth_unproven" [< 'sTR"Not enough unproven subgoals" >]
  else 
    let children = children_of_proof pf in
    let rec process i k = function
      | [] -> 
	  errorlabstrm "nth_unproven" [< 'sTR"Not enough unproven subgoals" >]
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


(* Pretty-printers. *)

open Pp
open Printer

let pr_tactic (s,l) =
  gentacpr (Ast.ope (s,(List.map ast_of_cvt_arg l)))

let pr_rule = function
  | Prim r -> pr_prim_rule r
  | Tactic texp -> hOV 0 (pr_tactic texp)
  | Context ctxt -> pr_ctxt ctxt
  | Local_constraints lc -> [< 'sTR"Local constraint change" >]

exception Different

(* We remove from the var context of env what is already in osign *)
let thin_sign osign sign =
  Sign.fold_named_context
    (fun (id,c,ty as d) sign ->
       try 
	 if lookup_id id osign = (c,ty) then sign
	 else raise Different
       with Not_found | Different -> add_named_decl d sign)
    sign empty_named_context

let rec print_proof sigma osign pf =
  let {evar_hyps=hyps; evar_concl=cl; 
       evar_info=info; evar_body=body} = pf.goal in
  let hyps' = thin_sign osign hyps in
  match pf.ref with
    | None -> 
	hOV 0 [< pr_seq {evar_hyps=hyps'; evar_concl=cl;
			 evar_info=info; evar_body=body} >]
    | Some(r,spfl) ->
    	hOV 0 [< hOV 0 (pr_seq {evar_hyps=hyps'; evar_concl=cl;
				evar_info=info; evar_body=body});
		 'sPC ; 'sTR" BY ";
		 hOV 0 [< pr_rule r >]; 'fNL ;
		 'sTR"  ";
		 hOV 0 (prlist_with_sep pr_fnl (print_proof sigma hyps) spfl)
              >]
	  
let pr_change gl = [< 'sTR"Change " ; prterm gl.evar_concl ; 'sTR"." ; 'fNL>]
		     
let rec print_script nochange sigma osign pf =
  let {evar_hyps=sign; evar_concl=cl} = pf.goal in
  match pf.ref with
    | None ->
        if nochange then 
	  [< 'sTR"<Your Tactic Text here>" >] 
	else 
	  pr_change pf.goal
    | Some(r,spfl) ->
        [< (if nochange then [< >] else (pr_change pf.goal));
           pr_rule r ; 'sTR"." ; 'fNL ;
           prlist_with_sep pr_fnl
             (print_script nochange sigma sign) spfl >]

let rec print_treescript sigma osign pf =
  let {evar_hyps=sign; evar_concl=cl} = pf.goal in
  match pf.ref with
    | None -> [< >]
    | Some(r,spfl) ->
        [< pr_rule r ; 'sTR"." ; 'fNL ;
           let prsub =
             prlist_with_sep pr_fnl (print_treescript sigma sign) spfl
           in
           if List.length spfl > 1 then 
	     [< 'sTR"  "; hOV 0 prsub >]
           else 
	     prsub 
	>]

let rec print_info_script sigma osign pf =
  let {evar_hyps=sign; evar_concl=cl} = pf.goal in
  match pf.ref with
    | None -> [< >]
    | Some(r,spfl) ->
        [< pr_rule r ; 
           match spfl with
             | [pf1] ->
                 if pf1.ref = None then 
		   [<'sTR "."; 'fNL >]
                 else 
		   [< 'sTR";" ; 'bRK(1,3) ;
		      print_info_script sigma sign pf1 >]
             | _ -> [< 'sTR"." ; 'fNL ;
                       prlist_with_sep pr_fnl
                         (print_info_script sigma sign) spfl >] >]

let format_print_info_script sigma osign pf = 
  hOV 0 (print_info_script sigma osign pf)
    
let print_subscript sigma sign pf = 
  if is_tactic_proof pf then 
    format_print_info_script sigma sign (subproof_of_proof pf)
  else 
    format_print_info_script sigma sign pf

let tclINFO (tac : tactic) gls = 
  let (sgl,v) as res = tac gls in 
  begin try 
    let pf = v (List.map leaf (sig_it sgl)) in
    let sign = (sig_it gls).evar_hyps in
    mSGNL(hOV 0 [< 'sTR" == "; 
                   print_subscript 
                     ((compose ts_it sig_sig) gls) sign pf >])
  with e when catchable_exception e -> 
    mSGNL(hOV 0 [< 'sTR "Info failed to apply validation" >])
  end;
  res
