
(* $Id$ *)

open Pp
open Util
open Stamps
open Generic
open Term
open Sign
open Evd
open Environ
open Reduction
open Instantiate
open Proof_trees
open Logic

type 'a sigma = { 
  it : 'a ; 
  sigma : global_constraints }

type validation = (proof_tree list -> proof_tree)
type tactic = goal sigma -> (goal list sigma * validation)
type transformation_tactic = proof_tree -> (goal list * validation)

let hypotheses gl = gl.evar_env
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

(* mapshape [ l1 ; ... ; lk ] [ v1 ; ... ; vk ] [ p_1 ; .... ; p_(l1+...+lk) ]
   gives
   [ (v1 [p_1 ... p_l1]) ; (v2 [ p_(l1+1) ... p_(l1+l2) ]) ; ... ;
   (vk [ p_(l1+...+l(k-1)+1) ... p_(l1+...lk) ]) ] *)

let rec mapshape nl (fl:(proof_tree list -> proof_tree) list) 
                    (l : proof_tree list) =
  match nl with
    | [] -> []
    | h::t ->
	let m,l = list_chop h l in 
	(List.hd fl m) :: (mapshape t (List.tl fl) l)

(* given a proof p, frontier p gives (l,v) where l is the list of goals
   to be solved to complete the proof, and v is the corresponding validation *)

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

(* list_pf p is the lists of goals to be solved in order to complete the
   proof p *)

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
  errorlabstrm "Refiner.refiner" [< 'sTR"Bad subproof in validation.">]

let refiner = function
  | Prim pr as r ->
      let prim_fun = prim_refiner pr in
      (fun goal_sigma ->
         let sgl = prim_fun (ts_it goal_sigma.sigma) goal_sigma.it in 
	 ({it=sgl; sigma = goal_sigma.sigma},
          (fun pfl ->
             if not (list_for_all2eq (fun g pf -> g = pf.goal) sgl pfl) then
	       bad_subproof ();
             { status = and_status (List.map pf_status pfl);
               goal = goal_sigma.it;
               subproof = None;
               ref = Some(r,pfl) })))
      
  | Tactic(s,targs) as r ->
      let tacfun = lookup_tactic s targs in
      (fun goal_sigma ->
         let (sgl_sigma,v) = tacfun goal_sigma in
         let hidden_proof = v (List.map leaf sgl_sigma.it) in
         (sgl_sigma,
          fun spfl ->
            if not (list_for_all2eq (fun g pf -> g=pf.goal) sgl_sigma.it spfl)
	    then bad_subproof ();
            { status = and_status (List.map pf_status spfl);
              goal = goal_sigma.it;
              subproof = Some hidden_proof;
              ref = Some(r,spfl) }))
      
  | (Context ctxt) as r ->
      (fun goal_sigma ->
         let gl = goal_sigma.it in
         let sg = mk_goal ctxt gl.evar_env gl.evar_concl in
         ({it=[sg];sigma=goal_sigma.sigma},
          (fun pfl -> 
	     let pf = List.hd pfl in
             if pf.goal <> sg then bad_subproof ();
             { status = pf.status;
               goal = gl;
               subproof = None;
               ref = Some(r,[pf]) })))
      
   (* [Local_constraints lc] makes the local constraints be [lc] *)

  | (Local_constraints lc) as r ->
      (fun goal_sigma ->
         let gl = goal_sigma.it  in
         let ctxt = gl.evar_info in 
         let sg = mk_goal ctxt gl.evar_env gl.evar_concl in
	 ({it=[sg];sigma=goal_sigma.sigma},
          (fun pfl -> 
	     let pf = List.hd pfl in
             if pf.goal <> sg then bad_subproof ();
             { status = pf.status;
               goal = gl;
               subproof = None;
               ref = Some(r,[pf]) })))


let context ctxt = refiner (Context ctxt)
let vernac_tactic texp = refiner (Tactic texp)

(* hide_tactic s tac pr registers a tactic s under the name s *)

let hide_tactic s tac =
  add_tactic s tac;
  (fun args -> vernac_tactic(s,args))

(* overwriting_register_tactic s tac pr registers a tactic s under the
   name s even if a tactic of the same name is already registered *)

let overwrite_hidden_tactic s tac =
  overwriting_add_tactic s tac;
  (fun args -> vernac_tactic(s,args))

(* rc_of_pfsigma : proof sigma -> readable_constraints *)
let rc_of_pfsigma sigma = rc_of_gc sigma.sigma sigma.it.goal

(* rc_of_glsigma : proof sigma -> readable_constraints *)
let rc_of_glsigma sigma = rc_of_gc sigma.sigma sigma.it

(* extract_open_proof : constr signature -> proof
  -> constr * (int * constr) list
  takes a constr signature corresponding to global definitions
  and a (not necessarly complete) proof
  and gives a pair (pfterm,obl)
  where pfterm is the constr corresponding to the proof
  and obl is an int*constr list [ (m1,c1) ; ... ; (mn,cn)]
  where the mi are metavariables numbers, and ci are their types.
  Their proof should be completed in order to complete the initial proof *)

let extract_open_proof sign pf =
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
	let rel_env = get_rels vl in
	let n_rels = List.length rel_env in
	let visible_rels =
          map_succeed
            (fun id ->
               match lookup_id id vl with
		 | GLOBNAME _ -> failwith "caught"
		 | RELNAME(n,_) -> (n,id))
            (ids_of_sign (evar_hyps goal)) in
	let sorted_rels = 
	  Sort.list (fun (n1,_) (n2,_) -> n1>n2) visible_rels in
	let abs_concl =
          List.fold_right
            (fun (_,id) concl ->
	       let (_,ty) = lookup_sign id (evar_hyps goal) in
	       mkNamedProd id (incast_type ty) concl)
            sorted_rels goal.evar_concl
	in
	let mv = new_meta() in
	open_obligations := (mv,abs_concl):: !open_obligations;
	applist(DOP0(Meta mv),List.map (fun (n,_) -> Rel n) sorted_rels) 
	  
    | _ -> anomaly "Bug : a case has been forgotten in proof_extractor"
  in
  let pfterm = proof_extractor (gLOB sign) pf in
  (pfterm, List.rev !open_obligations)
  
(* extracts a constr from a proof, and raises an error if the proof is
   incomplete *)

let extract_proof sign pf =
  match extract_open_proof sign pf with
    | t,[] -> t
    | _ -> errorlabstrm "extract_proof"
	  [< 'sTR "Attempt to save an incomplete proof" >]

(* whd_evar goes through existential variables when they are defined *)

let rec whd_evar env sigma k = 
  let (ev,_) = destEvar k in
  if Evd.is_defined sigma ev then 
    whd_evar env sigma (existential_value sigma k)
  else 
    k

(* expanses every existential constant and compute the normal form
   through beta iota reduction *)

let rec expand_evars env sigma c = 
  nf_betaiota env sigma (strong whd_evar env sigma c)


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

(* the identity tactic *)

let tclIDTAC gls = 
  { it = [gls.it]; sigma = gls.sigma },
  (function 
     | [pf] -> pf 
     | _ -> anomalylabstrm "Refiner.tclIDTAC"
	   [< 'sTR "tclIDTAC validation is applicable only to"; 'sPC;
	      'sTR "a one-proof list" >])

(* solve_subgoal n tac pf_sigma applies the tactic tac at the nth subgoal of
   pf_sigma *)

let non_existent_goal n =
  errorlabstrm ("No such goal: "^(string_of_int n))
    [< 'sTR"Trying to apply a tactic to a non existent goal" >]

let solve_subgoal n tac pf_sigma =
  let (sigr,pf) = unpackage pf_sigma in
  let gl,p = frontier pf in
  if gl = [] then errorlabstrm "solve_subgoal" [< 'sTR"No more subgoals.">];
  if List.length gl < n then non_existent_goal n;
  let tac2 i = if i = n then tac else tclIDTAC in
  let gll,pl = 
    List.split (list_map_i (fun n -> apply_sig_tac sigr (tac2 n)) 1 gl)
  in 
  repackage sigr (compose p (mapshape (List.map List.length gll) pl) 
                    (List.map leaf (List.flatten gll)))

(* tclTHEN tac1 tac2 gls applies the tactic tac1 to gls and applies tac2 to
   every resulting subgoals *)

let tclTHEN (tac1:tactic) (tac2:tactic) (gls:goal sigma) =
  let (sigr,g) = unpackage gls in
  let gl,p = apply_sig_tac sigr tac1 g in
  let gll,pl = List.split(List.map (apply_sig_tac sigr tac2) gl) in
  (repackage sigr (List.flatten gll), 
   compose p (mapshape(List.map List.length gll)pl))

(* tclTHEN_i tac1 tac2 n gls applies the tactic tac1 to gls and applies
   tac2 (i+n-1) to the i_th resulting subgoal *)

let tclTHEN_i (tac1:tactic) (tac2:(int -> tactic)) n (gls:goal sigma) =
  let (sigr,g) = unpackage gls in
  let gl,p = apply_sig_tac sigr tac1 g in
  let gll,pl = 
    List.split (list_map_i (fun k -> apply_sig_tac sigr (tac2 k)) n gl) 
  in
  (repackage sigr (List.flatten gll), 
   compose p (mapshape(List.map List.length gll)pl))

(* tclTHENS tac1 [t1 ; ... ; tn] gls applies the tactic tac1 to gls
   and applies t1,..., tn to the n resulting subgoals. Raises an error if
   the number of resulting subgoals is not n *)

let tclTHENS (tac1:tactic) (tac2l:tactic list) (gls:goal sigma) =
  let (sigr,g) = unpackage gls in
  let gl,p = apply_sig_tac sigr tac1 g  in
  let tac2gl = 
    try List.combine tac2l gl
    with Invalid_argument _ -> errorlabstrm "Refiner.tclTHENS"
        [<'sTR "Wrong number of tactics.">]
  in
  let gll,pl = 
    List.split (List.map (fun (tac2,g) -> apply_sig_tac sigr tac2 g) tac2gl)
  in
  (repackage sigr (List.flatten gll), 
   compose p (mapshape(List.map List.length gll)pl))

(* tclTHENL tac1 tac2 gls applies the tactic tac1 to gls and tac2
   to the last resulting subgoal *)

let tclTHENL (tac1:tactic) (tac2:tactic) (gls:goal sigma) =
  let (sigr,g) = unpackage gls in
  let gl,p = apply_sig_tac sigr tac1 g in 
  if List.length gl = 0 then
    errorlabstrm "Refiner.tclTHENL" [< 'sTR"No resulting subgoal.">];
  let g,rest = list_sep_last gl in
  let tac2l = (List.map (fun _ -> tclIDTAC) rest)@[tac2] in
  let tac2gl = 
    try List.combine tac2l gl
    with Invalid_argument _ -> errorlabstrm "Refiner.tclTHENL"
        [<'sTR "Wrong number of tactics.">]
  in
  let gll,pl = 
    List.split (List.map (fun (tac2,g) -> apply_sig_tac sigr tac2 g) tac2gl)
  in
  (repackage sigr (List.flatten gll), 
   compose p (mapshape(List.map List.length gll)pl))

(* Completes by Idtac if there is not tactic enough for tac1;[t1|...|tn] *)

let idtac_completion lac gl=
  let nl = ref lac
  and lthlac = List.length lac
  and lthgl = List.length gl in
  if lthlac > lthgl then failwith "idtac_completion";
  for i = 0 to lthgl-lthlac-1 do
    nl := !nl @ [tclIDTAC]
  done;
  !nl

(* Same as tclTHENS but completes with Idtac if the number resulting
  subgoals is strictly less than n *)

let tclTHENSI (tac1:tactic) (tac2l:tactic list) (gls:goal sigma) =
  let (sigr,g) = unpackage gls in
  let gl,p = apply_sig_tac sigr tac1 g  in
  let ntac2l=
    try (idtac_completion tac2l gl)
    with
	Failure "idtac_completion" ->
          errorlabstrm "Refiner.tclTHENSI" 
	    [<'sTR "Too many tactics for the generated subgoals.">]
  in
  let tac2gl = List.combine ntac2l gl in
  let gll,pl = 
    List.split (List.map (fun (tac2,g) -> apply_sig_tac sigr tac2 g) tac2gl)
  in
  (repackage sigr (List.flatten gll), 
   compose p (mapshape(List.map List.length gll)pl))

(* PROGRESS tac ptree applies tac to the goal ptree and fails if tac leaves
   the goal unchanged *)

let tclPROGRESS (tac:tactic) (ptree : goal sigma) =
  let rslt = tac ptree in 
  if (List.length (fst rslt).it) = 1 then begin
    let subgoal = List.hd (fst rslt).it in 
    if (hypotheses subgoal) = (hypotheses ptree.it) &&
       (conclusion subgoal) = (conclusion ptree.it) &&
       (subgoal.evar_info = ptree.it.evar_info) &&
       ts_eq ptree.sigma (fst rslt).sigma then
         errorlabstrm "Refiner.PROGRESS" [< 'sTR"Failed to progress.">];
    rslt
  end else 
    rslt

(* weak_PROGRESS tac ptree applies tac to the goal ptree and fails 
   if tac leaves the goal unchanged, possibly modifying sigma *)

let tclWEAK_PROGRESS (tac:tactic) (ptree : goal sigma) =
  let rslt = tac ptree in 
  if (List.length (fst rslt).it) = 1 then begin
    let subgoal = List.hd (fst rslt).it in 
    if (hypotheses subgoal) = (hypotheses ptree.it) &&
       eq_constr (conclusion subgoal) (conclusion ptree.it) &&
       (subgoal.evar_info = ptree.it.evar_info) then
         errorlabstrm "Refiner.tclWEAK_PROGRESS" 
	   [< 'sTR"Failed to progress.">];
    rslt
  end else 
    rslt

(* Same as tclWEAK_PROGRESS but fails also if tactics generates several goals,
   one of them being identical to the original goal *)

let tclNOTSAMEGOAL (tac:tactic) (ptree : goal sigma) =
  let rslt = tac ptree in 
  let gls = (fst rslt).it in 
  let same_goal subgoal = 
    (hypotheses subgoal) = (hypotheses ptree.it) &
    eq_constr (conclusion subgoal) (conclusion ptree.it) &
    (subgoal.evar_info = ptree.it.evar_info)
  in 
  if List.exists same_goal gls then 
    errorlabstrm "Refiner.tclNOTSAMEGOAL" 
      [< 'sTR"Tactic generated a subgoal identical to the original goal.">];
  rslt

(* ORELSE f1 f2 tries to apply f1 and if it fails, applies f2 *)

let tclORELSE (f1:tactic) (f2:tactic) (g:goal sigma) =
  try 
    (tclPROGRESS f1) g
  with UserError _ | Stdpp.Exc_located(_,UserError _) -> 
    f2 g 

(* TRY f tries to apply f, and if it fails, leave the goal unchanged *)

let tclTRY (f:tactic) = (tclORELSE f tclIDTAC)

let tclTHENTRY (f:tactic) (g:tactic) = (tclTHEN f (tclTRY g))

let tclCOMPLETE (tac:tactic) goal =
  let achievement = tac goal in 
  if (fst achievement).it <> [] then
    errorlabstrm "Refiner.COMPLETE" [< 'sTR "Proof is not complete" >];
  achievement

(* Beware: call by need of CAML, g is needed *)

let rec tclREPEAT = fun t g ->
  (tclORELSE (tclTHEN t (tclREPEAT t)) tclIDTAC) g

(*Try the first tactic that does not fail in a list of tactics*)

let rec tclFIRST = fun tacl g ->
  match tacl with
    | [] -> errorlabstrm "Refiner.tclFIRST" [< 'sTR"No applicable tactic.">]
    |  t::rest -> (try t g with UserError _ -> tclFIRST rest g)

(*Try the first thats solves the current goal*)

let tclSOLVE=fun tacl gls ->
  let (sigr,gl)=unpackage gls in
  let rec solve=function
    | [] -> errorlabstrm "Refiner.tclSOLVE" [< 'sTR"Cannot solve the goal.">]
    | e::tail ->
        (try
           let (ngl,p)=apply_sig_tac sigr e gl in
           if ngl = [] then
             (repackage sigr ngl,p)
           else
             solve tail
         with UserError _ -> 
	   solve tail)
  in
  solve tacl
  
let tclTRY t = (tclORELSE t tclIDTAC)
		 
let tclAT_LEAST_ONCE t = (tclTHEN t (tclREPEAT t))
			   
let (tclFAIL:tactic) = 
  fun _ -> errorlabstrm "Refiner.tclFAIL" [< 'sTR"Failtac always fails.">]

(* Iteration tactical *)

let tclDO n t = 
  let rec dorec k = 
    if k < 0 then errorlabstrm "Refiner.tclDO"
      [<'sTR"Wrong argument : Do needs a positive integer.">];
    if k = 0 then tclIDTAC
    else if k = 1 then t else (tclTHEN t (dorec (k-1)))
  in 
  dorec n 


(*s Tactics handling a list of goals. *)

type validation_list = proof_tree list -> proof_tree list

type tactic_list = (goal list sigma) -> (goal list sigma) * validation_list

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
    | g1::rest ->
	let (gl,p) = apply_sig_tac sigr tac g1 in
	let n = List.length gl in 
        repackage sigr (gl@rest), 
        (function pfl -> let (pfg,pfrest) = list_chop n pfl in (p pfg)::pfrest)
    | _ -> error "apply_tac_list"
	  
let then_tactic_list tacl1 tacl2 glls = 
  let (sigr,gl) = unpackage glls in
  let gll1,pl1 = apply_sig_tac sigr tacl1 gl in
  let gll2,pl2 = apply_sig_tac sigr tacl2 gll1 in
  (repackage sigr gll2, compose pl1 pl2)

(* Transform a tactic_list into a tactic *)

let tactic_list_tactic tac gls = 
  let glit = gls.it 
  and glsig = gls.sigma in 
  let (glres,vl) = tac {it=[glit];sigma=glsig} in 
  (glres, 
   fun pfl -> match (vl pfl) with [p] -> p | _ -> error "tactic_list_tactic")

(* Functions working on goal list for correct backtracking in Prolog *)

let tclFIRSTLIST = tclFIRST
let tclIDTAC_list gls = (gls, fun x -> x)


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
let evc_of_pftreestate pts = pts.tpfsigma

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
  let pf = pts.tpf in
  let rslts = solve_subgoal n tac {it = pts.tpf;sigma = pts.tpfsigma} in
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

let extract_pftreestate pts =
  if pts.tstack <> [] then
    errorlabstrm "extract_pftreestate"
      [< 'sTR"Cannot extract from a proof-tree in which we have descended;" ;
         'sPC; 'sTR"Please ascend to the root" >];
  let env = pts.tpf.goal.evar_env in
  let hyps = Environ.var_context env in
  strong whd_betadeltatiota env (ts_it pts.tpfsigma)
    (extract_proof hyps pts.tpf)


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

let thin_sign osign (x,y) =
  let com_nsign = List.combine x y in 
  List.split
    (map_succeed (fun (id,ty) ->
                    if (not (mem_sign osign id))
                      or (id,ty) <> (lookup_sign id osign) then
                        (id,ty)
                    else failwith "caught") com_nsign)

let rec print_proof sigma osign pf =
  let {evar_env=env; evar_concl=cl; 
       evar_info=info; evar_body=body} = pf.goal in
  let env' = change_hyps (fun sign -> thin_sign osign sign) env in
  match pf.ref with
    | None -> 
	hOV 0 [< pr_seq {evar_env=env'; evar_concl=cl;
			 evar_info=info; evar_body=body} >]
    | Some(r,spfl) ->
  	let sign = var_context env in
    	hOV 0 [< hOV 0 (pr_seq {evar_env=env'; evar_concl=cl;
				evar_info=info; evar_body=body});
		 'sPC ; 'sTR" BY ";
		 hOV 0 [< pr_rule r >]; 'fNL ;
		 'sTR"  ";
		 hOV 0 (prlist_with_sep pr_fnl (print_proof sigma sign) spfl)
              >]
	  
let pr_change gl = [< 'sTR"Change " ; prterm gl.evar_concl ; 'sTR"." ; 'fNL>]
		     
let rec print_script nochange sigma osign pf =
  let {evar_env=env; evar_concl=cl} = pf.goal in
  let sign = var_context env in
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
  let {evar_env=env; evar_concl=cl} = pf.goal in
  let sign = var_context env in
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
  let {evar_env=env; evar_concl=cl} = pf.goal in
  let sign = var_context env in
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

