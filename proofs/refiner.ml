
(* $Id$ *)

open Pp
open Util
open Stamps
open Generic
open Term
open Sign
open Evd
open Environ
open Proof_trees
open Logic

type 'a sigma = { 
  it : 'a ; 
  sigma : global_constraints }

type validation = (proof_tree list -> proof_tree)
type tactic = goal sigma -> (goal list sigma * validation)
type transformation_tactic = proof_tree -> (goal list * validation)
type validation_list = proof_tree list -> proof_tree list

type tactic_list = (goal list sigma) -> (goal list sigma) * validation_list

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

let refiner env = function
  | Prim pr as r ->
      let prim_fun = prim_refiner pr env in
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
      
  | ((Context ctxt) as r) ->
      (fun goal_sigma ->
         let gl = goal_sigma.it in
         let sg = mk_goal ctxt gl.evar_hyps gl.evar_concl in
         ({it=[sg];sigma=goal_sigma.sigma},
          (fun pfl -> 
	     let pf = List.hd pfl in
             if pf.goal <> sg then bad_subproof ();
             { status = pf.status;
               goal = gl;
               subproof = None;
               ref = Some(r,[pf]) })))
      
   (* [Local_constraints lc] makes the local constraints be [lc] *)

  | ((Local_constraints lc) as r) ->
      (fun goal_sigma ->
         let gl = goal_sigma.it  in
         let ctxt = gl.evar_info in 
         let sg = mk_goal ctxt gl.evar_hyps gl.evar_concl in
	 ({it=[sg];sigma=goal_sigma.sigma},
          (fun pfl -> 
	     let pf = List.hd pfl in
             if pf.goal <> sg then bad_subproof ();
             { status = pf.status;
               goal = gl;
               subproof = None;
               ref = Some(r,[pf]) })))

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
            (ids_of_sign goal.evar_hyps) in
	let sorted_rels = 
	  Sort.list (fun (n1,_) (n2,_) -> n1>n2) visible_rels in
	let abs_concl =
          List.fold_right
            (fun (_,id) concl -> 
	       mkNamedProd id (incast_type (snd(lookup_sign id goal.evar_hyps))) 
		 concl)
            sorted_rels goal.evar_concl
	in
	let mv = new_meta() in
	open_obligations := (mv,abs_concl):: !open_obligations;
	applist(DOP0(Meta mv),List.map (fun (n,_) -> Rel n) sorted_rels) 
	  
    | _ -> anomaly "Bug : a case has been forgotten in proof_extractor"
  in
  let pfterm = proof_extractor (gLOB sign) pf in
  (pfterm, List.rev !open_obligations)
  
