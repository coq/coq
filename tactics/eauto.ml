
(* $Id$ *)

open Pp
open Util
open Names
open Term
open Sign
open Reduction
open Proof_type
open Proof_trees
open Tacmach
open Tactics
open Pattern
open Clenv
open Auto

let e_give_exact c gl = tclTHEN (unify (pf_type_of gl c)) (exact_no_check c) gl

let assumption id = e_give_exact (mkVar id)
        
let e_assumption gl = 
  tclFIRST (List.map assumption (pf_ids_of_hyps gl)) gl

let e_give_exact_constr = hide_constr_tactic "EExact" e_give_exact

let registered_e_assumption gl = 
  tclFIRST (List.map (fun id gl -> e_give_exact_constr (mkVar id) gl) 
              (pf_ids_of_hyps gl)) gl
    
let e_resolve_with_bindings_tac  (c,lbind) gl = 
  let (wc,kONT) = startWalk gl in
  let t = w_hnf_constr wc (w_type_of wc c) in 
  let clause = make_clenv_binding_apply wc (c,t) lbind in 
  e_res_pf kONT clause gl

let e_resolve_with_bindings = 
  tactic_com_bind_list e_resolve_with_bindings_tac

let vernac_e_resolve_with_bindings = 
  hide_cbindl_tactic  "EApplyWithBindings" e_resolve_with_bindings_tac

let e_resolve_constr c gls = e_resolve_with_bindings_tac (c,[]) gls
let resolve_constr c gls = Tactics.apply_with_bindings (c,[]) gls
			     
let vernac_e_resolve_constr = 
  hide_constr_tactic "EApply" e_resolve_constr

(************************************************************************)
(*   PROLOG tactic                                                      *)
(************************************************************************)

let one_step l gl =
  [Tactics.intro]
  @ (List.map e_resolve_constr (List.map mkVar (pf_ids_of_hyps gl)))
  @ (List.map e_resolve_constr l)
  @ (List.map assumption (pf_ids_of_hyps gl))

let rec prolog l n gl =
  if n <= 0 then error "prolog - failure";
  let prol = (prolog l (n-1)) in
  (tclFIRST (List.map (fun t -> (tclTHEN t prol)) (one_step l gl))) gl

let prolog_tac l n gl =
 (* let l = List.map (pf_interp_constr gl) lcom in *)
  try (prolog l n gl)
  with UserError ("Refiner.tclFIRST",_) ->
    errorlabstrm "Prolog.prolog" [< 'sTR "Prolog failed" >]

let evars_of evc c = 
  let rec evrec acc c = match splay_constr c with
    | OpEvar n, _ when Evd.in_dom evc n -> c :: acc
    | _, cl -> Array.fold_left evrec acc cl
  in 
  evrec [] c

let instantiate n c gl =
  let sigma = project gl in
  let evl = evars_of sigma (pf_concl gl) in
  let (wc,kONT) = startWalk gl in
  if List.length evl < n then error "not enough evars";
  let (n,_) as k = destEvar (List.nth evl (n-1)) in 
  if Evd.is_defined sigma n then 
    error "Instantiate called on already-defined evar";
  let wc' = w_Define n c wc in 
  kONT wc' gl

let instantiate_tac = function
  | [Integer n; Command com] ->
      (fun gl -> instantiate n (pf_interp_constr gl com) gl)
  | [Integer n; Constr c] ->
      (fun gl -> instantiate n c gl)
  | _ -> invalid_arg "Instantiate called with bad arguments"

let whd_evar env sigma c = match kind_of_term c with
  | IsEvar (n, cl) when Evd.in_dom sigma n & Evd.is_defined sigma n ->
        Instantiate.existential_value sigma (n,cl)
  | _ -> c

let normEvars gl =
  let sigma = project gl in
  let env = pf_env gl in
  let nf_evar = strong whd_evar
  and simplify = nf_betaiota in 
  convert_concl (nf_evar env sigma (simplify env sigma (pf_concl gl))) gl

let vernac_prolog =
  let uncom = function
    | Constr c -> c
    | _ -> assert false
  in
  let gentac = 
    hide_tactic "Prolog"
      (function
	 | (Integer n) :: al -> prolog_tac (List.map uncom al) n
	 | _ -> assert false)
  in 
  fun coms n -> 
    gentac ((Integer n) :: (List.map (fun com -> (Constr com)) coms))

let vernac_instantiate =
  hide_tactic "Instantiate" instantiate_tac;;

let vernac_normevars =
  hide_atomic_tactic "NormEvars" normEvars

open Auto

(***************************************************************************)
(* A tactic similar to Auto, but using EApply, Assumption and e_give_exact *)
(***************************************************************************)

(* A registered version of tactics in order to keep a trace *)

let unify_e_resolve  (c,clenv) gls = 
  let (wc,kONT) = startWalk gls in
  let clenv' = connect_clenv wc clenv in
  let _ = clenv_unique_resolver false clenv' gls in
  vernac_e_resolve_constr c gls

let rec e_trivial_fail_db db_list local_db goal =
  let tacl = 
    registered_e_assumption ::
    (tclTHEN Tactics.intro 
       (function g'->
	  let d = pf_last_hyp g' in
	  let hintl = make_resolve_hyp (pf_env g') (project g') d in
          (e_trivial_fail_db db_list
	     (Hint_db.add_list hintl local_db) g'))) ::
    (e_trivial_resolve db_list local_db (pf_concl goal)) 
  in 
  tclFIRST (List.map tclCOMPLETE tacl) goal 

and e_my_find_search db_list local_db hdc concl = 
  let hdc = head_of_constr_reference hdc in
  let hintl =
    if occur_existential concl then 
      list_map_append (fun db -> Hint_db.map_all hdc db) (local_db::db_list)
    else 
      list_map_append (fun db -> Hint_db.map_auto (hdc,concl) db)
	(local_db::db_list)
  in 
  let tac_of_hint = 
    fun ({pri=b; pat = p; code=t} as patac) -> 
      (b, let tac =
       match t with
	 | Res_pf (term,cl) -> unify_resolve (term,cl)
	 | ERes_pf (term,cl) -> unify_e_resolve (term,cl)
	 | Give_exact (c) -> e_give_exact_constr c
	 | Res_pf_THEN_trivial_fail (term,cl) ->
             tclTHEN (unify_e_resolve (term,cl)) 
	       (e_trivial_fail_db db_list local_db)
	 | Unfold_nth c -> unfold_constr c
	 | Extern tacast -> Tacticals.conclPattern concl 
	       (out_some p) tacast
       in tac)
	 (*i fun gls -> pPNL (fmt_autotactic t); flush stdout; 
                     try tac gls
		     with e when Logic.catchable_exception(e) -> 
                            (print_string "Fail\n"; flush stdout; raise e)
	   i*)
  in List.map tac_of_hint hintl
    
and e_trivial_resolve db_list local_db gl = 
  try 
    Auto.priority 
      (e_my_find_search db_list local_db 
	 (List.hd (head_constr_bound gl [])) gl)
  with Bound | Not_found -> []

(***
let vernac_e_trivial 
   = hide_atomic_tactic "ETrivial" e_trivial_fail
****)

let e_possible_resolve db_list local_db gl =
  try List.map snd (e_my_find_search db_list local_db 
		      (List.hd (head_constr_bound gl [])) gl)
  with Bound | Not_found -> []

(* A depth-first version with correct (?) backtracking using operations on lists 
   of goals *)

let assumption_tac_list id = apply_tac_list (e_give_exact_constr (mkVar id))

exception Nogoals

let find_first_goal gls = 
  try first_goal gls with UserError _ -> raise Nogoals
      
let rec e_search_depth n db_list local_db lg =
  try 
    let g = find_first_goal lg in
    if n = 0 then error "BOUND 2";
    let assumption_tacs = 
      List.map 
	(fun id gls -> 
	   then_tactic_list 
	     (assumption_tac_list id)
	     (e_search_depth n db_list local_db)
	     gls)
	(pf_ids_of_hyps g)
    in
    let intro_tac = 
      apply_tac_list
	(tclTHEN Tactics.intro 
	   (fun g' -> 		   
	      let hintl = make_resolve_hyp (pf_env g') (project g') 
			    (pf_last_hyp g') in
	      (tactic_list_tactic 
		 (e_search_depth n db_list
		    (Hint_db.add_list hintl local_db))) g')) 
    in
    let rec_tacs = 
      List.map 
	(fun ntac lg' -> 
	   (then_tactic_list 
	      (apply_tac_list ntac)
	      (e_search_depth (n-1) db_list local_db) lg'))
        (e_possible_resolve db_list local_db (pf_concl g)) 
    in
    tclFIRSTLIST (assumption_tacs @ (intro_tac :: rec_tacs)) lg
  with Nogoals -> 
    tclIDTAC_list lg

(* Breadth-first search, a state is [(n,(lgls,val),hintl)] where 
   [n] is the depth of search before failing
   [lgls,val] is a non empty list of remaining goals and the current validation
   hintl is a possible hints list to be added to the local hints database (after intro)
   we manipulate a FILO of possible states.
*) 
type state = {depth : int; 
	      tacres : goal list sigma * validation;
              localdb :  Auto.Hint_db.t}

type state_queue = state list * state list

let empty_queue = ([],[])

let push_state s (l1,l2) = (s::l1,l2)

let decomp_states = function 
    [],[] -> raise Not_found
  | (l1,a::l2)->(a,(l1,l2))
  | (l1,[])-> let l2 = List.rev l1 in (List.hd l2,([],List.tl l2))

let add_state n tacr db sl = push_state {depth=n;tacres=tacr;localdb=db} sl

let e_search (n,p) db_list local_db gl =
  let state0 = add_state n (tclIDTAC gl) local_db empty_queue in
  let rec process_state stateq =
    let (fstate,restq) = try decomp_states stateq 
    with Not_found -> error "BOUND 2" (* no more states *)
    in 
    let (glls,v) = fstate.tacres 
    and n = fstate.depth
    and local_db = fstate.localdb 
    in 
    let rec process_tacs tacl sq = 
      match tacl with 
	  [] -> (* no more tactics for the goal *)
	     process_state sq (* continue with next state *)
	| (b,tac)::tacrest ->
            (try 
	    let (lgls,ptl) = apply_tac_list tac glls in 
	    let v' p = v (ptl p) in
	    let k = List.length (sig_it lgls) in
	      if k = 0 then (lgls,v') (* success *)
	      else  let n' = if k < List.length (sig_it glls) or b then n else n-1 in
		   let hintl = (* possible new hint list for assumptions *)
		     if b then (* intro tactic *)
		       let g' = first_goal lgls in 
			 make_resolve_hyp (pf_env g') (project g') (pf_last_hyp g')
		     else []
                   in let ldb = Hint_db.add_list hintl local_db
		   in if n'=0 then 
		     try 
		       let (lgls1,ptl1) = e_search_depth p db_list ldb lgls 
		       in let v1 p = v' (ptl1 p) in (lgls1,v1)
		     with e when Logic.catchable_exception e -> process_tacs tacrest sq
		     else let sq' = add_state n' (lgls, v') ldb sq
		   in process_tacs tacrest sq'
	     with e when Logic.catchable_exception e -> process_tacs tacrest sq)
    in let g = first_goal glls in 
    let tac1 = List.map (fun id -> (false, e_give_exact_constr (mkVar id))) (pf_ids_of_hyps g)
    and tac2 = (true,Tactics.intro)
    and tac3 = List.map (fun tac -> (false,tac)) 
		 (e_possible_resolve db_list local_db (pf_concl g))
    in process_tacs (tac1@tac2::tac3) restq
 in process_state state0


let e_search_auto (n,p) db_list gl = 
  let local_db = make_local_hint_db gl in 
    if n = 0 then tactic_list_tactic (e_search_depth p db_list local_db) gl
    else e_search (n,p) db_list local_db gl

let eauto np dbnames = 
  let db_list =
    List.map
      (fun x -> 
	 try Stringmap.find x !searchtable
	 with Not_found -> error ("EAuto: "^x^": No such Hint database"))
      ("core"::dbnames) 
  in
  tclTRY (e_search_auto np db_list)

let full_eauto n gl = 
  let dbnames = stringmap_dom !searchtable in
  let dbnames =  list_subtract dbnames ["v62"] in
  let db_list = List.map (fun x -> Stringmap.find x !searchtable) dbnames in
  let local_db = make_local_hint_db gl in
  tclTRY (e_search_auto n db_list) gl

let dyn_eauto l = 
  let (np,l) = match l with
    | (Integer n) :: (Integer p) :: l -> ((n,p),l)
    | (Integer n) :: l -> ((n,0),l)
    | l -> ((!default_search_depth,0),l)
  in
  match l with
  | [] -> eauto np []
  | [Quoted_string "*"] -> full_eauto np
  | l1 -> 
      eauto np (List.map 
		 (function 
		    | Identifier id -> (string_of_id id)
		    | _ -> bad_tactic_args "dyn_eauto" l) l1)

let h_eauto = hide_tactic "EAuto" dyn_eauto
