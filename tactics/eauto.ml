
(* $Id$ *)

open Pp
open Util
open Names
(* open Generic *)
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

let e_give_exact c gl = tclTHEN (unify (pf_type_of gl c)) (Tactics.exact c) gl

let assumption id = e_give_exact (VAR id)
        
let e_assumption gl = 
  tclFIRST (List.map assumption (pf_ids_of_hyps gl)) gl

let e_give_exact_constr = hide_constr_tactic "EExact" e_give_exact

let registered_e_assumption gl = 
  tclFIRST (List.map (fun id gl -> e_give_exact_constr (VAR id) gl) 
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
  @ (List.map e_resolve_constr (List.map (fun x -> VAR x)
				  (pf_ids_of_hyps gl)))
  @ (List.map e_resolve_constr l)
  @ (List.map assumption (pf_ids_of_hyps gl))

let rec prolog l n gl =
  if n <= 0 then error "prolog - failure";
  let prol = (prolog l (n-1)) in
  (tclFIRST (List.map (fun t -> (tclTHEN t prol)) (one_step l gl))) gl

let prolog_tac lcom n gl =
  let l = List.map (pf_interp_constr gl) lcom in
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
    | Command com -> com
    | _ -> assert false
  in
  let gentac = 
    hide_tactic "Prolog"
      (function
	 | (Integer n) :: al -> prolog_tac (List.map uncom al) n
	 | _ -> assert false)
  in 
  fun coms n -> 
    gentac ((Integer n) :: (List.map (fun com -> (Command com)) coms))

let vernac_instantiate =
  let gentac = hide_tactic "Instantiate" instantiate_tac in 
  fun n com -> gentac [Integer n; Command com]

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
	  let hintl = make_resolve_hyp d in
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
      (b,
       match t with
	 | Res_pf (term,cl) -> unify_resolve (term,cl)
	 | ERes_pf (term,cl) -> unify_e_resolve (term,cl)
	 | Give_exact (c) -> e_give_exact_constr c
	 | Res_pf_THEN_trivial_fail (term,cl) ->
             tclTHEN (unify_e_resolve (term,cl)) 
	       (e_trivial_fail_db db_list local_db)
	 | Unfold_nth c -> unfold_constr c
	 | Extern tacast -> Tacticals.conclPattern concl 
	       (out_some p) tacast)
  in 
  List.map tac_of_hint hintl
    
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

(* A version with correct (?) backtracking using operations on lists 
   of goals *)

let assumption_tac_list id = apply_tac_list (e_give_exact_constr (VAR id))

exception Nogoals

let find_first_goal gls = 
  try first_goal gls with UserError _ -> raise Nogoals
      
let rec e_search n db_list local_db lg =
  try 
    let g = find_first_goal lg in
    if n = 0 then error "BOUND 2";
    let assumption_tacs = 
      List.map 
	(fun id gls -> 
	   then_tactic_list 
	     (assumption_tac_list id)
	     (e_search n db_list local_db)
	     gls)
	(pf_ids_of_hyps g)
    in
    let intro_tac = 
      apply_tac_list
	(tclTHEN Tactics.intro 
	   (fun g' -> 		   
	      let hintl = make_resolve_hyp (pf_last_hyp g') in
	      (tactic_list_tactic 
		 (e_search n db_list
		    (Hint_db.add_list hintl local_db))) g')) 
    in
    let rec_tacs = 
      List.map 
	(fun ntac lg' -> 
	   (then_tactic_list 
	      (apply_tac_list ntac)
	      (e_search (n-1) db_list local_db) lg'))
        (e_possible_resolve db_list local_db (pf_concl g)) 
    in
    tclFIRSTLIST (assumption_tacs @ (intro_tac :: rec_tacs)) lg
  with Nogoals -> 
    tclIDTAC_list lg

let e_search_auto n db_list gl = 
  tactic_list_tactic 
    (e_search n db_list (make_local_hint_db (pf_hyps gl)))
    gl

let eauto n dbnames = 
  let db_list =
    List.map
      (fun x -> 
	 try Stringmap.find x !searchtable
	 with Not_found -> error ("EAuto: "^x^": No such Hint database"))
      ("core"::dbnames) 
  in
  tclTRY (tclCOMPLETE (e_search_auto n db_list))

let default_eauto gl = eauto !default_search_depth [] gl

let full_eauto n gl = 
  let dbnames = stringmap_dom !searchtable in
  let dbnames =  list_subtract dbnames ["v62"] in
  let db_list = List.map (fun x -> Stringmap.find x !searchtable) dbnames in
  let local_db = make_local_hint_db (pf_hyps gl) in
  tclTRY (tclCOMPLETE (e_search_auto n db_list)) gl

let default_full_auto gl = full_auto !default_search_depth gl

let dyn_eauto l = match l with
  | [] -> default_eauto
  | [Integer n] -> eauto n []
  | [Quoted_string "*"] -> default_full_auto 
  | [Integer n; Quoted_string "*"] -> full_eauto n
  | (Integer n) :: l1 -> 
      eauto n (List.map 
		 (function 
		    | Identifier id -> (string_of_id id)
		    | _ -> bad_tactic_args "dyn_eauto" l) l1)
  | _ -> 
      eauto !default_search_depth 
	(List.map 
	   (function Identifier id -> (string_of_id id)
	      | _ -> bad_tactic_args "dyn_eauto" l) l)

let h_eauto = hide_tactic "EAuto" dyn_eauto
