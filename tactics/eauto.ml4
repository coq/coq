(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Pp
open Util
open Names
open Nameops
open Term
open Termops
open Sign
open Reduction
open Proof_type
open Proof_trees
open Declarations
open Tacticals
open Tacmach
open Evar_refiner
open Tactics
open Pattern
open Clenv
open Auto
open Rawterm
open Hiddentac

let e_give_exact c gl = let t1 = (pf_type_of gl c) and t2 = pf_concl gl in 
  if occur_existential t1 or occur_existential t2 then 
     tclTHEN (Clenvtac.unify t1) (exact_check c) gl
  else exact_check c gl

let assumption id = e_give_exact (mkVar id)
        
let e_assumption gl = 
  tclFIRST (List.map assumption (pf_ids_of_hyps gl)) gl

TACTIC EXTEND eassumption
| [ "eassumption" ] -> [ e_assumption ]
END

TACTIC EXTEND eexact
| [ "eexact" constr(c) ] -> [ e_give_exact c ]
END

let e_give_exact_constr = h_eexact

let registered_e_assumption gl = 
  tclFIRST (List.map (fun id gl -> e_give_exact_constr (mkVar id) gl) 
              (pf_ids_of_hyps gl)) gl

(************************************************************************)
(*   PROLOG tactic                                                      *)
(************************************************************************)

let one_step l gl =
  [Tactics.intro]
  @ (List.map h_simplest_eapply (List.map mkVar (pf_ids_of_hyps gl)))
  @ (List.map h_simplest_eapply l)
  @ (List.map assumption (pf_ids_of_hyps gl))

let rec prolog l n gl =
  if n <= 0 then error "prolog - failure";
  let prol = (prolog l (n-1)) in
  (tclFIRST (List.map (fun t -> (tclTHEN t prol)) (one_step l gl))) gl

let prolog_tac l n gl =
  let n =
    match n with
      |  ArgArg n -> n
      | _ -> error "Prolog called with a non closed argument."
  in
  try (prolog l n gl)
  with UserError ("Refiner.tclFIRST",_) ->
    errorlabstrm "Prolog.prolog" (str "Prolog failed.")

TACTIC EXTEND prolog
| [ "prolog" "[" constr_list(l) "]" int_or_var(n) ] -> [ prolog_tac l n ]
END

open Auto
open Unification

(***************************************************************************)
(* A tactic similar to Auto, but using EApply, Assumption and e_give_exact *)
(***************************************************************************)

(* no delta yet *)

let unify_e_resolve flags (c,clenv) gls = 
  let clenv' = connect_clenv gls clenv in
  let _ = clenv_unique_resolver false ~flags clenv' gls in
  h_simplest_eapply c gls

let unify_e_resolve_nodelta (c,clenv) gls = 
  let clenv' = connect_clenv gls clenv in
  let _ = clenv_unique_resolver false clenv' gls in
  h_simplest_eapply c gls

let rec e_trivial_fail_db mod_delta db_list local_db goal =
  let tacl = 
    registered_e_assumption ::
    (tclTHEN Tactics.intro 
       (function g'->
	  let d = pf_last_hyp g' in
	  let hintl = make_resolve_hyp (pf_env g') (project g') d in
          (e_trivial_fail_db mod_delta db_list
	      (Hint_db.add_list hintl local_db) g'))) ::
    (List.map fst (e_trivial_resolve mod_delta db_list local_db (pf_concl goal)) )
  in 
  tclFIRST (List.map tclCOMPLETE tacl) goal 

and e_my_find_search mod_delta =
  if mod_delta then e_my_find_search_delta
  else e_my_find_search_nodelta

and e_my_find_search_nodelta db_list local_db hdc concl = 
  let hdc = head_of_constr_reference hdc in
  let hintl =
    if occur_existential concl then 
      list_map_append (Hint_db.map_all hdc) (local_db::db_list)
    else 
      list_map_append (Hint_db.map_auto (hdc,concl)) (local_db::db_list)
  in 
  let tac_of_hint = 
    fun {pri=b; pat = p; code=t} -> 
      (b, 
       let tac =
	 match t with
	   | Res_pf (term,cl) -> unify_resolve_nodelta (term,cl)
	   | ERes_pf (term,cl) -> unify_e_resolve_nodelta (term,cl)
	   | Give_exact (c) -> e_give_exact_constr c
	   | Res_pf_THEN_trivial_fail (term,cl) ->
               tclTHEN (unify_e_resolve_nodelta (term,cl)) 
		 (e_trivial_fail_db false db_list local_db)
	   | Unfold_nth c -> unfold_in_concl [all_occurrences,c]
	   | Extern tacast -> conclPattern concl p tacast
       in 
       (tac,fmt_autotactic t))
       (*i
	 fun gls -> pPNL (fmt_autotactic t); Format.print_flush (); 
                     try tac gls
		     with e when Logic.catchable_exception(e) -> 
                            (Format.print_string "Fail\n"; 
			     Format.print_flush (); 
			     raise e)
       i*)
  in 
  List.map tac_of_hint hintl

and e_my_find_search_delta db_list local_db hdc concl = 
  let hdc = head_of_constr_reference hdc in
  let hintl =
    if occur_existential concl then 
      list_map_append (fun db -> 
	let flags = {auto_unif_flags with modulo_delta = Hint_db.transparent_state db} in
	  List.map (fun x -> flags, x) (Hint_db.map_all hdc db)) (local_db::db_list)
    else 
      list_map_append (fun db -> 
	let flags = {auto_unif_flags with modulo_delta = Hint_db.transparent_state db} in
	  List.map (fun x -> flags, x) (Hint_db.map_auto (hdc,concl) db)) (local_db::db_list)
  in 
  let tac_of_hint = 
    fun (st, {pri=b; pat = p; code=t}) -> 
      (b, 
       let tac =
	 match t with
	   | Res_pf (term,cl) -> unify_resolve st (term,cl)
	   | ERes_pf (term,cl) -> unify_e_resolve st (term,cl)
	   | Give_exact (c) -> e_give_exact_constr c
	   | Res_pf_THEN_trivial_fail (term,cl) ->
               tclTHEN (unify_e_resolve st (term,cl)) 
		 (e_trivial_fail_db true db_list local_db)
	   | Unfold_nth c -> unfold_in_concl [all_occurrences,c]
	   | Extern tacast -> conclPattern concl p tacast
       in 
       (tac,fmt_autotactic t))
       (*i
	 fun gls -> pPNL (fmt_autotactic t); Format.print_flush (); 
                     try tac gls
		     with e when Logic.catchable_exception(e) -> 
                            (Format.print_string "Fail\n"; 
			     Format.print_flush (); 
			     raise e)
       i*)
  in 
  List.map tac_of_hint hintl
    
and e_trivial_resolve mod_delta db_list local_db gl = 
  try 
    Auto.priority 
      (e_my_find_search mod_delta db_list local_db 
	 (List.hd (head_constr_bound gl [])) gl)
  with Bound | Not_found -> []

let e_possible_resolve mod_delta db_list local_db gl =
  try List.map snd 
    (e_my_find_search mod_delta db_list local_db 
	(List.hd (head_constr_bound gl [])) gl)
  with Bound | Not_found -> []

let assumption_tac_list id = apply_tac_list (e_give_exact_constr (mkVar id))

let find_first_goal gls = 
  try first_goal gls with UserError _ -> assert false

(*s The following module [SearchProblem] is used to instantiate the generic
    exploration functor [Explore.Make]. *)

type search_state = { 
  depth : int; (*r depth of search before failing *)
  tacres : goal list sigma * validation;
  last_tactic : std_ppcmds;
  dblist : Auto.hint_db list;
  localdb :  Auto.hint_db list }
    
module SearchProblem = struct
    
  type state = search_state

  let success s = (sig_it (fst s.tacres)) = []

  let pr_ev evs ev = Printer.pr_constr_env (Evd.evar_env ev) (Evarutil.nf_evar evs ev.Evd.evar_concl)
    
  let pr_goals gls =
    let evars = Evarutil.nf_evars (Refiner.project gls) in
      prlist (pr_ev evars) (sig_it gls)
	
  let filter_tactics (glls,v) l =
(*     let _ = Proof_trees.db_pr_goal (List.hd (sig_it glls)) in *)
(*     let evars = Evarutil.nf_evars (Refiner.project glls) in *)
(*     msg (str"Goal:" ++ pr_ev evars (List.hd (sig_it glls)) ++ str"\n"); *)
    let rec aux = function
      | [] -> []
      | (tac,pptac) :: tacl -> 
	  try 
	    let (lgls,ptl) = apply_tac_list tac glls in 
	    let v' p = v (ptl p) in
(* 	    let gl = Proof_trees.db_pr_goal (List.hd (sig_it glls)) in *)
(* 	      msg (hov 1 (pptac ++ str" gives: \n" ++ pr_goals lgls ++ str"\n")); *)
	      ((lgls,v'),pptac) :: aux tacl
	  with e -> Refiner.catch_failerror e; aux tacl
    in aux l
      
  (* Ordering of states is lexicographic on depth (greatest first) then
     number of remaining goals. *)
  let compare s s' =
    let d = s'.depth - s.depth in
    let nbgoals s = List.length (sig_it (fst s.tacres)) in
    if d <> 0 then d else nbgoals s - nbgoals s'

  let branching s = 
    if s.depth = 0 then 
      []
    else      
      let lg = fst s.tacres in
      let nbgl = List.length (sig_it lg) in
      assert (nbgl > 0);
      let g = find_first_goal lg in
      let assumption_tacs = 
	let l = 
	  filter_tactics s.tacres
	    (List.map 
	       (fun id -> (e_give_exact_constr (mkVar id),
			   (str "exact" ++ spc () ++ pr_id id)))
	       (pf_ids_of_hyps g))
	in
	List.map (fun (res,pp) -> { depth = s.depth; tacres = res;
				    last_tactic = pp; dblist = s.dblist;
				    localdb = List.tl s.localdb }) l
      in
      let intro_tac = 
	List.map 
	  (fun ((lgls,_) as res,pp) -> 
	     let g' = first_goal lgls in 
	     let hintl = 
	       make_resolve_hyp (pf_env g') (project g') (pf_last_hyp g')
	     in
             let ldb = Hint_db.add_list hintl (List.hd s.localdb) in
	     { depth = s.depth; tacres = res; 
	       last_tactic = pp; dblist = s.dblist;
	       localdb = ldb :: List.tl s.localdb })
	  (filter_tactics s.tacres [Tactics.intro,(str "intro")])
      in
      let rec_tacs = 
	let l = 
	  filter_tactics s.tacres (e_possible_resolve false s.dblist (List.hd s.localdb) (pf_concl g))
	in
	List.map 
	  (fun ((lgls,_) as res, pp) -> 
	     let nbgl' = List.length (sig_it lgls) in
	     if nbgl' < nbgl then
	       { depth = s.depth; tacres = res; last_tactic = pp;
		 dblist = s.dblist; localdb = List.tl s.localdb }
	     else 
	       { depth = pred s.depth; tacres = res; 
		 dblist = s.dblist; last_tactic = pp;
		 localdb = 
		   list_addn (nbgl'-nbgl) (List.hd s.localdb) s.localdb })
	  l
      in
      List.sort compare (assumption_tacs @ intro_tac @ rec_tacs)

  let pp s = 
    msg (hov 0 (str " depth=" ++ int s.depth ++ spc () ++ 
		  s.last_tactic ++ str "\n"))

end

module Search = Explore.Make(SearchProblem)

let make_initial_state n gl dblist localdb =
  { depth = n;
    tacres = tclIDTAC gl;
    last_tactic = (mt ());
    dblist = dblist;
    localdb = [localdb] }

let debug_depth_first = Search.debug_depth_first

let e_depth_search debug p db_list local_db gl =
  try
    let tac = if debug then Search.debug_depth_first else Search.depth_first in
    let s = tac (make_initial_state p gl db_list local_db) in
    s.tacres
  with Not_found -> error "eauto: depth first search failed."

let e_breadth_search debug n db_list local_db gl =
  try
    let tac = 
      if debug then Search.debug_breadth_first else Search.breadth_first 
    in
    let s = tac (make_initial_state n gl db_list local_db) in
    s.tacres
  with Not_found -> error "eauto: breadth first search failed."

let e_search_auto debug (in_depth,p) lems db_list gl = 
  let local_db = make_local_hint_db true lems gl in 
  if in_depth then 
    e_depth_search debug p db_list local_db gl
  else 
    e_breadth_search debug p db_list local_db gl

open Evd

let eauto_with_bases debug np lems db_list = 
  tclTRY (e_search_auto debug np lems db_list)

let eauto debug np lems dbnames = 
  let db_list =
    List.map
      (fun x -> 
	 try searchtable_map x
	 with Not_found -> error ("No such Hint database: "^x^"."))
      ("core"::dbnames) 
  in
  tclTRY (e_search_auto debug np lems db_list)
  
let full_eauto debug n lems gl = 
  let dbnames = current_db_names () in
  let dbnames =  list_subtract dbnames ["v62"] in
  let db_list = List.map searchtable_map dbnames in
  tclTRY (e_search_auto debug n lems db_list) gl

let gen_eauto d np lems = function
  | None -> full_eauto d np lems
  | Some l -> eauto d np lems l

let make_depth = function
  | None -> !default_search_depth 
  | Some (ArgArg d) -> d
  | _ -> error "eauto called with a non closed argument."

let make_dimension n = function
  | None -> (true,make_depth n)
  | Some (ArgArg d) -> (false,d)
  | _ -> error "eauto called with a non closed argument."

open Genarg

(* Hint bases *)

let pr_hintbases _prc _prlc _prt = Pptactic.pr_hintbases

ARGUMENT EXTEND hintbases
  TYPED AS preident_list_opt
  PRINTED BY pr_hintbases
| [ "with" "*" ] -> [ None ]
| [ "with" ne_preident_list(l) ] -> [ Some l ]
| [ ] -> [ Some [] ]
END

let pr_constr_coma_sequence prc _ _ = prlist_with_sep pr_coma prc

ARGUMENT EXTEND constr_coma_sequence
  TYPED AS constr_list
  PRINTED BY pr_constr_coma_sequence
| [ constr(c) "," constr_coma_sequence(l) ] -> [ c::l ]
| [ constr(c) ] -> [ [c] ]
END

let pr_auto_using prc _prlc _prt = Pptactic.pr_auto_using prc

ARGUMENT EXTEND auto_using
  TYPED AS constr_list
  PRINTED BY pr_auto_using
| [ "using" constr_coma_sequence(l) ] -> [ l ]
| [ ] -> [ [] ]
END

TACTIC EXTEND eauto
| [ "eauto" int_or_var_opt(n) int_or_var_opt(p) auto_using(lems) 
    hintbases(db) ] ->
    [ gen_eauto false (make_dimension n p) lems db ]
END

TACTIC EXTEND new_eauto
| [ "new" "auto" int_or_var_opt(n) auto_using(lems) 
    hintbases(db) ] ->
    [ match db with
      | None -> new_full_auto (make_depth n) lems
      | Some l ->
	  new_auto (make_depth n) lems l ]
END
      
TACTIC EXTEND debug_eauto
| [ "debug" "eauto" int_or_var_opt(n) int_or_var_opt(p) auto_using(lems) 
    hintbases(db) ] ->
    [ gen_eauto true (make_dimension n p) lems db ]
END

TACTIC EXTEND dfs_eauto
| [ "dfs" "eauto" int_or_var_opt(p) auto_using(lems) 
      hintbases(db) ] ->
    [ gen_eauto false (true, make_depth p) lems db ]
END

let autosimpl db cl =
  let unfold_of_elts constr (b, elts) =
    if not b then 
      List.map (fun c -> all_occurrences, constr c) elts
    else []
  in
  let unfolds = List.concat (List.map (fun dbname -> 
    let db = searchtable_map dbname in
    let (ids, csts) = Hint_db.transparent_state db in
      unfold_of_elts (fun x -> EvalConstRef x) (Cpred.elements csts) @
      unfold_of_elts (fun x -> EvalVarRef x) (Idpred.elements ids)) db)
  in unfold_option unfolds cl

TACTIC EXTEND autosimpl
| [ "autosimpl" hintbases(db) ] ->
    [ autosimpl (match db with None -> ["core"] | Some x -> "core"::x) None ]
END
