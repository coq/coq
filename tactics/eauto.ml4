(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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
open Tacticals
open Tacmach
open Evar_refiner
open Tactics
open Pattern
open Clenv
open Auto
open Rawterm

let e_give_exact c gl = let t1 = (pf_type_of gl c) and t2 = pf_concl gl in 
  if occur_existential t1 or occur_existential t2 then 
     tclTHEN (unify t1) (exact_no_check c) gl
  else exact_no_check c gl

let assumption id = e_give_exact (mkVar id)
        
let e_assumption gl = 
  tclFIRST (List.map assumption (pf_ids_of_hyps gl)) gl

let e_resolve_with_bindings_tac  (c,lbind) gl = 
  let (wc,kONT) = startWalk gl in
  let t = w_hnf_constr wc (w_type_of wc c) in 
  let clause = make_clenv_binding_apply wc (-1) (c,t) lbind in 
  e_res_pf kONT clause gl

let e_resolve_with_bindings = 
  tactic_com_bind_list e_resolve_with_bindings_tac

let e_resolve_constr c gls = e_resolve_with_bindings_tac (c,NoBindings) gls
let resolve_constr c gls = Tactics.apply_with_bindings (c,NoBindings) gls
			     
TACTIC EXTEND EExact
| [ "EExact" constr(c) ] -> [ e_give_exact c ]
END

let e_give_exact_constr = h_eExact

let registered_e_assumption gl = 
  tclFIRST (List.map (fun id gl -> e_give_exact_constr (mkVar id) gl) 
              (pf_ids_of_hyps gl)) gl

TACTIC EXTEND EApply
  [ "EApply" constr_with_bindings(c) ] -> [ e_resolve_with_bindings_tac c ]
END

let vernac_e_resolve_constr c = h_eApply (c,NoBindings)

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
  let n =
    match n with
      |  Genarg.ArgArg n -> n
      | _ -> error "Prolog called with a non closed argument"
  in
  try (prolog l n gl)
  with UserError ("Refiner.tclFIRST",_) ->
    errorlabstrm "Prolog.prolog" (str "Prolog failed")

TACTIC EXTEND Prolog
| [ "Prolog" "[" constr_list(l) "]" int_or_var(n) ] -> [ prolog_tac l n ]
END

(*
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
*)

open Auto

(***************************************************************************)
(* A tactic similar to Auto, but using EApply, Assumption and e_give_exact *)
(***************************************************************************)

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
    (List.map fst (e_trivial_resolve db_list local_db (pf_concl goal)) )
  in 
  tclFIRST (List.map tclCOMPLETE tacl) goal 

and e_my_find_search db_list local_db hdc concl = 
  let hdc = head_of_constr_reference hdc in
  let hintl =
    if occur_existential concl then 
      list_map_append (Hint_db.map_all hdc) (local_db::db_list)
    else 
      list_map_append (Hint_db.map_auto (hdc,concl)) (local_db::db_list)
  in 
  let tac_of_hint = 
    fun ({pri=b; pat = p; code=t} as patac) -> 
      (b, 
       let tac =
	 match t with
	   | Res_pf (term,cl) -> unify_resolve (term,cl)
	   | ERes_pf (term,cl) -> unify_e_resolve (term,cl)
	   | Give_exact (c) -> e_give_exact_constr c
	   | Res_pf_THEN_trivial_fail (term,cl) ->
               tclTHEN (unify_e_resolve (term,cl)) 
		 (e_trivial_fail_db db_list local_db)
	   | Unfold_nth c -> unfold_constr c
	   | Extern tacast -> conclPattern concl 
	       (out_some p) tacast
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
    
and e_trivial_resolve db_list local_db gl = 
  try 
    Auto.priority 
      (e_my_find_search db_list local_db 
	 (List.hd (head_constr_bound gl [])) gl)
  with Bound | Not_found -> []

let e_possible_resolve db_list local_db gl =
  try List.map snd (e_my_find_search db_list local_db 
		      (List.hd (head_constr_bound gl [])) gl)
  with Bound | Not_found -> []

let assumption_tac_list id = apply_tac_list (e_give_exact_constr (mkVar id))

let find_first_goal gls = 
  try first_goal gls with UserError _ -> assert false

(*s The following module [SearchProblem] is used to instantiate the generic
    exploration functor [Explore.Make]. *)
      
module SearchProblem = struct

  type state = { 
    depth : int; (*r depth of search before failing *)
    tacres : goal list sigma * validation;
    last_tactic : std_ppcmds;
    dblist : Auto.Hint_db.t list;
    localdb :  Auto.Hint_db.t list }
		 
  let success s = (sig_it (fst s.tacres)) = []

  let rec filter_tactics (glls,v) = function
    | [] -> []
    | (tac,pptac) :: tacl -> 
	try 
	  let (lgls,ptl) = apply_tac_list tac glls in 
	  let v' p = v (ptl p) in
	  ((lgls,v'),pptac) :: filter_tactics (glls,v) tacl
	with e when Logic.catchable_exception e ->
	  filter_tactics (glls,v) tacl

  let rec list_addn n x l = 
    if n = 0 then l else x :: (list_addn (pred n) x l)

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
			   (str "Exact" ++ spc () ++ pr_id id)))
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
	  (filter_tactics s.tacres [Tactics.intro,(str "Intro")])
      in
      let rec_tacs = 
	let l = 
	  filter_tactics s.tacres
	    (e_possible_resolve s.dblist (List.hd s.localdb) (pf_concl g))
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
  { SearchProblem.depth = n;
    SearchProblem.tacres = tclIDTAC gl;
    SearchProblem.last_tactic = (mt ());
    SearchProblem.dblist = dblist;
    SearchProblem.localdb = [localdb] }

let e_depth_search debug p db_list local_db gl =
  try
    let tac = if debug then Search.debug_depth_first else Search.depth_first in
    let s = tac (make_initial_state p gl db_list local_db) in
    s.SearchProblem.tacres
  with Not_found -> error "EAuto: depth first search failed"

let e_breadth_search debug n db_list local_db gl =
  try
    let tac = 
      if debug then Search.debug_breadth_first else Search.breadth_first 
    in
    let s = tac (make_initial_state n gl db_list local_db) in
    s.SearchProblem.tacres
  with Not_found -> error "EAuto: breadth first search failed"

let e_search_auto debug (in_depth,p) db_list gl = 
  let local_db = make_local_hint_db gl in 
  if in_depth then 
    e_depth_search debug p db_list local_db gl
  else 
    e_breadth_search debug p db_list local_db gl

let eauto debug np dbnames = 
  let db_list =
    List.map
      (fun x -> 
	 try Stringmap.find x !searchtable
	 with Not_found -> error ("EAuto: "^x^": No such Hint database"))
      ("core"::dbnames) 
  in
  tclTRY (e_search_auto debug np db_list)

let full_eauto debug n gl = 
  let dbnames = stringmap_dom !searchtable in
  let dbnames =  list_subtract dbnames ["v62"] in
  let db_list = List.map (fun x -> Stringmap.find x !searchtable) dbnames in
  let local_db = make_local_hint_db gl in
  tclTRY (e_search_auto debug n db_list) gl

let gen_eauto d np = function
  | None -> full_eauto d np
  | Some l -> eauto d np l

let make_depth = function
  | None -> !default_search_depth 
  | Some (Genarg.ArgArg d) -> d
  | _ -> error "EAuto called with a non closed argument"

let make_dimension n = function
  | None -> (true,make_depth n)
  | Some (Genarg.ArgArg d) -> (false,d)
  | _ -> error "EAuto called with a non closed argument"

open Genarg

(* Hint bases *)

let wit_hintbases, rawwit_hintbases = Genarg.create_arg "hintbases"
let hintbases = create_generic_entry "hintbases" rawwit_hintbases
let _ = Tacinterp.add_genarg_interp "hintbases"
  (fun ist x ->
    (in_gen wit_hintbases
      (out_gen (wit_opt (wit_list0 wit_string))
	(Tacinterp.genarg_interp ist
	  (in_gen (wit_opt (wit_list0 rawwit_string))
	    (out_gen rawwit_hintbases x))))))

GEXTEND Gram
  GLOBAL: hintbases;
  hintbases:
  [ [ "with"; "*" -> None
    | "with"; l = LIST1 IDENT -> Some l
    | -> Some [] ] ];
END

let pr_hintbases = function 
  | None -> str " with *"
  | Some [] -> mt ()
  | Some l -> str " with " ++ Util.prlist str l

let _ = 
  Pptactic.declare_extra_genarg_pprule 
    (rawwit_hintbases, pr_hintbases)
    (wit_hintbases, pr_hintbases)

TACTIC EXTEND EAuto
| [ "EAuto" int_or_var_opt(n) int_or_var_opt(p) hintbases(db) ] ->
    [ gen_eauto false (make_dimension n p) db ]
END

TACTIC EXTEND EAutoDebug
| [ "EAutod" int_or_var_opt(n) int_or_var_opt(p) hintbases(db) ] ->
    [ gen_eauto true (make_dimension n p) db ]
END


