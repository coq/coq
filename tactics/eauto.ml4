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
open Declarations
open Tacticals
open Tactics
open Pattern
open Clenv
open Auto
open Rawterm
open Hiddentac

(* arnaud: trucs factices *)
type tactics = Tacticals.tactic

let pf_type_of _ = Util.anomaly "Eauto.pf_type_of: fantome"
let pf_concl _ = Util.anomaly "Eauto.pf_concl: fantome"

module Clenvtac =
  struct
    let unify  _ = Util.anomaly "Eauto.unify: fantome"
  end

let pf_ids_of_hyps _ = Util.anomaly "Eauto.pf_ids_of_hyps: fantome"

module Refiner =
  struct
    let abstract_extended_tactic = Tacticals.abstract_extended_tactic
  end
let pf_reduce_to_quantified_ind _ = Util.anomaly "Eauto.pf_reduce_to_quantified_ind: fantome"
let convert_concl_no_check _ = Util.anomaly "Eauto.convert_concl_no_check: fantome"
let pf_last_hyp _ = Util.anomaly "Eauto.pf_last_hyp: fantome"
let pf_env _ = Util.anomaly "Eauto.pf_env: fantome"
let project _ = Util.anomaly "Eauto.project: fantome"
let apply_tac_list _ = Util.anomaly "Eauto.apply_tac_list: fantome"
let first_goal _ = Util.anomaly "Eauto.first_goal: fantome"
let sig_it _ = Util.anomaly "Eauto.sig_it: fantome"

(* arnaud: /trucs factices *)

let e_give_exact c gl = let t1 = (pf_type_of gl c) and t2 = pf_concl gl in 
  if occur_existential t1 or occur_existential t2 then 
     tclTHEN (Clenvtac.unify t1) (exact_check c) gl
  else exact_check c gl

let assumption id = e_give_exact (mkVar id)
        
let e_assumption gl = 
  tclFIRST (List.map assumption (pf_ids_of_hyps gl)) gl

(* arnaud: à restaurer
TACTIC EXTEND eassumption
| [ "eassumption" ] -> [ Util.anomaly "Eauto.eassuptiom: à restaurer" (* arnaud: e_assumption *)]
END
*)

TACTIC EXTEND eexact
| [ "eexact" constr(c) ] -> [ Util.anomaly "Eauto.eexact: à restaurer" (* arnaud: e_give_exact c *)]
END

let e_give_exact_constr = h_eexact

let registered_e_assumption gl = 
  tclFIRST (List.map (fun id gl -> e_give_exact_constr (mkVar id) gl) 
              (pf_ids_of_hyps gl)) gl

let e_constructor_tac boundopt i lbind gl = 
    let cl = pf_concl gl in 
  let (mind,redcl) = pf_reduce_to_quantified_ind gl cl in 
  let nconstr =
    Array.length (snd (Global.lookup_inductive mind)).mind_consnames in
  if i=0 then error "The constructors are numbered starting from 1";
  if i > nconstr then error "Not enough constructors";
  begin match boundopt with 
    | Some expctdnum -> 
        if expctdnum <> nconstr then 
	  error "Not the expected number of constructors"
    | None -> ()
  end;
  let cons = mkConstruct (ith_constructor_of_inductive mind i) in
  let apply_tac = eapply_with_ebindings (cons,lbind) in
  (tclTHENLIST [convert_concl_no_check redcl DEFAULTcast
; intros; apply_tac]) gl

let e_one_constructor i = e_constructor_tac None i

let e_any_constructor tacopt gl =
  let t = match tacopt with None -> tclIDTAC | Some t -> t in
  let mind = fst (pf_reduce_to_quantified_ind gl (pf_concl gl)) in
  let nconstr =
    Array.length (snd (Global.lookup_inductive mind)).mind_consnames in
  if nconstr = 0 then error "The type has no constructors";
  tclFIRST (List.map (fun i -> tclTHEN (e_one_constructor i NoBindings) t) 
              (interval 1 nconstr)) gl

let e_left = e_constructor_tac (Some 2) 1

let e_right = e_constructor_tac (Some 2) 2

let e_split = e_constructor_tac (Some 1) 1

(* This automatically define h_econstructor (among other things) *)
TACTIC EXTEND econstructor
  [ "econstructor" integer(n) "with" bindings(c) ] -> [ Util.anomaly "Eauto.econstructor: à restaurer" (* arnaud: e_constructor_tac None n c *) ]
| [ "econstructor" integer(n) ] -> [ Util.anomaly "Eauto.econstructor: à restaurer" (* arnaud: e_constructor_tac None n NoBindings *) ]
| [ "econstructor" tactic_opt(t) ] -> [ Util.anomaly "Eauto.econstructor: à restaurer" (* arnaud: e_any_constructor (Option.map Tacinterp.eval_tactic t) *) ] 
      END

TACTIC EXTEND eleft
  [ "eleft" "with" bindings(l) ] -> [Util.anomaly "Eauto.eleft: à restaurer" (* arnaud: e_left l*)]
| [ "eleft"] -> [Util.anomaly "Eauto.eleft: à restaurer" (* arnaud: e_left NoBindings*)]
END

TACTIC EXTEND eright
  [ "eright" "with" bindings(l) ] -> [Util.anomaly "Eauto.eright: à restaurer" (* arnaud: e_right l*)]
| [ "eright" ] -> [Util.anomaly "Eauto.eright: à restaurer" (* arnaud: e_right NoBindings*)]
END

TACTIC EXTEND esplit
  [ "esplit" "with" bindings(l) ] -> [Util.anomaly "Eauto.esplit: à restaurer" (* arnaud: e_split l *) ]
| [ "esplit"] -> [Util.anomaly "Eauto.esplit: à restaurer" (* arnaud: e_split NoBindings *)]
END


TACTIC EXTEND eexists
  [ "eexists" bindings(l) ] -> [Util.anomaly "Eauto.eexists: à restaurer" (* arnaud: e_split l*)]
END


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
      | _ -> error "Prolog called with a non closed argument"
  in
  try (prolog l n gl)
  with UserError ("Refiner.tclFIRST",_) ->
    errorlabstrm "Prolog.prolog" (str "Prolog failed")

TACTIC EXTEND prolog
| [ "prolog" "[" constr_list(l) "]" int_or_var(n) ] -> [ Util.anomaly "Eauto.prolog: à restaurer" (* prolog_tac l n *) ]
END

open Auto

(***************************************************************************)
(* A tactic similar to Auto, but using EApply, Assumption and e_give_exact *)
(***************************************************************************)

let unify_e_resolve  (c,clenv) gls = 
  let clenv' = connect_clenv gls clenv in
  let _ = clenv_unique_resolver false clenv' gls in
  h_simplest_eapply c gls

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
    fun {pri=b; pat = p; code=t} -> 
      (b, 
       let tac =
	 match t with
	   | Res_pf (term,cl) -> unify_resolve (term,cl)
	   | ERes_pf (term,cl) -> unify_e_resolve (term,cl)
	   | Give_exact (c) -> e_give_exact_constr c
	   | Res_pf_THEN_trivial_fail (term,cl) ->
               tclTHEN (unify_e_resolve (term,cl)) 
		 (e_trivial_fail_db db_list local_db)
	   | Unfold_nth c -> unfold_in_concl [[],c]
	   | Extern tacast -> conclPattern concl 
	       (Option.get p) tacast
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

let e_search_auto debug (in_depth,p) lems db_list gl = 
  let local_db = make_local_hint_db lems gl in 
  if in_depth then 
    e_depth_search debug p db_list local_db gl
  else 
    e_breadth_search debug p db_list local_db gl

let eauto debug np lems dbnames =
  let db_list =
    List.map
      (fun x -> 
	 try searchtable_map x
	 with Not_found -> error ("EAuto: "^x^": No such Hint database"))
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
  | _ -> error "EAuto called with a non closed argument"

let make_dimension n = function
  | None -> (true,make_depth n)
  | Some (ArgArg d) -> (false,d)
  | _ -> error "EAuto called with a non closed argument"

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
    [ Util.anomaly "Eauto.eauto: à restaurer" (* arnaud: gen_eauto false (make_dimension n p) lems db *) ]
END
