(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

open Pp
open Errors
open Util
open Names
open Nameops
open Term
open Termops
open Proof_type
open Tacticals
open Tacmach
open Tactics
open Patternops
open Clenv
open Auto
open Genredexpr
open Tacexpr
open Misctypes
open Locus
open Locusops
open Hints

DECLARE PLUGIN "eauto"

let eauto_unif_flags = auto_flags_of_state full_transparent_state

let e_give_exact ?(flags=eauto_unif_flags) c gl = let t1 = (pf_type_of gl c) and t2 = pf_concl gl in
  if occur_existential t1 || occur_existential t2 then
     tclTHEN (Proofview.V82.of_tactic (Clenvtac.unify ~flags t1)) (exact_no_check c) gl
  else Proofview.V82.of_tactic (exact_check c) gl

let assumption id = e_give_exact (mkVar id)

let e_assumption gl =
  tclFIRST (List.map assumption (pf_ids_of_hyps gl)) gl

TACTIC EXTEND eassumption
| [ "eassumption" ] -> [ Proofview.V82.tactic e_assumption ]
END

TACTIC EXTEND eexact
| [ "eexact" constr(c) ] -> [ Proofview.V82.tactic (e_give_exact c) ]
END

let registered_e_assumption gl =
  tclFIRST (List.map (fun id gl -> e_give_exact (mkVar id) gl)
              (pf_ids_of_hyps gl)) gl

(************************************************************************)
(*   PROLOG tactic                                                      *)
(************************************************************************)

(*s Tactics handling a list of goals. *)

(* first_goal : goal list sigma -> goal sigma *)

let first_goal gls =
  let gl = gls.Evd.it and sig_0 = gls.Evd.sigma in
  if List.is_empty gl then error "first_goal";
  { Evd.it = List.hd gl; Evd.sigma = sig_0; }

(* tactic -> tactic_list : Apply a tactic to the first goal in the list *)

let apply_tac_list tac glls =
  let (sigr,lg) = unpackage glls in
  match lg with
  | (g1::rest) ->
      let gl = apply_sig_tac sigr tac g1 in
      repackage sigr (gl@rest)
  | _ -> error "apply_tac_list"

let one_step l gl =
  [Proofview.V82.of_tactic Tactics.intro]
  @ (List.map (fun c -> Proofview.V82.of_tactic (Tactics.Simple.eapply c)) (List.map mkVar (pf_ids_of_hyps gl)))
  @ (List.map (fun c -> Proofview.V82.of_tactic (Tactics.Simple.eapply c)) l)
  @ (List.map assumption (pf_ids_of_hyps gl))

let rec prolog l n gl =
  if n <= 0 then error "prolog - failure";
  let prol = (prolog l (n-1)) in
  (tclFIRST (List.map (fun t -> (tclTHEN t prol)) (one_step l gl))) gl

let out_term = function
  | IsConstr (c, _) -> c
  | IsGlobRef gr -> fst (Universes.fresh_global_instance (Global.env ()) gr)

let prolog_tac l n gl =
  let l = List.map (fun x -> out_term (pf_apply (prepare_hint false) gl x)) l in
  let n =
    match n with
      | ArgArg n -> n
      | _ -> error "Prolog called with a non closed argument."
  in
  try (prolog l n gl)
  with UserError ("Refiner.tclFIRST",_) ->
    errorlabstrm "Prolog.prolog" (str "Prolog failed.")

TACTIC EXTEND prolog
| [ "prolog" "[" open_constr_list(l) "]" int_or_var(n) ] -> [ Proofview.V82.tactic (prolog_tac l n) ]
END

open Auto
open Unification

(***************************************************************************)
(* A tactic similar to Auto, but using EApply, Assumption and e_give_exact *)
(***************************************************************************)

let priority l = List.map snd (List.filter (fun (pr,_) -> Int.equal pr 0) l)

let unify_e_resolve poly flags (c,clenv) gls =
  let clenv', subst = if poly then Clenv.refresh_undefined_univs clenv 
  else clenv, Univ.empty_level_subst in
  let clenv' = connect_clenv gls clenv' in
  let clenv' = clenv_unique_resolver ~flags clenv' gls in
    tclTHEN (Refiner.tclEVARUNIVCONTEXT (Evd.evar_universe_context clenv'.evd))
      (Proofview.V82.of_tactic (Tactics.Simple.eapply (Vars.subst_univs_level_constr subst c))) gls

let e_exact poly flags (c,clenv) =
  let clenv', subst = 
    if poly then Clenv.refresh_undefined_univs clenv 
    else clenv, Univ.empty_level_subst
  in e_give_exact (* ~flags *) (Vars.subst_univs_level_constr subst c)
    
let rec e_trivial_fail_db db_list local_db goal =
  let tacl =
    registered_e_assumption ::
    (tclTHEN (Proofview.V82.of_tactic Tactics.intro)
       (function g'->
	  let d = pf_last_hyp g' in
	  let hintl = make_resolve_hyp (pf_env g') (project g') d in
          (e_trivial_fail_db db_list
	      (Hint_db.add_list hintl local_db) g'))) ::
    (List.map fst (e_trivial_resolve db_list local_db (pf_concl goal)) )
  in
    tclFIRST (List.map tclCOMPLETE tacl) goal

and e_my_find_search db_list local_db hdc concl =
  let hintl =
    if occur_existential concl then
      List.map_append (fun db ->
	let flags = auto_flags_of_state (Hint_db.transparent_state db) in
	  List.map (fun x -> flags, x) (Hint_db.map_existential hdc concl db)
   (* FIXME: should be (Hint_db.map_eauto hdc concl db) *)) (local_db::db_list)
    else
      List.map_append (fun db ->
	let flags = auto_flags_of_state (Hint_db.transparent_state db) in
	  List.map (fun x -> flags, x) (Hint_db.map_auto hdc concl db)) (local_db::db_list)
  in
  let tac_of_hint =
    fun (st, {pri = b; pat = p; code = t; poly = poly}) ->
      (b,
       let tac =
	 match t with
	   | Res_pf (term,cl) -> Proofview.V82.of_tactic (unify_resolve poly st (term,cl))
	   | ERes_pf (term,cl) -> unify_e_resolve poly st (term,cl)
	   | Give_exact (c,cl) -> e_exact poly st (c,cl)
	   | Res_pf_THEN_trivial_fail (term,cl) ->
               tclTHEN (unify_e_resolve poly st (term,cl))
		 (e_trivial_fail_db db_list local_db)
	   | Unfold_nth c -> reduce (Unfold [AllOccurrences,c]) onConcl
	   | Extern tacast -> Proofview.V82.of_tactic (conclPattern concl p tacast)
       in
       (tac,lazy (pr_autotactic t)))
  in
  List.map tac_of_hint hintl

and e_trivial_resolve db_list local_db gl =
  try
    priority
      (e_my_find_search db_list local_db
	 (decompose_app_bound gl) gl)
  with Bound | Not_found -> []

let e_possible_resolve db_list local_db gl =
  try List.map snd
    (e_my_find_search db_list local_db
	(decompose_app_bound gl) gl)
  with Bound | Not_found -> []

let find_first_goal gls =
  try first_goal gls with UserError _ -> assert false

(*s The following module [SearchProblem] is used to instantiate the generic
    exploration functor [Explore.Make]. *)

type search_state = {
  depth : int; (*r depth of search before failing *)
  tacres : goal list sigma;
  last_tactic : std_ppcmds Lazy.t;
  dblist : hint_db list;
  localdb :  hint_db list;
  prev : prev_search_state
}

and prev_search_state = (* for info eauto *)
  | Unknown
  | Init
  | State of search_state

module SearchProblem = struct

  type state = search_state

  let success s = List.is_empty (sig_it s.tacres)

(*   let pr_ev evs ev = Printer.pr_constr_env (Evd.evar_env ev) (Evarutil.nf_evar evs ev.Evd.evar_concl) *)

  let filter_tactics glls l =
(*     let _ = Proof_trees.db_pr_goal (List.hd (sig_it glls)) in *)
(*     let evars = Evarutil.nf_evars (Refiner.project glls) in *)
(*     msg (str"Goal:" ++ pr_ev evars (List.hd (sig_it glls)) ++ str"\n"); *)
    let rec aux = function
      | [] -> []
      | (tac,pptac) :: tacl ->
	  try
	    let lgls = apply_tac_list tac glls in
(* 	    let gl = Proof_trees.db_pr_goal (List.hd (sig_it glls)) in *)
(* 	      msg (hov 1 (pptac ++ str" gives: \n" ++ pr_goals lgls ++ str"\n")); *)
	      (lgls,pptac) :: aux tacl
	  with e when Errors.noncritical e ->
            let e = Errors.push e in
            Refiner.catch_failerror e; aux tacl
    in aux l

  (* Ordering of states is lexicographic on depth (greatest first) then
     number of remaining goals. *)
  let compare s s' =
    let d = s'.depth - s.depth in
    let nbgoals s = List.length (sig_it s.tacres) in
    if not (Int.equal d 0) then d else nbgoals s - nbgoals s'

  let branching s =
    if Int.equal s.depth 0 then
      []
    else
      let ps = if s.prev == Unknown then Unknown else State s in
      let lg = s.tacres in
      let nbgl = List.length (sig_it lg) in
      assert (nbgl > 0);
      let g = find_first_goal lg in
      let assumption_tacs =
	let l =
	  filter_tactics s.tacres
	    (List.map
	       (fun id -> (e_give_exact (mkVar id),
			   lazy (str "exact" ++ spc () ++ pr_id id)))
	       (pf_ids_of_hyps g))
	in
	List.map (fun (res,pp) -> { depth = s.depth; tacres = res;
				    last_tactic = pp; dblist = s.dblist;
				    localdb = List.tl s.localdb;
				    prev = ps}) l
      in
      let intro_tac =
	List.map
	  (fun (lgls as res,pp) ->
	     let g' = first_goal lgls in
	     let hintl =
	       make_resolve_hyp (pf_env g') (project g') (pf_last_hyp g')
	     in
             let ldb = Hint_db.add_list hintl (List.hd s.localdb) in
	     { depth = s.depth; tacres = res;
	       last_tactic = pp; dblist = s.dblist;
	       localdb = ldb :: List.tl s.localdb; prev = ps })
	  (filter_tactics s.tacres [Proofview.V82.of_tactic Tactics.intro,lazy (str "intro")])
      in
      let rec_tacs =
	let l =
	  filter_tactics s.tacres (e_possible_resolve s.dblist (List.hd s.localdb) (pf_concl g))
	in
	List.map
	  (fun (lgls as res, pp) ->
	     let nbgl' = List.length (sig_it lgls) in
	     if nbgl' < nbgl then
	       { depth = s.depth; tacres = res; last_tactic = pp; prev = ps;
		 dblist = s.dblist; localdb = List.tl s.localdb }
	     else
	       let newlocal = 
		 let hyps = pf_hyps g in
		   List.map (fun gl ->
		     let gls = {Evd.it = gl; sigma = lgls.Evd.sigma } in
		     let hyps' = pf_hyps gls in
		       if hyps' == hyps then List.hd s.localdb
		       else make_local_hint_db (pf_env gls) (project gls) ~ts:full_transparent_state true [])
		     (List.firstn ((nbgl'-nbgl) + 1) (sig_it lgls))
	       in
		 { depth = pred s.depth; tacres = res;
		   dblist = s.dblist; last_tactic = pp; prev = ps;
		   localdb = newlocal @ List.tl s.localdb })
	  l
      in
      List.sort compare (assumption_tacs @ intro_tac @ rec_tacs)

  let pp s = hov 0 (str " depth=" ++ int s.depth ++ spc () ++
		      (Lazy.force s.last_tactic))

end

module Search = Explore.Make(SearchProblem)

(** Utilities for debug eauto / info eauto *)

let global_debug_eauto = ref false
let global_info_eauto = ref false

let _ =
  Goptions.declare_bool_option
    { Goptions.optsync  = true;
      Goptions.optdepr  = false;
      Goptions.optname  = "Debug Eauto";
      Goptions.optkey   = ["Debug";"Eauto"];
      Goptions.optread  = (fun () -> !global_debug_eauto);
      Goptions.optwrite = (:=) global_debug_eauto }

let _ =
  Goptions.declare_bool_option
    { Goptions.optsync  = true;
      Goptions.optdepr  = false;
      Goptions.optname  = "Info Eauto";
      Goptions.optkey   = ["Info";"Eauto"];
      Goptions.optread  = (fun () -> !global_info_eauto);
      Goptions.optwrite = (:=) global_info_eauto }

let mk_eauto_dbg d =
  if d == Debug || !global_debug_eauto then Debug
  else if d == Info || !global_info_eauto then Info
  else Off

let pr_info_nop = function
  | Info -> msg_debug (str "idtac.")
  | _ -> ()

let pr_dbg_header = function
  | Off -> ()
  | Debug -> msg_debug (str "(* debug eauto : *)")
  | Info -> msg_debug (str "(* info eauto : *)")

let pr_info dbg s =
  if dbg != Info then ()
  else
    let rec loop s =
      match s.prev with
	| Unknown | Init -> s.depth
	| State sp ->
	  let mindepth = loop sp in
	  let indent = String.make (mindepth - sp.depth) ' ' in
	  msg_debug (str indent ++ Lazy.force s.last_tactic ++ str ".");
	  mindepth
    in
    ignore (loop s)

(** Eauto main code *)

let make_initial_state dbg n gl dblist localdb =
  { depth = n;
    tacres = tclIDTAC gl;
    last_tactic = lazy (mt());
    dblist = dblist;
    localdb = [localdb];
    prev = if dbg == Info then Init else Unknown;
  }

let e_search_auto debug (in_depth,p) lems db_list gl =
  let local_db = make_local_hint_db (pf_env gl) (project gl) ~ts:full_transparent_state true lems in
  let d = mk_eauto_dbg debug in
  let tac = match in_depth,d with
    | (true,Debug) -> Search.debug_depth_first
    | (true,_) -> Search.depth_first
    | (false,Debug) -> Search.debug_breadth_first
    | (false,_) -> Search.breadth_first
  in
  try
    pr_dbg_header d;
    let s = tac (make_initial_state d p gl db_list local_db) in
    pr_info d s;
    s.tacres
  with Not_found ->
    pr_info_nop d;
    error "eauto: search failed"

(* let e_search_auto_key = Profile.declare_profile "e_search_auto" *)
(* let e_search_auto = Profile.profile5 e_search_auto_key e_search_auto *)

let eauto_with_bases ?(debug=Off) np lems db_list =
  tclTRY (e_search_auto debug np lems db_list)

let eauto ?(debug=Off) np lems dbnames =
  let db_list = make_db_list dbnames in
  tclTRY (e_search_auto debug np lems db_list)

let full_eauto ?(debug=Off) n lems gl =
  let dbnames = current_db_names () in
  let dbnames =  String.Set.remove "v62" dbnames in
  let db_list = List.map searchtable_map (String.Set.elements dbnames) in
  tclTRY (e_search_auto debug n lems db_list) gl

let gen_eauto ?(debug=Off) np lems = function
  | None -> full_eauto ~debug np lems
  | Some l -> eauto ~debug np lems l

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

let pr_constr_coma_sequence prc _ _ =
  prlist_with_sep pr_comma (fun (_,c) -> prc c)

ARGUMENT EXTEND constr_coma_sequence
  TYPED AS open_constr_list
  PRINTED BY pr_constr_coma_sequence
| [ open_constr(c) "," constr_coma_sequence(l) ] -> [ c::l ]
| [ open_constr(c) ] -> [ [c] ]
END

let pr_auto_using prc _prlc _prt = Pptactic.pr_auto_using (fun (_,c) -> prc c)

ARGUMENT EXTEND auto_using
  TYPED AS open_constr_list
  PRINTED BY pr_auto_using
| [ "using" constr_coma_sequence(l) ] -> [ l ]
| [ ] -> [ [] ]
END

TACTIC EXTEND eauto
| [ "eauto" int_or_var_opt(n) int_or_var_opt(p) auto_using(lems)
    hintbases(db) ] ->
    [ Proofview.V82.tactic (gen_eauto (make_dimension n p) lems db) ]
END

TACTIC EXTEND new_eauto
| [ "new" "auto" int_or_var_opt(n) auto_using(lems)
    hintbases(db) ] ->
    [ match db with
      | None -> new_full_auto (make_depth n) lems
      | Some l -> new_auto (make_depth n) lems l ]
END

TACTIC EXTEND debug_eauto
| [ "debug" "eauto" int_or_var_opt(n) int_or_var_opt(p) auto_using(lems)
    hintbases(db) ] ->
    [ Proofview.V82.tactic (gen_eauto ~debug:Debug (make_dimension n p) lems db) ]
END

TACTIC EXTEND info_eauto
| [ "info_eauto" int_or_var_opt(n) int_or_var_opt(p) auto_using(lems)
    hintbases(db) ] ->
    [ Proofview.V82.tactic (gen_eauto ~debug:Info (make_dimension n p) lems db) ]
END

TACTIC EXTEND dfs_eauto
| [ "dfs" "eauto" int_or_var_opt(p) auto_using(lems)
      hintbases(db) ] ->
    [ Proofview.V82.tactic (gen_eauto (true, make_depth p) lems db) ]
END

let cons a l = a :: l

let autounfolds db occs cls gl =
  let unfolds = List.concat (List.map (fun dbname -> 
    let db = try searchtable_map dbname 
      with Not_found -> errorlabstrm "autounfold" (str "Unknown database " ++ str dbname)
    in
    let (ids, csts) = Hint_db.unfolds db in
    let hyps = pf_ids_of_hyps gl in
    let ids = Idset.filter (fun id -> List.mem id hyps) ids in
      Cset.fold (fun cst -> cons (AllOccurrences, EvalConstRef cst)) csts
	(Id.Set.fold (fun id -> cons (AllOccurrences, EvalVarRef id)) ids [])) db)
  in unfold_option unfolds cls gl

let autounfold db cls gl =
  let cls = concrete_clause_of (fun () -> pf_ids_of_hyps gl) cls in
  let tac = autounfolds db in
  tclMAP (function
    | OnHyp (id,occs,where) -> tac occs (Some (id,where))
    | OnConcl occs -> tac occs None)
    cls gl

let autounfold_tac db cls gl =
  let dbs = match db with
  | None -> String.Set.elements (current_db_names ())
  | Some [] -> ["core"]
  | Some l -> l
  in
  autounfold dbs  cls gl

TACTIC EXTEND autounfold
| [ "autounfold" hintbases(db) clause(cl) ] -> [ Proofview.V82.tactic (autounfold_tac db cl) ]
END

let unfold_head env (ids, csts) c = 
  let rec aux c = 
    match kind_of_term c with
    | Var id when Id.Set.mem id ids ->
	(match Environ.named_body id env with
	| Some b -> true, b
	| None -> false, c)
    | Const (cst,u as c) when Cset.mem cst csts ->
	true, Environ.constant_value_in env c
    | App (f, args) ->
	(match aux f with
	| true, f' -> true, Reductionops.whd_betaiota Evd.empty (mkApp (f', args))
	| false, _ -> 
	    let done_, args' = 
	      Array.fold_left_i (fun i (done_, acc) arg -> 
		if done_ then done_, arg :: acc 
		else match aux arg with
		| true, arg' -> true, arg' :: acc
		| false, arg' -> false, arg :: acc)
		(false, []) args
	    in 
	      if done_ then true, mkApp (f, Array.of_list (List.rev args'))
	      else false, c)
    | _ -> 
	let done_ = ref false in
	let c' = map_constr (fun c -> 
	  if !done_ then c else 
	    let x, c' = aux c in
	      done_ := x; c') c
	in !done_, c'
  in aux c

let autounfold_one db cl =
  Proofview.Goal.nf_enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let concl = Proofview.Goal.concl gl in
  let st =
    List.fold_left (fun (i,c) dbname -> 
      let db = try searchtable_map dbname 
	with Not_found -> errorlabstrm "autounfold" (str "Unknown database " ++ str dbname)
      in
      let (ids, csts) = Hint_db.unfolds db in
	(Id.Set.union ids i, Cset.union csts c)) (Id.Set.empty, Cset.empty) db
  in
  let did, c' = unfold_head env st 
    (match cl with Some (id, _) -> Tacmach.New.pf_get_hyp_typ id gl | None -> concl) 
  in
    if did then
      match cl with
      | Some hyp -> change_in_hyp None (fun sigma -> sigma, c') hyp
      | None -> convert_concl_no_check c' DEFAULTcast
    else Tacticals.New.tclFAIL 0 (str "Nothing to unfold")
  end

(* 	  Cset.fold (fun cst -> cons (all_occurrences, EvalConstRef cst)) csts *)
(* 	    (Id.Set.fold (fun id -> cons (all_occurrences, EvalVarRef id)) ids [])) db) *)
(*       in unfold_option unfolds cl *)

(*       let db = try searchtable_map dbname  *)
(* 	with Not_found -> errorlabstrm "autounfold" (str "Unknown database " ++ str dbname) *)
(*       in *)
(*       let (ids, csts) = Hint_db.unfolds db in *)
(* 	Cset.fold (fun cst -> tclORELSE (unfold_option [(occ, EvalVarRef id)] cst)) csts *)
(* 	  (Id.Set.fold (fun id -> tclORELSE (unfold_option [(occ, EvalVarRef id)] cl) ids acc))) *)
(*       (tclFAIL 0 (mt())) db *)
      
TACTIC EXTEND autounfold_one
| [ "autounfold_one" hintbases(db) "in" hyp(id) ] ->
    [ autounfold_one (match db with None -> ["core"] | Some x -> "core"::x) (Some (id, InHyp)) ]
| [ "autounfold_one" hintbases(db) ] ->
    [ autounfold_one (match db with None -> ["core"] | Some x -> "core"::x) None ]
      END

TACTIC EXTEND autounfoldify
| [ "autounfoldify" constr(x) ] -> [
  Proofview.V82.tactic (
    let db = match kind_of_term x with
      | Const (c,_) -> Label.to_string (con_label c)
      | _ -> assert false
    in autounfold ["core";db] onConcl 
  )]
END

TACTIC EXTEND unify
| ["unify" constr(x) constr(y) ] -> [ unify x y ]
| ["unify" constr(x) constr(y) "with" preident(base)  ] -> [
    let table = try Some (searchtable_map base) with Not_found -> None in
    match table with
    | None ->
      let msg = str "Hint table " ++ str base ++ str " not found" in
      Proofview.tclZERO (UserError ("", msg))
    | Some t ->
      let state = Hint_db.transparent_state t in
      unify ~state x y
  ]
END


TACTIC EXTEND convert_concl_no_check
| ["convert_concl_no_check" constr(x) ] -> [ convert_concl_no_check x DEFAULTcast ]
END


let pr_hints_path_atom prc _ _ a =
  match a with
  | PathAny -> str"."
  | PathHints grs ->
    pr_sequence Printer.pr_global grs

ARGUMENT EXTEND hints_path_atom
  TYPED AS hints_path_atom
  PRINTED BY pr_hints_path_atom
| [ global_list(g) ] -> [ PathHints (List.map Nametab.global g) ]
| [ "*" ] -> [ PathAny ]
END

let pr_hints_path prc prx pry c =
  let rec aux = function
  | PathAtom a -> pr_hints_path_atom prc prx pry a
  | PathStar p -> str"(" ++ aux p ++ str")*"
  | PathSeq (p, p') -> aux p ++ spc () ++ aux p'
  | PathOr (p, p') -> str "(" ++ aux p ++ str"|" ++ aux p' ++ str")"
  | PathEmpty -> str"ø"
  | PathEpsilon -> str"ε"
  in aux c

ARGUMENT EXTEND hints_path
  TYPED AS hints_path
  PRINTED BY pr_hints_path
| [ "(" hints_path(p) ")"  ] -> [ p ]
| [ "!" hints_path(p)  ] -> [ PathStar p ]
| [ "emp" ] -> [ PathEmpty ]
| [ "eps" ] -> [ PathEpsilon ]
| [ hints_path_atom(a) ] -> [ PathAtom a ]
| [ hints_path(p) "|" hints_path(q) ] -> [ PathOr (p, q) ]
| [ hints_path(p) ";" hints_path(q) ] -> [ PathSeq (p, q) ]
END

let pr_hintbases _prc _prlc _prt = Pptactic.pr_hintbases

ARGUMENT EXTEND opthints
  TYPED AS preident_list_opt
  PRINTED BY pr_hintbases
| [ ":" ne_preident_list(l) ] -> [ Some l ]
| [ ] -> [ None ]
END

VERNAC COMMAND EXTEND HintCut CLASSIFIED AS SIDEFF
| [ "Hint" "Cut" "[" hints_path(p) "]" opthints(dbnames) ] -> [
  let entry = HintsCutEntry p in
    Hints.add_hints (Locality.make_section_locality (Locality.LocalityFixme.consume ()))
      (match dbnames with None -> ["core"] | Some l -> l) entry ]
END
