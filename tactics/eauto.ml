(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names
open Constr
open Termops
open EConstr
open Proof_type
open Tacticals
open Tacmach
open Evd
open Tactics
open Clenv
open Auto
open Genredexpr
open Tactypes
open Locus
open Locusops
open Hints
open Proofview.Notations

let eauto_unif_flags = auto_flags_of_state full_transparent_state

let e_give_exact ?(flags=eauto_unif_flags) c =
  Proofview.Goal.enter begin fun gl ->
  let t1 = Tacmach.New.pf_unsafe_type_of gl c in
  let t2 = Tacmach.New.pf_concl gl in
  let sigma = Tacmach.New.project gl in
  if occur_existential sigma t1 || occur_existential sigma t2 then
     Tacticals.New.tclTHEN (Clenvtac.unify ~flags t1) (exact_no_check c)
  else exact_check c
  end

let assumption id = e_give_exact (mkVar id)

let e_assumption =
  Proofview.Goal.enter begin fun gl ->
    Tacticals.New.tclFIRST (List.map assumption (Tacmach.New.pf_ids_of_hyps gl))
  end

let registered_e_assumption =
  Proofview.Goal.enter begin fun gl ->
  Tacticals.New.tclFIRST (List.map (fun id -> e_give_exact (mkVar id))
              (Tacmach.New.pf_ids_of_hyps gl))
  end

(************************************************************************)
(*   PROLOG tactic                                                      *)
(************************************************************************)

(*s Tactics handling a list of goals. *)

(* first_goal : goal list sigma -> goal sigma *)

let first_goal gls =
  let gl = gls.Evd.it and sig_0 = gls.Evd.sigma in
  if List.is_empty gl then user_err Pp.(str "first_goal");
  { Evd.it = List.hd gl; Evd.sigma = sig_0; }

(* tactic -> tactic_list : Apply a tactic to the first goal in the list *)

let apply_tac_list tac glls =
  match glls.it with
  | (g1::rest) ->
      let pack = tac (re_sig g1 glls.sigma) in
      re_sig (pack.it @ rest) pack.sigma
  | _ -> user_err Pp.(str "apply_tac_list")

let one_step l gl =
  [Proofview.V82.of_tactic Tactics.intro]
  @ (List.map (fun c -> Proofview.V82.of_tactic (Tactics.Simple.eapply c)) (List.map mkVar (pf_ids_of_hyps gl)))
  @ (List.map (fun c -> Proofview.V82.of_tactic (Tactics.Simple.eapply c)) l)
  @ (List.map (fun c -> Proofview.V82.of_tactic (assumption c)) (pf_ids_of_hyps gl))

let rec prolog l n gl =
  if n <= 0 then user_err Pp.(str "prolog - failure");
  let prol = (prolog l (n-1)) in
  (tclFIRST (List.map (fun t -> (tclTHEN t prol)) (one_step l gl))) gl

let out_term env = function
  | IsConstr (c, _) -> c
  | IsGlobRef gr -> EConstr.of_constr (fst (UnivGen.fresh_global_instance env gr))

let prolog_tac l n =
  Proofview.V82.tactic begin fun gl ->
  let map c =
    let (sigma, c) = c (pf_env gl) (project gl) in
    let c = pf_apply (prepare_hint false (false,true)) gl (sigma, c) in
    out_term (pf_env gl) c
  in
  let l = List.map map l in
  try (prolog l n gl)
  with UserError (Some "Refiner.tclFIRST",_) ->
    user_err ~hdr:"Prolog.prolog" (str "Prolog failed.")
  end

open Auto

(***************************************************************************)
(* A tactic similar to Auto, but using EApply, Assumption and e_give_exact *)
(***************************************************************************)

let priority l = List.map snd (List.filter (fun (pr,_) -> Int.equal pr 0) l)

let unify_e_resolve poly flags (c,clenv) =
  Proofview.Goal.enter begin fun gl ->
      let clenv', c = connect_hint_clenv poly c clenv gl in
      let clenv' = clenv_unique_resolver ~flags clenv' gl in
      Proofview.tclTHEN
        (Proofview.Unsafe.tclEVARUNIVCONTEXT (Evd.evar_universe_context clenv'.evd))
        (Tactics.Simple.eapply c)
    end

let hintmap_of sigma secvars hdc concl =
  match hdc with
  | None -> fun db -> Hint_db.map_none ~secvars db
  | Some hdc ->
     if occur_existential sigma concl then
       (fun db -> Hint_db.map_existential sigma ~secvars hdc concl db)
     else (fun db -> Hint_db.map_auto sigma ~secvars hdc concl db)
   (* FIXME: should be (Hint_db.map_eauto hdc concl db) *)

let e_exact poly flags (c,clenv) =
  Proofview.Goal.enter begin fun gl ->
    let clenv', c = connect_hint_clenv poly c clenv gl in
    Tacticals.New.tclTHEN
    (Proofview.Unsafe.tclEVARUNIVCONTEXT (Evd.evar_universe_context clenv'.evd))
    (e_give_exact c)
  end

let rec e_trivial_fail_db db_list local_db =
  let next = Proofview.Goal.enter begin fun gl ->
    let d = Tacmach.New.pf_last_hyp gl in
    let hintl = make_resolve_hyp (Tacmach.New.pf_env gl) (Tacmach.New.project gl) d in
    e_trivial_fail_db db_list (Hint_db.add_list (Tacmach.New.pf_env gl) (Tacmach.New.project gl) hintl local_db)
  end in
  Proofview.Goal.enter begin fun gl ->
  let secvars = compute_secvars gl in
  let tacl =
    registered_e_assumption ::
    (Tacticals.New.tclTHEN Tactics.intro next) ::
    (List.map fst (e_trivial_resolve (Tacmach.New.pf_env gl) (Tacmach.New.project gl) db_list local_db secvars (Tacmach.New.pf_concl gl)))
  in
  Tacticals.New.tclFIRST (List.map Tacticals.New.tclCOMPLETE tacl)
  end

and e_my_find_search env sigma db_list local_db secvars hdc concl =
  let hint_of_db = hintmap_of sigma secvars hdc concl in
  let hintl =
      List.map_append (fun db ->
	let flags = auto_flags_of_state (Hint_db.transparent_state db) in
	  List.map (fun x -> flags, x) (hint_of_db db)) (local_db::db_list)
  in
  let tac_of_hint =
    fun (st, {pri = b; pat = p; code = t; poly = poly}) ->
      let b = match Hints.repr_hint t with
      | Unfold_nth _ -> 1
      | _ -> b
      in
      (b,
        let tac = function
        | Res_pf (term,cl) -> unify_resolve poly st (term,cl)
        | ERes_pf (term,cl) -> unify_e_resolve poly st (term,cl)
        | Give_exact (c,cl) -> e_exact poly st (c,cl)
        | Res_pf_THEN_trivial_fail (term,cl) ->
          Tacticals.New.tclTHEN (unify_e_resolve poly st (term,cl))
            (e_trivial_fail_db db_list local_db)
        | Unfold_nth c -> reduce (Unfold [AllOccurrences,c]) onConcl
        | Extern tacast -> conclPattern concl p tacast
       in
       let tac = run_hint t tac in
       (tac, lazy (pr_hint env sigma t)))
  in
  List.map tac_of_hint hintl

and e_trivial_resolve env sigma db_list local_db secvars gl =
  let hd = try Some (decompose_app_bound sigma gl) with Bound -> None in
  try priority (e_my_find_search env sigma db_list local_db secvars hd gl)
  with Not_found -> []

let e_possible_resolve env sigma db_list local_db secvars gl =
  let hd = try Some (decompose_app_bound sigma gl) with Bound -> None in
  try List.map (fun (b, (tac, pp)) -> (tac, b, pp))
               (e_my_find_search env sigma db_list local_db secvars hd gl)
  with Not_found -> []

let find_first_goal gls =
  try first_goal gls with UserError _ -> assert false

(*s The following module [SearchProblem] is used to instantiate the generic
    exploration functor [Explore.Make]. *)

type search_state = {
  priority : int;
  depth : int; (*r depth of search before failing *)
  tacres : goal list sigma;
  last_tactic : Pp.t Lazy.t;
  dblist : hint_db list;
  localdb :  hint_db list;
  prev : prev_search_state;
  local_lemmas : delayed_open_constr list;
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
      | (tac, cost, pptac) :: tacl ->
	  try
	    let lgls = apply_tac_list (Proofview.V82.of_tactic tac) glls in
(* 	    let gl = Proof_trees.db_pr_goal (List.hd (sig_it glls)) in *)
(* 	      msg (hov 1 (pptac ++ str" gives: \n" ++ pr_goals lgls ++ str"\n")); *)
	      (lgls, cost, pptac) :: aux tacl
	  with e when CErrors.noncritical e ->
            let e = CErrors.push e in
            Refiner.catch_failerror e; aux tacl
    in aux l

  (* Ordering of states is lexicographic on depth (greatest first) then
     number of remaining goals. *)
  let compare s s' =
    let d = s'.depth - s.depth in
    let d' = Int.compare s.priority s'.priority in
    let nbgoals s = List.length (sig_it s.tacres) in
    if not (Int.equal d 0) then d
    else if not (Int.equal d' 0) then d'
    else Int.compare (nbgoals s) (nbgoals s')

  let branching s =
    if Int.equal s.depth 0 then
      []
    else
      let ps = if s.prev == Unknown then Unknown else State s in
      let lg = s.tacres in
      let nbgl = List.length (sig_it lg) in
      assert (nbgl > 0);
      let g = find_first_goal lg in
      let hyps = pf_ids_of_hyps g in
      let secvars = secvars_of_hyps (pf_hyps g) in
      let map_assum id = (e_give_exact (mkVar id), (-1), lazy (str "exact" ++ spc () ++ Id.print id)) in
      let assumption_tacs =
        let tacs = List.map map_assum hyps in
        let l = filter_tactics s.tacres tacs in
	List.map (fun (res, cost, pp) -> { depth = s.depth; priority = cost; tacres = res;
				    last_tactic = pp; dblist = s.dblist;
				    localdb = List.tl s.localdb;
				    prev = ps; local_lemmas = s.local_lemmas}) l
      in
      let intro_tac =
        let l = filter_tactics s.tacres [Tactics.intro, (-1), lazy (str "intro")] in
	List.map
	  (fun (lgls, cost, pp) ->
	     let g' = first_goal lgls in
	     let hintl =
	       make_resolve_hyp (pf_env g') (project g') (pf_last_hyp g')
	     in
             let ldb = Hint_db.add_list (pf_env g') (project g')
		  hintl (List.hd s.localdb) in
	     { depth = s.depth; priority = cost; tacres = lgls;
	       last_tactic = pp; dblist = s.dblist;
	       localdb = ldb :: List.tl s.localdb; prev = ps;
               local_lemmas = s.local_lemmas})
	  l
      in
      let rec_tacs =
	let l =
          let concl = Reductionops.nf_evar (project g) (pf_concl g) in
	  filter_tactics s.tacres
                         (e_possible_resolve (pf_env g) (project g) s.dblist (List.hd s.localdb) secvars concl)
	in
	List.map
	  (fun (lgls, cost, pp) ->
	     let nbgl' = List.length (sig_it lgls) in
	     if nbgl' < nbgl then
	       { depth = s.depth; priority = cost; tacres = lgls; last_tactic = pp;
                  prev = ps; dblist = s.dblist; localdb = List.tl s.localdb;
                  local_lemmas = s.local_lemmas }
	     else
	       let newlocal = 
		 let hyps = pf_hyps g in
		   List.map (fun gl ->
		     let gls = {Evd.it = gl; sigma = lgls.Evd.sigma } in
		     let hyps' = pf_hyps gls in
		       if hyps' == hyps then List.hd s.localdb
		       else make_local_hint_db (pf_env gls) (project gls) ~ts:full_transparent_state true s.local_lemmas)
		     (List.firstn ((nbgl'-nbgl) + 1) (sig_it lgls))
	       in
		 { depth = pred s.depth; priority = cost; tacres = lgls;
		   dblist = s.dblist; last_tactic = pp; prev = ps;
		   localdb = newlocal @ List.tl s.localdb;
                   local_lemmas = s.local_lemmas })
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
    { Goptions.optdepr  = false;
      Goptions.optname  = "Debug Eauto";
      Goptions.optkey   = ["Debug";"Eauto"];
      Goptions.optread  = (fun () -> !global_debug_eauto);
      Goptions.optwrite = (:=) global_debug_eauto }

let _ =
  Goptions.declare_bool_option
    { Goptions.optdepr  = false;
      Goptions.optname  = "Info Eauto";
      Goptions.optkey   = ["Info";"Eauto"];
      Goptions.optread  = (fun () -> !global_info_eauto);
      Goptions.optwrite = (:=) global_info_eauto }

let mk_eauto_dbg d =
  if d == Debug || !global_debug_eauto then Debug
  else if d == Info || !global_info_eauto then Info
  else Off

let pr_info_nop = function
  | Info -> Feedback.msg_info (str "idtac.")
  | _ -> ()

let pr_dbg_header = function
  | Off -> ()
  | Debug -> Feedback.msg_debug (str "(* debug eauto: *)")
  | Info  -> Feedback.msg_info (str "(* info eauto: *)")

let pr_info dbg s =
  if dbg != Info then ()
  else
    let rec loop s =
      match s.prev with
	| Unknown | Init -> s.depth
	| State sp ->
	  let mindepth = loop sp in
	  let indent = String.make (mindepth - sp.depth) ' ' in
	  Feedback.msg_info (str indent ++ Lazy.force s.last_tactic ++ str ".");
	  mindepth
    in
    ignore (loop s)

(** Eauto main code *)

let make_initial_state dbg n gl dblist localdb lems =
  { depth = n;
    priority = 0;
    tacres = tclIDTAC gl;
    last_tactic = lazy (mt());
    dblist = dblist;
    localdb = [localdb];
    prev = if dbg == Info then Init else Unknown;
    local_lemmas = lems;
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
    let s = tac (make_initial_state d p gl db_list local_db lems) in
    pr_info d s;
    s.tacres
  with Not_found ->
    pr_info_nop d;
    user_err Pp.(str "eauto: search failed")

(* let e_search_auto_key = CProfile.declare_profile "e_search_auto" *)
(* let e_search_auto = CProfile.profile5 e_search_auto_key e_search_auto *)

let eauto_with_bases ?(debug=Off) np lems db_list =
  tclTRY (e_search_auto debug np lems db_list)

let eauto ?(debug=Off) np lems dbnames =
  let db_list = make_db_list dbnames in
  tclTRY (e_search_auto debug np lems db_list)

let full_eauto ?(debug=Off) n lems gl =
  let db_list = current_pure_db () in
  tclTRY (e_search_auto debug n lems db_list) gl

let gen_eauto ?(debug=Off) np lems = function
  | None -> Proofview.V82.tactic (full_eauto ~debug np lems)
  | Some l -> Proofview.V82.tactic (eauto ~debug np lems l)

let make_depth = function
  | None -> !default_search_depth
  | Some d -> d

let make_dimension n = function
  | None -> (true,make_depth n)
  | Some d -> (false,d)

let cons a l = a :: l

let autounfolds db occs cls gl =
  let unfolds = List.concat (List.map (fun dbname -> 
    let db = try searchtable_map dbname 
      with Not_found -> user_err ~hdr:"autounfold" (str "Unknown database " ++ str dbname)
    in
    let (ids, csts) = Hint_db.unfolds db in
    let hyps = pf_ids_of_hyps gl in
    let ids = Id.Set.filter (fun id -> List.mem id hyps) ids in
      Cset.fold (fun cst -> cons (AllOccurrences, EvalConstRef cst)) csts
	(Id.Set.fold (fun id -> cons (AllOccurrences, EvalVarRef id)) ids [])) db)
  in Proofview.V82.of_tactic (unfold_option unfolds cls) gl

let autounfold db cls =
  Proofview.V82.tactic begin fun gl ->
  let cls = concrete_clause_of (fun () -> pf_ids_of_hyps gl) cls in
  let tac = autounfolds db in
  tclMAP (function
    | OnHyp (id,occs,where) -> tac occs (Some (id,where))
    | OnConcl occs -> tac occs None)
    cls gl
  end

let autounfold_tac db cls =
  Proofview.tclUNIT () >>= fun () ->
  let dbs = match db with
  | None -> String.Set.elements (current_db_names ())
  | Some [] -> ["core"]
  | Some l -> l
  in
  autounfold dbs cls

let unfold_head env sigma (ids, csts) c =
  let rec aux c = 
    match EConstr.kind sigma c with
    | Var id when Id.Set.mem id ids ->
	(match Environ.named_body id env with
	| Some b -> true, EConstr.of_constr b
	| None -> false, c)
    | Const (cst, u) when Cset.mem cst csts ->
        let u = EInstance.kind sigma u in
	true, EConstr.of_constr (Environ.constant_value_in env (cst, u))
    | App (f, args) ->
	(match aux f with
	| true, f' -> true, Reductionops.whd_betaiota sigma (mkApp (f', args))
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
	let c' = EConstr.map sigma (fun c -> 
	  if !done_ then c else 
	    let x, c' = aux c in
	      done_ := x; c') c
	in !done_, c'
  in aux c

let autounfold_one db cl =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.New.project gl in
  let concl = Proofview.Goal.concl gl in
  let st =
    List.fold_left (fun (i,c) dbname -> 
      let db = try searchtable_map dbname 
	with Not_found -> user_err ~hdr:"autounfold" (str "Unknown database " ++ str dbname)
      in
      let (ids, csts) = Hint_db.unfolds db in
	(Id.Set.union ids i, Cset.union csts c)) (Id.Set.empty, Cset.empty) db
  in
  let did, c' = unfold_head env sigma st 
    (match cl with Some (id, _) -> Tacmach.New.pf_get_hyp_typ id gl | None -> concl) 
  in
    if did then
      match cl with
      | Some hyp -> change_in_hyp None (make_change_arg c') hyp
      | None -> convert_concl_no_check c' DEFAULTcast
    else Tacticals.New.tclFAIL 0 (str "Nothing to unfold")
  end
