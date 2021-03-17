(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
open Tacticals
open Tacmach
open Evd
open Tactics
open Auto
open Genredexpr
open Tactypes
open Locus
open Locusops
open Hints
open Proofview.Notations

let eauto_unif_flags = auto_flags_of_state TransparentState.full

let e_give_exact ?(flags=eauto_unif_flags) c =
  Proofview.Goal.enter begin fun gl ->
  let sigma, t1 = Tacmach.New.pf_type_of gl c in
  let t2 = Tacmach.New.pf_concl gl in
  if occur_existential sigma t1 || occur_existential sigma t2 then
    Tacticals.New.tclTHENLIST
      [Proofview.Unsafe.tclEVARS sigma;
       Clenv.unify ~flags t1;
       exact_no_check c]
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

open Auto

(***************************************************************************)
(* A tactic similar to Auto, but using EApply, Assumption and e_give_exact *)
(***************************************************************************)

let unify_e_resolve flags h =
  Hints.hint_res_pf ~with_evars:true ~with_classes:true ~flags h

let hintmap_of env sigma secvars concl =
  (* Warning: for computation sharing, we need to return a closure *)
  let hdc = try Some (decompose_app_bound sigma concl) with Bound -> None in
  match hdc with
  | None -> fun db -> Hint_db.map_none ~secvars db
  | Some hdc ->
     if occur_existential sigma concl then
       (fun db ->
          match Hint_db.map_existential sigma ~secvars hdc concl db with
          | ModeMatch (_, l) -> l
          | ModeMismatch -> [])
     else (fun db -> Hint_db.map_auto env sigma ~secvars hdc concl db)
   (* FIXME: should be (Hint_db.map_eauto hdc concl db) *)

let e_exact flags h =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let sigma, c = Hints.fresh_hint env sigma h in
    Proofview.Unsafe.tclEVARS sigma <*> e_give_exact c
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
    (e_trivial_resolve (Tacmach.New.pf_env gl) (Tacmach.New.project gl) db_list local_db secvars (Tacmach.New.pf_concl gl))
  in
  Tacticals.New.tclSOLVE tacl
  end

and e_my_find_search env sigma db_list local_db secvars concl =
  let hint_of_db = hintmap_of env sigma secvars concl in
  let hintl =
      List.map_append (fun db ->
        let flags = auto_flags_of_state (Hint_db.transparent_state db) in
          List.map (fun x -> flags, x) (hint_of_db db)) (local_db::db_list)
  in
  let tac_of_hint =
    fun (st, h) ->
      let b = match FullHint.repr h with
      | Unfold_nth _ -> 1
      | _ -> FullHint.priority h
      in
      let tac = function
      | Res_pf h -> unify_resolve st h
      | ERes_pf h -> unify_e_resolve st h
      | Give_exact h -> e_exact st h
      | Res_pf_THEN_trivial_fail h ->
        Tacticals.New.tclTHEN (unify_e_resolve st h)
          (e_trivial_fail_db db_list local_db)
      | Unfold_nth c -> reduce (Unfold [AllOccurrences,c]) onConcl
      | Extern (pat, tacast) -> conclPattern concl pat tacast
      in
      let tac = FullHint.run h tac in
      (tac, b, lazy (FullHint.print env sigma h))
  in
  List.map tac_of_hint hintl

and e_trivial_resolve env sigma db_list local_db secvars gl =
  let filter (tac, pr, _) = if Int.equal pr 0 then Some tac else None in
  try List.map_filter filter (e_my_find_search env sigma db_list local_db secvars gl)
  with Not_found -> []

let e_possible_resolve env sigma db_list local_db secvars gl =
  try e_my_find_search env sigma db_list local_db secvars gl
  with Not_found -> []

(*s Tactics handling a list of goals. *)

(* first_goal : goal list sigma -> goal sigma *)

let find_first_goal gls =
  let gl = gls.Evd.it and sig_0 = gls.Evd.sigma in
  match gl with
  | [] -> assert false
  | (gl, db) :: _ ->
    { Evd.it = gl; Evd.sigma = sig_0; }, db

(*s The following module [SearchProblem] is used to instantiate the generic
    exploration functor [Explore.Make]. *)

type search_state = {
  priority : int;
  depth : int; (*r depth of search before failing *)
  tacres : (Goal.goal * hint_db) list sigma;
  last_tactic : Pp.t Lazy.t;
  dblist : hint_db list;
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

(* tactic -> tactic_list : Apply a tactic to the first goal in the list *)

  let apply_tac_list tac mkdb glls =
    match glls.it with
    | ((g1, db) :: rest) ->
        let pack = tac (re_sig g1 glls.sigma) in
        List.map (fun gl -> gl, mkdb db (re_sig gl pack.sigma)) pack.it, re_sig rest pack.sigma
    | _ -> user_err Pp.(str "apply_tac_list")

  let filter_tactics mkdb glls l =
(*     let _ = Proof_trees.db_pr_goal (List.hd (sig_it glls)) in *)
(*     let evars = Evarutil.nf_evars (Refiner.project glls) in *)
(*     msg (str"Goal:" ++ pr_ev evars (List.hd (sig_it glls)) ++ str"\n"); *)
    let rec aux = function
      | [] -> []
      | (tac, cost, pptac) :: tacl ->
          try
            let ngls, lgls = apply_tac_list (Proofview.V82.of_tactic tac) mkdb glls in
(* 	    let gl = Proof_trees.db_pr_goal (List.hd (sig_it glls)) in *)
(* 	      msg (hov 1 (pptac ++ str" gives: \n" ++ pr_goals lgls ++ str"\n")); *)
              (ngls, lgls, cost, pptac) :: aux tacl
          with e when CErrors.noncritical e ->
            let e = Exninfo.capture e in
            Tacticals.catch_failerror e; aux tacl
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
      let g, db = find_first_goal lg in
      let hyps = pf_ids_of_hyps g in
      let secvars = secvars_of_hyps (pf_hyps g) in
      let map_assum id = (e_give_exact (mkVar id), (-1), lazy (str "exact" ++ spc () ++ Id.print id)) in
      let assumption_tacs =
        let tacs = List.map map_assum hyps in
        let mkdb db gl = assert false in (* no goal can be generated *)
        let l = filter_tactics mkdb s.tacres tacs in
        List.map (fun (ngl, res, cost, pp) ->
          let () = assert (List.is_empty ngl) in
          { depth = s.depth; priority = cost; tacres = res;
                                    last_tactic = pp; dblist = s.dblist;
                                    prev = ps; local_lemmas = s.local_lemmas}) l
      in
      let intro_tac =
        let mkdb db gl =
          let hintl = make_resolve_hyp (pf_env gl) (project gl) (pf_last_hyp gl) in
          Hint_db.add_list (pf_env gl) (project gl) hintl db
        in
        let l = filter_tactics mkdb s.tacres [Tactics.intro, (-1), lazy (str "intro")] in
        List.map
          (fun (ngls, lgls, cost, pp) ->
             let lgls = re_sig (ngls @ lgls.it) lgls.sigma in
             { depth = s.depth; priority = cost; tacres = lgls;
               last_tactic = pp; dblist = s.dblist;
               prev = ps;
               local_lemmas = s.local_lemmas})
          l
      in
      let rec_tacs =
        let hyps = pf_hyps g in
        let mkdb db gls =
          let hyps' = pf_hyps gls in
            if hyps' == hyps then db
            else make_local_hint_db (pf_env gls) (project gls) ~ts:TransparentState.full true s.local_lemmas
        in
        let l =
          let concl = Reductionops.nf_evar (project g) (pf_concl g) in
          filter_tactics mkdb s.tacres
                         (e_possible_resolve (pf_env g) (project g) s.dblist db secvars concl)
        in
        List.map
          (fun (ngls, lgls, cost, pp) ->
            let lgls = re_sig (ngls @ lgls.it) lgls.sigma in
            let depth = if List.is_empty ngls then s.depth else pred s.depth in
            { depth; priority = cost; tacres = lgls; last_tactic = pp;
              prev = ps; dblist = s.dblist;
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

let () =
  Goptions.(declare_bool_option
    { optdepr  = false;
      optkey   = ["Debug";"Eauto"];
      optread  = (fun () -> !global_debug_eauto);
      optwrite = (:=) global_debug_eauto })

let () =
  Goptions.(declare_bool_option
    { optdepr  = false;
      optkey   = ["Info";"Eauto"];
      optread  = (fun () -> !global_info_eauto);
      optwrite = (:=) global_info_eauto })

let mk_eauto_dbg d =
  if d == Debug || !global_debug_eauto then Debug
  else if d == Info || !global_info_eauto then Info
  else Off

let pr_info_nop = function
  | Info -> Feedback.msg_notice (str "idtac.")
  | _ -> ()

let pr_dbg_header = function
  | Off -> ()
  | Debug -> Feedback.msg_notice (str "(* debug eauto: *)")
  | Info  -> Feedback.msg_notice (str "(* info eauto: *)")

let pr_info dbg s =
  if dbg != Info then ()
  else
    let rec loop s =
      match s.prev with
        | Unknown | Init -> s.depth
        | State sp ->
          let mindepth = loop sp in
          let indent = String.make (mindepth - sp.depth) ' ' in
          Feedback.msg_notice (str indent ++ Lazy.force s.last_tactic ++ str ".");
          mindepth
    in
    ignore (loop s)

(** Eauto main code *)

let make_initial_state dbg n gl dblist localdb lems =
  { depth = n;
    priority = 0;
    tacres = re_sig [gl.it, localdb] gl.sigma;
    last_tactic = lazy (mt());
    dblist = dblist;
    prev = if dbg == Info then Init else Unknown;
    local_lemmas = lems;
  }

let e_search_auto debug (in_depth,p) lems db_list =
  Proofview.V82.tactic ~nf_evars:false begin fun gl ->
  let local_db = make_local_hint_db (pf_env gl) (project gl) ~ts:TransparentState.full true lems in
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
    re_sig (List.map fst s.tacres.it) s.tacres.sigma
  with Not_found ->
    pr_info_nop d;
    tclIDTAC gl
  end

(* let e_search_auto_key = CProfile.declare_profile "e_search_auto" *)
(* let e_search_auto = CProfile.profile5 e_search_auto_key e_search_auto *)

let eauto_with_bases ?(debug=Off) np lems db_list =
  Hints.wrap_hint_warning (e_search_auto debug np lems db_list)

let eauto ?(debug=Off) np lems dbnames =
  let db_list = make_db_list dbnames in
  e_search_auto debug np lems db_list

let full_eauto ?(debug=Off) n lems =
  let db_list = current_pure_db () in
  e_search_auto debug n lems db_list

let gen_eauto ?(debug=Off) np lems = function
  | None -> Hints.wrap_hint_warning (full_eauto ~debug np lems)
  | Some l -> Hints.wrap_hint_warning (eauto ~debug np lems l)

let make_depth = function
  | None -> !default_search_depth
  | Some d -> d

let make_dimension n = function
  | None -> (true,make_depth n)
  | Some d -> (false,d)

let autounfolds ids csts gl cls =
  let open Tacred in
  let hyps = Tacmach.New.pf_ids_of_hyps gl in
  let env = Tacmach.New.pf_env gl in
  let ids = List.filter (fun id -> List.mem id hyps && Tacred.is_evaluable env (EvalVarRef id)) ids in
  let csts = List.filter (fun cst -> Tacred.is_evaluable env (EvalConstRef cst)) csts in
  let flags =
    List.fold_left (fun flags cst -> CClosure.RedFlags.(red_add flags (fCONST cst)))
      (List.fold_left (fun flags id -> CClosure.RedFlags.(red_add flags (fVAR id)))
         CClosure.betaiotazeta ids) csts
  in reduct_option ~check:false (Reductionops.clos_norm_flags flags, DEFAULTcast) cls

let cons a l = a :: l

exception UnknownDatabase of string

let autounfold db cls =
  if not (Locusops.clause_with_generic_occurrences cls) then
    user_err ~hdr:"autounfold" (str "\"at\" clause not supported");
  match List.fold_left (fun (ids, csts) dbname ->
    let db = try searchtable_map dbname
      with Not_found -> raise (UnknownDatabase dbname)
    in
    let (db_ids, db_csts) = Hint_db.unfolds db in
    (Id.Set.fold cons db_ids ids, Cset.fold cons db_csts csts)) ([], []) db
  with
  | (ids, csts) -> Proofview.Goal.enter begin fun gl ->
      let cls = concrete_clause_of (fun () -> Tacmach.New.pf_ids_of_hyps gl) cls in
      let tac = autounfolds ids csts gl in
      Tacticals.New.tclMAP (function
      | OnHyp (id, _, where) -> tac (Some (id, where))
      | OnConcl _ -> tac None) cls
    end
  | exception UnknownDatabase dbname -> Tacticals.New.tclZEROMSG (str "Unknown database " ++ str dbname)

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
        | true, f' -> true, Reductionops.whd_betaiota env sigma (mkApp (f', args))
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
      | Some hyp -> change_in_hyp ~check:true None (make_change_arg c') hyp
      | None -> convert_concl ~check:false c' DEFAULTcast
    else
      let info = Exninfo.reify () in
      Tacticals.New.tclFAIL ~info 0 (str "Nothing to unfold")
  end
