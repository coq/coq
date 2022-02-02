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
open Tactics
open Auto
open Genredexpr
open Locus
open Locusops
open Hints
open Proofview.Notations

module NamedDecl = Context.Named.Declaration

let eauto_unif_flags = auto_flags_of_state TransparentState.full

let e_give_exact ?(flags=eauto_unif_flags) c =
  Proofview.Goal.enter begin fun gl ->
  let sigma, t1 = Tacmach.pf_type_of gl c in
  let t2 = Tacmach.pf_concl gl in
  if occur_existential sigma t1 || occur_existential sigma t2 then
    Tacticals.tclTHENLIST
      [Proofview.Unsafe.tclEVARS sigma;
       Clenv.unify ~flags t1;
       exact_no_check c]
  else exact_check c
  end

let e_assumption =
  Proofview.Goal.enter begin fun gl ->
    let hyps = Proofview.Goal.hyps gl in
    let sigma = Proofview.Goal.sigma gl in
    let concl = Tacmach.pf_concl gl in
    if List.is_empty hyps then
      Tacticals.tclZEROMSG (str "No applicable tactic.")
    else
      let not_ground = occur_existential sigma concl in
      let map decl =
        let id = NamedDecl.get_id decl in
        let t = NamedDecl.get_type decl in
        if not_ground || occur_existential sigma t then
          Clenv.unify ~flags:eauto_unif_flags t <*> exact_no_check (mkVar id)
        else
          exact_check (mkVar id)
      in
      Tacticals.tclFIRST (List.map map hyps)
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

type cost = {
  cost_priority : int;
  cost_subgoals : int option;
}

let hintmap_of env sigma secvars concl =
  (* Warning: for computation sharing, we need to return a closure *)
  let hdc = try Some (decompose_app_bound sigma concl) with Bound -> None in
  match hdc with
  | None -> fun db -> Hint_db.map_none ~secvars db
  | Some hdc ->
     if occur_existential sigma concl then
       (fun db ->
          match Hint_db.map_eauto env sigma ~secvars hdc concl db with
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
    let d = NamedDecl.get_id @@ Tacmach.pf_last_hyp gl in
    let local_db = push_resolve_hyp (Tacmach.pf_env gl) (Tacmach.project gl) d local_db in
    e_trivial_fail_db db_list local_db
  end in
  Proofview.Goal.enter begin fun gl ->
  let secvars = compute_secvars gl in
  let tacl =
    e_assumption ::
    (Tacticals.tclTHEN Tactics.intro next) ::
    (e_trivial_resolve (Tacmach.pf_env gl) (Tacmach.project gl) db_list local_db secvars (Tacmach.pf_concl gl))
  in
  Tacticals.tclSOLVE tacl
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
        Tacticals.tclTHEN (unify_e_resolve st h)
          (e_trivial_fail_db db_list local_db)
      | Unfold_nth c -> reduce (Unfold [AllOccurrences,c]) onConcl
      | Extern (pat, tacast) -> conclPattern concl pat tacast
      in
      let b = { cost_priority = b; cost_subgoals = FullHint.subgoals h } in
      let tac = FullHint.run h tac in
      (tac, b, lazy (FullHint.print env sigma h))
  in
  List.map tac_of_hint hintl

and e_trivial_resolve env sigma db_list local_db secvars gl =
  let filter (tac, pr, _) = if Int.equal pr.cost_priority 0 then Some tac else None in
  try List.map_filter filter (e_my_find_search env sigma db_list local_db secvars gl)
  with Not_found -> []

let e_possible_resolve env sigma db_list local_db secvars gl =
  try e_my_find_search env sigma db_list local_db secvars gl
  with Not_found -> []

type delayed_db = Environ.env -> Evd.evar_map -> hint_db

type search_state = {
  depth : int; (*r depth of search before failing *)
  tacres : (Proofview_monad.goal_with_state * delayed_db) list;
  last_tactic : Pp.t Lazy.t;
  prev : prev_search_state;
}

and prev_search_state = (* for info eauto *)
  | Unknown
  | Init
  | State of search_state

(*s Tactics handling a list of goals. *)

(* first_goal : goal list sigma -> goal sigma *)

module Search = struct

  let is_solved p = match p.cost_subgoals with
  | Some n -> Int.equal n 0
  | None -> assert false (* Ruled out by partial_eval *)

  let solve_order p1 p2 = match is_solved p1, is_solved p2 with
  | true, true | false, false -> 0
  | false, true -> 1
  | true, false -> -1 (* solved comes first *)

  let subgoals_order p1 p2 = match p1.cost_subgoals, p2.cost_subgoals with
  | Some n1, Some n2 -> Int.compare n1 n2
  | Some _, None -> -1
  | None, Some _ -> 1
  | None, None -> 0

  (* Ordering of states is lexicographic:
     1. tactics known to solve the goal
     2. priority
     3. number of generated goals. *)
  let compare (_, p1, _) (_, p2, _) =
    let d = solve_order p1 p2 in
    let d' = Int.compare p1.cost_priority p2.cost_priority in
    if not (Int.equal d 0) then d
    else if not (Int.equal d' 0) then d'
    else subgoals_order p1 p2

  (* We cannot determine statically the cost of an Extern hint, so we evaluate
     it locally, backtrack and return a dummy tactic that immediately sets the
     result. *)
  let partial_eval (tac, cost, pp) = match cost.cost_subgoals with
  | Some _ -> Proofview.tclUNIT (Some (tac, cost, pp))
  | None ->
    (* Assert that we are focussed *)
    Proofview.Goal.enter_one begin fun _ ->
    Proofview.tclORELSE (Proofview.UnsafeRepr.make begin
      let open Logic_monad.BackState in
      get >>= fun s ->
      Proofview.UnsafeRepr.repr (Proofview.tclONCE tac) >>= fun () ->
      get >>= fun r ->
      Proofview.UnsafeRepr.repr Proofview.numgoals >>= fun n ->
      set s >>= fun () ->
      let tac = Proofview.UnsafeRepr.make (set r) in
      let cost = { cost with cost_subgoals = Some n } in
      return (Some (tac, cost, pp))
    end) (fun _ -> Proofview.tclUNIT None)
    end

  let branching db dblist local_lemmas =
    Proofview.Goal.enter_one begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let concl = Proofview.Goal.concl gl in
    let hyps = EConstr.named_context env in
    let db = db env sigma in
    let secvars = secvars_of_hyps hyps in
    let assumption_tacs =
      let mkdb env sigma = assert false in (* no goal can be generated *)
      let map_assum id = (false, mkdb, e_give_exact (mkVar id), lazy (str "exact" ++ spc () ++ Id.print id)) in
      List.map map_assum (ids_of_named_context hyps)
    in
    let intro_tac =
      let mkdb env sigma =
        push_resolve_hyp env sigma (NamedDecl.get_id (List.hd (EConstr.named_context env))) db
      in
      (false, mkdb, Tactics.intro, lazy (str "intro"))
    in
    let rec_tacs =
      let mkdb env sigma =
        let hyps' = EConstr.named_context env in
          if hyps' == hyps then db
          else make_local_hint_db env sigma ~ts:TransparentState.full true local_lemmas
      in
      let tacs = e_possible_resolve env sigma dblist db secvars concl in
      Proofview.Monad.List.map_filter partial_eval tacs >>= fun tacs ->
      let tacs = List.sort compare tacs in
      let tacs = List.map (fun (tac, _, pp) -> (true, mkdb, tac, pp)) tacs in
      Proofview.tclUNIT tacs
    in
    rec_tacs >>= fun rec_tacs ->
    Proofview.tclUNIT (assumption_tacs @ intro_tac :: rec_tacs)
    end

  let msg_with_position (p : int list) s = match p with
  | [] -> ()
  | _ :: _ ->
    let pp = hov 0 (str " depth=" ++ int s.depth ++ spc () ++ (Lazy.force s.last_tactic)) in
    let rec pp_rec = function
      | [] -> mt ()
      | [i] -> int i
      | i :: l -> pp_rec l ++ str "." ++ int i
    in
    Feedback.msg_debug (h (pp_rec p) ++ pp)

  let push i p = match p with [] -> [] | _ :: _ -> i :: p

  exception SearchFailure

  let is_failure (e, _) = match e with SearchFailure -> true | _ -> false

  let search ?(debug=false) dblist local_lemmas s =
    let rec explore p s =
      let () = msg_with_position p s in
      if Int.equal s.depth 0 then Proofview.tclZERO SearchFailure
      else match s.tacres with
      | [] -> Proofview.tclUNIT s
      | (gl, db) :: rest ->
        Proofview.tclEVARMAP >>= fun sigma ->
        match Proofview.Unsafe.undefined sigma [gl] with
        | [] -> explore p { s with tacres = rest }
        | gl :: _ ->
          Proofview.Unsafe.tclSETGOALS [gl] <*>
          let ps = if s.prev == Unknown then Unknown else State s in
          branching db dblist local_lemmas >>= fun tacs ->
          let map (isrec, mkdb, tac, pp) =
            Proofview.tclONCE tac >>= fun () ->
            Proofview.Unsafe.tclGETGOALS >>= fun lgls ->
            Proofview.tclEVARMAP >>= fun sigma ->
            let map gl = gl, mkdb in
            let depth =
              if isrec then if List.is_empty lgls then s.depth else pred s.depth
              else s.depth
            in
            let lgls = List.map map lgls in
            Proofview.tclUNIT { depth; tacres = lgls @ rest; last_tactic = pp; prev = ps; }
          in
          let tacs = List.map map tacs in
          explore_many 1 p tacs

    and explore_many i p = function
    | [] -> Proofview.tclZERO SearchFailure
    | tac :: l ->
      Proofview.tclORELSE (tac >>= fun s -> explore (push i p) s)
        (fun e -> explore_many (if is_failure e then succ i else i) p l)
        (* discriminate between search failures and [tac] raising an error *)
    in
    let pos = if debug then [1] else [] in
    explore pos s

end

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

let make_initial_state evk dbg n localdb =
  { depth = n;
    tacres = [evk, localdb];
    last_tactic = lazy (mt());
    prev = if dbg == Info then Init else Unknown;
  }

let e_search_auto ?(debug = Off) ?depth lems db_list =
  Proofview.Goal.enter begin fun gl ->
  let p = Option.default !default_search_depth depth in
  let local_db env sigma = make_local_hint_db env sigma ~ts:TransparentState.full true lems in
  let d = mk_eauto_dbg debug in
  let debug = match d with Debug -> true | Info | Off -> false in
  let tac s = Search.search ~debug db_list lems s in
  let () = pr_dbg_header d in
  Proofview.tclORELSE
    begin
      let evk = Proofview.goal_with_state (Proofview.Goal.goal gl) (Proofview.Goal.state gl) in
      tac (make_initial_state evk d p local_db) >>= fun s ->
      let () = pr_info d s in
      let () = assert (List.is_empty s.tacres) in
      Proofview.Unsafe.tclSETGOALS []
    end
    begin function
    | (Search.SearchFailure, _) ->
      let () = pr_info_nop d in
      Proofview.tclUNIT ()
    | (e, info) -> Proofview.tclZERO ~info e
    end
  end

let eauto_with_bases ?debug ?depth lems db_list =
  Hints.wrap_hint_warning (e_search_auto ?debug ?depth lems db_list)

let gen_eauto ?debug ?depth lems dbs =
  let dbs = match dbs with None -> current_pure_db () | Some dbs -> make_db_list dbs in
  eauto_with_bases ?debug ?depth lems dbs

let autounfolds ids csts gl cls =
  let open Tacred in
  let hyps = Tacmach.pf_ids_of_hyps gl in
  let env = Tacmach.pf_env gl in
  let ids = List.filter (fun id -> List.mem id hyps && Tacred.is_evaluable env (EvalVarRef id)) ids in
  let csts = List.filter (fun cst -> Tacred.is_evaluable env (EvalConstRef cst)) csts in
  let flags =
    List.fold_left (fun flags cst -> CClosure.RedFlags.(red_add flags (fCONST cst)))
      (List.fold_left (fun flags id -> CClosure.RedFlags.(red_add flags (fVAR id)))
         (CClosure.RedFlags.red_add_transparent CClosure.all TransparentState.empty) ids) csts
  in reduct_option ~check:false (Reductionops.clos_norm_flags flags, DEFAULTcast) cls

let cons a l = a :: l

exception UnknownDatabase of string

let autounfold db cls =
  if not (Locusops.clause_with_generic_occurrences cls) then
    user_err (str "\"at\" clause not supported.");
  match List.fold_left (fun (ids, csts) dbname ->
    let db = try searchtable_map dbname
      with Not_found -> raise (UnknownDatabase dbname)
    in
    let (db_ids, db_csts) = Hint_db.unfolds db in
    (Id.Set.fold cons db_ids ids, Cset.fold cons db_csts csts)) ([], []) db
  with
  | (ids, csts) -> Proofview.Goal.enter begin fun gl ->
      let cls = concrete_clause_of (fun () -> Tacmach.pf_ids_of_hyps gl) cls in
      let tac = autounfolds ids csts gl in
      Tacticals.tclMAP (function
      | OnHyp (id, _, where) -> tac (Some (id, where))
      | OnConcl _ -> tac None) cls
    end
  | exception UnknownDatabase dbname -> Tacticals.tclZEROMSG (str "Unknown database " ++ str dbname)

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
  let sigma = Tacmach.project gl in
  let concl = Proofview.Goal.concl gl in
  let st =
    List.fold_left (fun (i,c) dbname ->
      let db = try searchtable_map dbname
        with Not_found -> user_err (str "Unknown database " ++ str dbname ++ str ".")
      in
      let (ids, csts) = Hint_db.unfolds db in
        (Id.Set.union ids i, Cset.union csts c)) (Id.Set.empty, Cset.empty) db
  in
  let did, c' = unfold_head env sigma st
    (match cl with Some (id, _) -> Tacmach.pf_get_hyp_typ id gl | None -> concl)
  in
    if did then
      match cl with
      | Some hyp -> change_in_hyp ~check:true None (make_change_arg c') hyp
      | None -> convert_concl ~cast:false ~check:false c' DEFAULTcast
    else
      let info = Exninfo.reify () in
      Tacticals.tclFAIL ~info (str "Nothing to unfold")
  end
