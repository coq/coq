(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open Names
open Termops
open Tactics
open Proofview.Notations
open Hints

(**************************************************************************)
(*                           Automatic tactics                            *)
(**************************************************************************)

(**************************************************************************)
(*          tactics with a trace mechanism for automatic search           *)
(**************************************************************************)

let compute_secvars gl =
  let hyps = Proofview.Goal.hyps gl in
  secvars_of_hyps hyps

(* tell auto not to reuse already instantiated metas in unification (for
   compatibility, since otherwise, apply succeeds oftener) *)

open Unification

let auto_core_unif_flags_of st1 st2 = {
  modulo_conv_on_closed_terms = Some st1;
  use_metas_eagerly_in_conv_on_closed_terms = true;
  use_evars_eagerly_in_conv_on_closed_terms = false;
  modulo_delta = st2;
  modulo_delta_types = TransparentState.full;
  check_applied_meta_types = false;
  use_pattern_unification = false;
  use_meta_bound_pattern_unification = true;
  allowed_evars = Evarsolve.AllowedEvars.all;
  restrict_conv_on_strict_subterms = false; (* Compat *)
  modulo_betaiota = false;
  modulo_eta = true;
}

let auto_unif_flags_of st1 st2 =
  let flags = auto_core_unif_flags_of st1 st2 in {
  core_unify_flags = flags;
  merge_unify_flags = flags;
  subterm_unify_flags = { flags with modulo_delta = TransparentState.empty };
  allow_K_in_toplevel_higher_order_unification = false;
  resolve_evars = true
}

let auto_unif_flags =
  auto_unif_flags_of TransparentState.full TransparentState.empty

(* Try unification with the precompiled clause, then use registered Apply *)

let unify_resolve flags h = Hints.hint_res_pf ~flags h
let unify_resolve_nodelta h = Hints.hint_res_pf ~flags:auto_unif_flags h

let exact h =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let sigma, c = Hints.fresh_hint env sigma h in
    let sigma, t = Typing.type_of env sigma c in
    let concl = Proofview.Goal.concl gl in
    if occur_existential sigma t || occur_existential sigma concl then
      try
        let _, sigma = Unification.w_unify env sigma CONV ~flags:auto_unif_flags concl t in
        Proofview.Unsafe.tclEVARSADVANCE sigma <*>
        exact_no_check c
      with e when CErrors.noncritical e -> Proofview.tclZERO e
    else Proofview.Unsafe.tclEVARS sigma <*> exact_check c
  end

(* Util *)

(* Serait-ce possible de compiler d'abord la tactique puis de faire la
   substitution sans passer par bdize dont l'objectif est de préparer un
   terme pour l'affichage ? (HH) *)

(* Si on enlève le dernier argument (gl) conclPattern est calculé une
fois pour toutes : en particulier si Pattern.somatch produit une UserError
Ce qui fait que si la conclusion ne matche pas le pattern, Auto échoue, même
si après Intros la conclusion matche le pattern.
*)

(* conclPattern doit échouer avec error car il est rattraper par tclFIRST *)

let conclPattern concl pat tac =
  let constr_bindings env sigma =
    match pat with
    | None -> Proofview.tclUNIT Id.Map.empty
    | Some pat ->
        try
          Proofview.tclUNIT (Constr_matching.matches env sigma pat concl)
        with Constr_matching.PatternMatchingFailure as exn ->
          let _, info = Exninfo.capture exn in
          Tacticals.tclZEROMSG ~info (str "pattern-matching failed")
  in
  Proofview.Goal.enter begin fun gl ->
     let env = Proofview.Goal.env gl in
     let sigma = Proofview.Goal.sigma gl in
     constr_bindings env sigma >>= fun constr_bindings ->
     Proofview.tclProofInfo [@ocaml.warning "-3"] >>= fun (_name, poly) ->
     let open Genarg in
     let open Geninterp in
     let inj c = Geninterp.Val.inject (val_tag (topwit Stdarg.wit_constr)) c in
     let fold id c accu = Id.Map.add id (inj c) accu in
     let lfun = Id.Map.fold fold constr_bindings Id.Map.empty in
     let ist = { lfun
               ; poly
               ; extra = TacStore.empty }
     in
     Ftactic.run (Geninterp.generic_interp ist tac) (fun _ -> Proofview.tclUNIT ())
  end

(***********************************************************)
(** A debugging / verbosity framework for trivial and auto *)
(***********************************************************)

(** The following options allow to trigger debugging/verbosity
    without having to adapt the scripts.
    Note: if Debug and Info are both activated, Debug take precedence. *)

let global_debug_trivial = ref false
let global_debug_auto = ref false
let global_info_trivial = ref false
let global_info_auto = ref false

let add_option ls refe =
  Goptions.(declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ls;
      optread  = (fun () -> !refe);
      optwrite = (:=) refe })

let () =
  add_option ["Debug";"Trivial"] global_debug_trivial;
  add_option ["Debug";"Auto"] global_debug_auto;
  add_option ["Info";"Trivial"] global_info_trivial;
  add_option ["Info";"Auto"] global_info_auto

type debug_kind = ReportForTrivial | ReportForAuto

let no_dbg (_,whatfor,_,_) = (Off,whatfor,0,ref [])

let mk_trivial_dbg debug =
  let d =
    if debug == Debug || !global_debug_trivial then Debug
    else if debug == Info || !global_info_trivial then Info
    else Off
  in (d,ReportForTrivial,0,ref [])

let mk_auto_dbg debug =
  let d =
    if debug == Debug || !global_debug_auto then Debug
    else if debug == Info || !global_info_auto then Info
    else Off
  in (d,ReportForAuto,0,ref [])

let incr_dbg = function (dbg,whatfor,depth,trace) -> (dbg,whatfor,depth+1,trace)

(** A tracing tactic for debug/info trivial/auto *)

let tclLOG (dbg,_,depth,trace) pp tac =
  match dbg with
    | Off -> tac
    | Debug ->
      (* For "debug (trivial/auto)", we directly output messages *)
      let s = String.make (depth+1) '*' in
      Proofview.(tclIFCATCH (
          tac >>= fun v ->
          tclENV >>= fun env ->
          tclEVARMAP >>= fun sigma ->
          Feedback.msg_notice (str s ++ spc () ++ pp env sigma ++ str ". (*success*)");
          tclUNIT v
        ) tclUNIT
          (fun (exn, info) ->
             tclENV >>= fun env ->
             tclEVARMAP >>= fun sigma ->
             Feedback.msg_notice (str s ++ spc () ++ pp env sigma ++ str ". (*fail*)");
             tclZERO ~info exn))
    | Info ->
      (* For "info (trivial/auto)", we store a log trace *)
      Proofview.(tclIFCATCH (
          tac >>= fun v ->
          trace := (depth, Some pp) :: !trace;
          tclUNIT v
        ) Proofview.tclUNIT
          (fun (exn, info) ->
             trace := (depth, None) :: !trace;
             tclZERO ~info exn))

(** For info, from the linear trace information, we reconstitute the part
    of the proof tree we're interested in. The last executed tactic
    comes first in the trace (and it should be a successful one).
    [depth] is the root depth of the tree fragment we're visiting.
    [keep] means we're in a successful tree fragment (the very last
    tactic has been successful). *)

let rec cleanup_info_trace depth acc = function
  | [] -> acc
  | (d,Some pp) :: l -> cleanup_info_trace d ((d,pp)::acc) l
  | l -> cleanup_info_trace depth acc (erase_subtree depth l)

and erase_subtree depth = function
  | [] -> []
  | (d,_) :: l -> if Int.equal d depth then l else erase_subtree depth l

let pr_info_atom env sigma (d,pp) =
  str (String.make d ' ') ++ pp env sigma ++ str "."

let pr_info_trace env sigma = function
  | (Info,_,_,{contents=(d,Some pp)::l}) ->
    Feedback.msg_notice (prlist_with_sep fnl (pr_info_atom env sigma) (cleanup_info_trace d [(d,pp)] l))
  | _ -> ()

let pr_info_nop = function
  | (Info,_,_,_) -> Feedback.msg_notice (str "idtac.")
  | _ -> ()

let pr_dbg_header = function
  | (Off,_,_,_) -> ()
  | (Debug,ReportForTrivial,_,_) -> Feedback.msg_notice (str "(* debug trivial: *)")
  | (Debug,ReportForAuto,_,_) -> Feedback.msg_notice (str "(* debug auto: *)")
  | (Info,ReportForTrivial,_,_) -> Feedback.msg_notice (str "(* info trivial: *)")
  | (Info,ReportForAuto,_,_) -> Feedback.msg_notice (str "(* info auto: *)")

let tclTRY_dbg d tac =
  let delay f = Proofview.tclUNIT () >>= fun () -> f () in
  let tac =
    delay (fun () -> pr_dbg_header d; tac) >>= fun () ->
      Proofview.tclENV >>= fun env ->
      Proofview.tclEVARMAP >>= fun sigma ->
      pr_info_trace env sigma d;
      Proofview.tclUNIT () in
  let after = delay (fun () -> pr_info_nop d; Proofview.tclUNIT ()) in
  Tacticals.tclORELSE0 tac after

(**************************************************************************)
(*                           The Trivial tactic                           *)
(**************************************************************************)

(* local_db is a Hint database containing the hypotheses of current goal *)
(* Papageno : cette fonction a été pas mal simplifiée depuis que la base
  de Hint impérative a été remplacée par plusieurs bases fonctionnelles *)

let auto_flags_of_state st =
  auto_unif_flags_of TransparentState.full st

let hintmap_of env sigma secvars hdc concl =
  match hdc with
  | None -> Hint_db.map_none ~secvars
  | Some hdc ->
      if occur_existential sigma concl then
        (fun db -> match Hint_db.map_eauto env sigma ~secvars hdc concl db with
                   | ModeMatch (_, l) -> l
                   | ModeMismatch -> [])
      else Hint_db.map_auto env sigma ~secvars hdc concl

let exists_evaluable_reference env = function
  | Evaluable.EvalConstRef _ -> true
  | Evaluable.EvalProjectionRef _ -> true
  | Evaluable.EvalVarRef v -> try ignore(Environ.lookup_named v env); true with Not_found -> false

let dbg_intro dbg = tclLOG dbg (fun _ _ -> str "intro") intro
let dbg_assumption dbg = tclLOG dbg (fun _ _ -> str "assumption") assumption

let intro_register dbg kont db =
  Proofview.tclTHEN (dbg_intro dbg) @@
    Proofview.Goal.enter begin fun gl ->
      let extend_local_db decl db =
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in
        push_resolve_hyp env sigma (Context.Named.Declaration.get_id decl) db
      in
      Tacticals.onLastDecl (fun decl -> kont (extend_local_db decl db))
    end

let rec trivial_fail_db dbg db_list local_db =
  Proofview.tclINDEPENDENT @@
    Tacticals.tclORELSE0 (dbg_assumption dbg) @@
    Tacticals.tclORELSE0 (intro_register dbg (trivial_fail_db dbg db_list) local_db) @@
    Proofview.Goal.enter begin fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      let concl = Proofview.Goal.concl gl in
      let secvars = compute_secvars gl in
      let hdc = try Some (decompose_app_bound sigma concl) with Bound -> None in
      let hintmap = hintmap_of env sigma secvars hdc concl in
      let hinttac = tac_of_hint dbg db_list local_db concl in
      (local_db::db_list)
      |> List.map_append (fun db -> try hintmap db with Not_found -> [])
      |> List.filter_map begin fun h ->
           if Int.equal (FullHint.priority h) 0 then
             Some (Tacticals.tclCOMPLETE (hinttac h))
           else None
         end
      |> Tacticals.tclFIRST
    end

and tac_of_hint dbg db_list local_db concl =
  let tactic = function
    | Res_pf h -> unify_resolve_nodelta h
    | ERes_pf _ -> Proofview.Goal.enter (fun gl ->
        let info = Exninfo.reify () in
        Tacticals.tclZEROMSG ~info (str "eres_pf"))
    | Give_exact h  -> exact h
    | Res_pf_THEN_trivial_fail h ->
      Tacticals.tclTHEN
        (unify_resolve_nodelta h)
        (* With "(debug) trivial", we shouldn't end here, and
           with "debug auto" we don't display the details of inner trivial *)
        (trivial_fail_db (no_dbg dbg) db_list local_db)
    | Unfold_nth c ->
      Proofview.Goal.enter begin fun gl ->
       if exists_evaluable_reference (Proofview.Goal.env gl) c then
         Tacticals.tclPROGRESS (reduce (Unfold [AllOccurrences,c]) Locusops.onConcl)
       else
         let info = Exninfo.reify () in
         Tacticals.tclFAIL ~info (str"Unbound reference")
       end
    | Extern (p, tacast) ->
      conclPattern concl p tacast
  in
  let pr_hint h env sigma =
    let origin = match FullHint.database h with
    | None -> mt ()
    | Some n -> str " (in " ++ str n ++ str ")"
    in
    FullHint.print env sigma h ++ origin
  in
  fun h -> tclLOG dbg (pr_hint h) (FullHint.run h tactic)

(** The use of the "core" database can be de-activated by passing
    "nocore" amongst the databases. *)

let gen_trivial ?(debug=Off) lems dbnames =
  Hints.wrap_hint_warning @@
    Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let db_list =
      match dbnames with
      | Some dbnames -> make_db_list dbnames
      | None -> current_pure_db ()
    in
    let d = mk_trivial_dbg debug in
    let local_db = make_local_hint_db env sigma false lems in
    tclTRY_dbg d (trivial_fail_db d db_list local_db)
  end

(**************************************************************************)
(*                       The classical Auto tactic                        *)
(**************************************************************************)

exception SearchBound

(* n is the max depth of search *)
(* local_db contains the local Hypotheses *)

let search d n db_list lems =
  let make_local_db gl =
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    make_local_hint_db env sigma false lems
  in
  let rec search d n local_db =
    if Int.equal n 0 then
      let info = Exninfo.reify () in
      Proofview.tclZERO ~info SearchBound
    else
      Tacticals.tclORELSE0 (dbg_assumption d) @@
      Tacticals.tclORELSE0 (intro_register d (search d n) local_db) @@
      Proofview.Goal.enter begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in
        let concl = Proofview.Goal.concl gl in
        let hyps = Proofview.Goal.hyps gl in
        let d' = incr_dbg d in
        let secvars = compute_secvars gl in
        let hdc = try Some (decompose_app_bound sigma concl) with Bound -> None in
        let hintmap = hintmap_of env sigma secvars hdc concl in
        let hinttac = tac_of_hint d db_list local_db concl in
        (local_db::db_list)
        |> List.map_append (fun db -> try hintmap db with Not_found -> [])
        |> List.map begin fun h ->
             Proofview.tclTHEN (hinttac h) @@
               Proofview.Goal.enter begin fun gl ->
                 let hyps' = Proofview.Goal.hyps gl in
                 let local_db' =
                   (* update local_db if local hypotheses have changed *)
                   if hyps' == hyps then local_db else make_local_db gl
                 in
                 search d' (n-1) local_db'
               end
           end
        |> Tacticals.tclFIRST
      end
  in
  Proofview.Goal.enter begin fun gl ->
    search d n (make_local_db gl)
  end

let default_search_depth = 5

let gen_auto ?(debug=Off) n lems dbnames =
  Hints.wrap_hint_warning @@
    Proofview.Goal.enter begin fun gl ->
    let n = match n with None -> default_search_depth | Some n -> n in
    let db_list =
      match dbnames with
      | Some dbnames -> make_db_list dbnames
      | None -> current_pure_db ()
    in
    let d = mk_auto_dbg debug in
    tclTRY_dbg d (search d n db_list lems)
  end

let auto ?(debug=Off) n lems dbnames = gen_auto ~debug (Some n) lems (Some dbnames)

let default_auto = auto default_search_depth [] []
