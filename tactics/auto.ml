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
open Util
open Names
open Termops
open Environ
open Genredexpr
open Tactics
open Locus
open Proofview.Notations
open Hints

(**************************************************************************)
(*                           Automatic tactics                            *)
(**************************************************************************)

(**************************************************************************)
(*          tactics with a trace mechanism for automatic search           *)
(**************************************************************************)

let priority l = List.filter (fun hint -> Int.equal (FullHint.priority hint) 0) l

let compute_secvars gl =
  let hyps = Proofview.Goal.hyps gl in
  secvars_of_hyps hyps

(* tell auto not to reuse already instantiated metas in unification (for
   compatibility, since otherwise, apply succeeds oftener) *)

open Unification

let auto_core_unif_flags_of st1 st2 = {
  modulo_conv_on_closed_terms = Some st1;
  use_metas_eagerly_in_conv_on_closed_terms = false;
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
    Proofview.Unsafe.tclEVARS sigma <*> exact_check c
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
     let sigma = Tacmach.project gl in
     constr_bindings env sigma >>= fun constr_bindings ->
     Proofview.tclProofInfo [@ocaml.warning "-3"] >>= fun (_name, poly) ->
     let open Genarg in
     let open Geninterp in
     let inj c = match val_tag (topwit Stdarg.wit_constr) with
     | Val.Base tag -> Val.Dyn (tag, c)
     | _ -> assert false
     in
     let fold id c accu = Id.Map.add id (inj c) accu in
     let lfun = Id.Map.fold fold constr_bindings Id.Map.empty in
     let ist = { lfun
               ; poly
               ; extra = TacStore.empty } in
     match tac with
     | GenArg (Glbwit wit, tac) ->
      Ftactic.run (Geninterp.interp wit ist tac) (fun _ -> Proofview.tclUNIT ())
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
    { optdepr  = false;
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
  | Tacred.EvalConstRef _ -> true
  | Tacred.EvalVarRef v -> try ignore(lookup_named v env); true with Not_found -> false

let dbg_intro dbg = tclLOG dbg (fun _ _ -> str "intro") intro
let dbg_assumption dbg = tclLOG dbg (fun _ _ -> str "assumption") assumption

let rec trivial_fail_db dbg db_list local_db =
  let intro_tac =
    Tacticals.tclTHEN (dbg_intro dbg)
      ( Proofview.Goal.enter begin fun gl ->
          let sigma = Tacmach.project gl in
          let env = Proofview.Goal.env gl in
          let decl = Tacmach.pf_last_hyp gl in
          let hyp = Context.Named.Declaration.get_id decl in
          let local_db = push_resolve_hyp env sigma hyp local_db in
          trivial_fail_db dbg db_list local_db
      end)
  in
  Proofview.Goal.enter begin fun gl ->
    let concl = Tacmach.pf_concl gl in
    let sigma = Tacmach.project gl in
    let env = Proofview.Goal.env gl in
    let secvars = compute_secvars gl in
    Tacticals.tclFIRST
      ((dbg_assumption dbg)::intro_tac::
          (List.map Tacticals.tclCOMPLETE
             (trivial_resolve env sigma dbg db_list local_db secvars concl)))
  end

and my_find_search env sigma db_list local_db secvars hdc concl =
  List.map_append (hintmap_of env sigma secvars hdc concl) (local_db::db_list)

and tac_of_hint dbg db_list local_db concl h =
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
       if exists_evaluable_reference (Tacmach.pf_env gl) c then
         Tacticals.tclPROGRESS (reduce (Unfold [AllOccurrences,c]) Locusops.onConcl)
       else
         let info = Exninfo.reify () in
         Tacticals.tclFAIL ~info (str"Unbound reference")
       end
    | Extern (p, tacast) ->
      conclPattern concl p tacast
  in
  let pr_hint env sigma =
    let origin = match FullHint.database h with
    | None -> mt ()
    | Some n -> str " (in " ++ str n ++ str ")"
    in
    FullHint.print env sigma h ++ origin
  in
  tclLOG dbg pr_hint (FullHint.run h tactic)

and trivial_resolve env sigma dbg db_list local_db secvars cl =
  try
    let head =
      try let hdconstr = decompose_app_bound sigma cl in
            Some hdconstr
      with Bound -> None
    in
      List.map (tac_of_hint dbg db_list local_db cl)
        (priority
            (my_find_search env sigma db_list local_db secvars head cl))
  with Not_found -> []

(** The use of the "core" database can be de-activated by passing
    "nocore" amongst the databases. *)

let trivial ?(debug=Off) lems dbnames =
  Hints.wrap_hint_warning @@
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.project gl in
  let db_list = make_db_list dbnames in
  let d = mk_trivial_dbg debug in
  let hints = make_local_hint_db env sigma false lems in
  tclTRY_dbg d
    (trivial_fail_db d db_list hints)
  end

let full_trivial ?(debug=Off) lems =
  Hints.wrap_hint_warning @@
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.project gl in
  let db_list = current_pure_db () in
  let d = mk_trivial_dbg debug in
  let hints = make_local_hint_db env sigma false lems in
  tclTRY_dbg d
    (trivial_fail_db d db_list hints)
  end

let gen_trivial ?(debug=Off) lems = function
  | None -> full_trivial ~debug lems
  | Some l -> trivial ~debug lems l

let h_trivial ?(debug=Off) lems l = gen_trivial ~debug lems l

(**************************************************************************)
(*                       The classical Auto tactic                        *)
(**************************************************************************)

let possible_resolve env sigma dbg db_list local_db secvars cl =
  try
    let head =
      try let hdconstr = decompose_app_bound sigma cl in
            Some hdconstr
      with Bound -> None
    in
      List.map (tac_of_hint dbg db_list local_db cl)
        (my_find_search env sigma db_list local_db secvars head cl)
  with Not_found -> []

(* Introduce an hypothesis, then call the continuation tactic [kont]
   with the hint db extended with the so-obtained hypothesis *)

let intro_register dbg kont db =
  Tacticals.tclTHEN (dbg_intro dbg)
    (Proofview.Goal.enter begin fun gl ->
      let extend_local_db decl db =
        let env = Tacmach.pf_env gl in
        let sigma = Tacmach.project gl in
        push_resolve_hyp env sigma (Context.Named.Declaration.get_id decl) db
      in
      Tacticals.onLastDecl (fun decl -> kont (extend_local_db decl db))
    end)

(* n is the max depth of search *)
(* local_db contains the local Hypotheses *)

let search d n db_list local_db =
  let rec search d n local_db =
    (* spiwack: the test of [n] to 0 must be done independently in
       each goal. Hence the [tclEXTEND] *)
    Proofview.tclEXTEND [] begin
      if Int.equal n 0 then
        let info = Exninfo.reify () in
        Tacticals.tclZEROMSG ~info (str"BOUND 2")
      else
        Tacticals.tclORELSE0 (dbg_assumption d)
          (Tacticals.tclORELSE0 (intro_register d (search d n) local_db)
             ( Proofview.Goal.enter begin fun gl ->
               let concl = Tacmach.pf_concl gl in
               let sigma = Tacmach.project gl in
               let env = Proofview.Goal.env gl in
               let secvars = compute_secvars gl in
               let d' = incr_dbg d in
               Tacticals.tclFIRST
                 (List.map
                    (fun ntac -> Tacticals.tclTHEN ntac (search d' (n-1) local_db))
                    (possible_resolve env sigma d db_list local_db secvars concl))
             end))
    end []
  in
  search d n local_db

let default_search_depth = ref 5

let delta_auto debug n lems dbnames =
  Hints.wrap_hint_warning @@
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.project gl in
  let db_list = make_db_list dbnames in
  let d = mk_auto_dbg debug in
  let hints = make_local_hint_db env sigma false lems in
  tclTRY_dbg d
    (search d n db_list hints)
  end

let auto ?(debug=Off) n = delta_auto debug n

let default_auto = auto !default_search_depth [] []

let delta_full_auto ?(debug=Off) n lems =
  Hints.wrap_hint_warning @@
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.project gl in
  let db_list = current_pure_db () in
  let d = mk_auto_dbg debug in
  let hints = make_local_hint_db env sigma false lems in
  tclTRY_dbg d
    (search d n db_list hints)
  end

let full_auto ?(debug=Off) n = delta_full_auto ~debug n

let default_full_auto = full_auto !default_search_depth []

let gen_auto ?(debug=Off) n lems dbnames =
  let n = match n with None -> !default_search_depth | Some n -> n in
  match dbnames with
  | None -> full_auto ~debug n lems
  | Some l -> auto ~debug n lems l

let h_auto ?(debug=Off) n lems l = gen_auto ~debug n lems l
