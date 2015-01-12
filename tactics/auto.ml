(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*
*)
open Pp
open Util
open Errors
open Names
open Vars
open Termops
open Environ
open Tacmach
open Genredexpr
open Tactics
open Tacticals
open Clenv
open Tacexpr
open Locus
open Proofview.Notations
open Hints

(**************************************************************************)
(*                           Automatic tactics                            *)
(**************************************************************************)

(**************************************************************************)
(*          tactics with a trace mechanism for automatic search           *)
(**************************************************************************)

let priority l = List.filter (fun (_, hint) -> Int.equal hint.pri 0) l

(* tell auto not to reuse already instantiated metas in unification (for
   compatibility, since otherwise, apply succeeds oftener) *)

open Unification

let auto_core_unif_flags_of st1 st2 useeager = {
  modulo_conv_on_closed_terms = Some st1;
  use_metas_eagerly_in_conv_on_closed_terms = useeager;
  use_evars_eagerly_in_conv_on_closed_terms = false;
  modulo_delta = st2;
  modulo_delta_types = full_transparent_state;
  check_applied_meta_types = false;
  use_pattern_unification = false;
  use_meta_bound_pattern_unification = true;
  frozen_evars = Evar.Set.empty;
  restrict_conv_on_strict_subterms = false; (* Compat *)
  modulo_betaiota = false;
  modulo_eta = true;
}

let auto_unif_flags_of st1 st2 useeager =
  let flags = auto_core_unif_flags_of st1 st2 useeager in {
  core_unify_flags = flags;
  merge_unify_flags = flags;
  subterm_unify_flags = { flags with modulo_delta = empty_transparent_state };
  allow_K_in_toplevel_higher_order_unification = false;
  resolve_evars = true
}

let auto_unif_flags =
  auto_unif_flags_of full_transparent_state empty_transparent_state false

let auto_flags_of_state st =
  auto_unif_flags_of full_transparent_state st false

(* Try unification with the precompiled clause, then use registered Apply *)

let unify_resolve_nodelta poly (c,clenv) =
  Proofview.Goal.nf_enter begin fun gl ->
  let clenv' = if poly then fst (Clenv.refresh_undefined_univs clenv) else clenv in
  let clenv' = Tacmach.New.of_old connect_clenv gl clenv' in
  let clenv'' = Tacmach.New.of_old (fun gl -> clenv_unique_resolver ~flags:auto_unif_flags clenv' gl) gl in
  Clenvtac.clenv_refine false clenv''
  end

let unify_resolve poly flags (c,clenv) =
  Proofview.Goal.nf_enter begin fun gl ->
  let clenv' = if poly then fst (Clenv.refresh_undefined_univs clenv) else clenv in
  let clenv' = Tacmach.New.of_old connect_clenv gl clenv' in
  let clenv'' = Tacmach.New.of_old (fun gl -> clenv_unique_resolver ~flags clenv' gl) gl in
  Clenvtac.clenv_refine false clenv''
  end

let unify_resolve_gen poly = function
  | None -> unify_resolve_nodelta poly
  | Some flags -> unify_resolve poly flags

let exact poly (c,clenv) =
  let ctx, c' = 
    if poly then
      let evd', subst = Evd.refresh_undefined_universes clenv.evd in
      let ctx = Evd.evar_universe_context evd' in
	ctx, subst_univs_level_constr subst c 
    else 
      let ctx = Evd.evar_universe_context clenv.evd in
	ctx, c
  in
  Proofview.Goal.enter begin fun gl ->
    let sigma = Evd.merge_universe_context (Proofview.Goal.sigma gl) ctx in
    Tacticals.New.tclTHEN (Proofview.Unsafe.tclEVARS sigma) (exact_check c')
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

let (forward_interp_tactic, extern_interp) = Hook.make ()

let conclPattern concl pat tac =
  let constr_bindings env sigma =
    match pat with
    | None -> Proofview.tclUNIT Id.Map.empty
    | Some pat ->
	try
	  Proofview.tclUNIT (Constr_matching.matches env sigma pat concl)
	with Constr_matching.PatternMatchingFailure ->
          Proofview.tclZERO (UserError ("conclPattern",str"conclPattern"))
  in
   Proofview.Goal.enter (fun gl ->
     let env = Proofview.Goal.env gl in
     let sigma = Proofview.Goal.sigma gl in
       constr_bindings env sigma >>= fun constr_bindings ->
     Hook.get forward_interp_tactic constr_bindings tac)

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
  let _ = Goptions.declare_bool_option
    { Goptions.optsync  = true;
      Goptions.optdepr  = false;
      Goptions.optname  = String.concat " " ls;
      Goptions.optkey   = ls;
      Goptions.optread  = (fun () -> !refe);
      Goptions.optwrite = (:=) refe }
  in ()

let _ =
  add_option ["Debug";"Trivial"] global_debug_trivial;
  add_option ["Debug";"Auto"] global_debug_auto;
  add_option ["Info";"Trivial"] global_info_trivial;
  add_option ["Info";"Auto"] global_info_auto

let no_dbg () = (Off,0,ref [])

let mk_trivial_dbg debug =
  let d =
    if debug == Debug || !global_debug_trivial then Debug
    else if debug == Info || !global_info_trivial then Info
    else Off
  in (d,0,ref [])

(** Note : we start the debug depth of auto at 1 to distinguish it
   for trivial (whose depth is 0). *)

let mk_auto_dbg debug =
  let d =
    if debug == Debug || !global_debug_auto then Debug
    else if debug == Info || !global_info_auto then Info
    else Off
  in (d,1,ref [])

let incr_dbg = function (dbg,depth,trace) -> (dbg,depth+1,trace)

(** A tracing tactic for debug/info trivial/auto *)

let tclLOG (dbg,depth,trace) pp tac =
  match dbg with
    | Off -> tac
    | Debug ->
       (* For "debug (trivial/auto)", we directly output messages *)
      let s = String.make depth '*' in
      Proofview.V82.tactic begin fun gl ->
	try
	  let out = Proofview.V82.of_tactic tac gl in
	  msg_debug (str s ++ spc () ++ pp () ++ str ". (*success*)");
	  out
	with reraise ->
          let reraise = Errors.push reraise in
	  msg_debug (str s ++ spc () ++ pp () ++ str ". (*fail*)");
	  iraise reraise
      end
    | Info ->
      (* For "info (trivial/auto)", we store a log trace *)
      Proofview.V82.tactic begin fun gl ->
	try
	  let out = Proofview.V82.of_tactic tac gl in
	  trace := (depth, Some pp) :: !trace;
	  out
	with reraise ->
          let reraise = Errors.push reraise in
	  trace := (depth, None) :: !trace;
	  iraise reraise
      end

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

let pr_info_atom (d,pp) =
  str (String.make d ' ') ++ pp () ++ str "."

let pr_info_trace = function
  | (Info,_,{contents=(d,Some pp)::l}) ->
      prlist_with_sep fnl pr_info_atom (cleanup_info_trace d [(d,pp)] l)
  | _ -> mt ()

let pr_info_nop = function
  | (Info,_,_) -> str "idtac."
  | _ -> mt ()

let pr_dbg_header = function
  | (Off,_,_) -> mt ()
  | (Debug,0,_) -> str "(* debug trivial : *)"
  | (Debug,_,_) -> str "(* debug auto : *)"
  | (Info,0,_) -> str "(* info trivial : *)"
  | (Info,_,_) -> str "(* info auto : *)"

let tclTRY_dbg d tac =
  let (level, _, _) = d in
  let delay f = Proofview.tclUNIT () >>= fun () -> f () in
  let tac = match level with
  | Off -> tac
  | Debug | Info -> delay (fun () -> msg_debug (pr_dbg_header d ++ fnl () ++ pr_info_trace d); tac)
  in
  let after = match level with
  | Info -> delay (fun () -> msg_debug (pr_info_nop d); Proofview.tclUNIT ())
  | Off | Debug -> Proofview.tclUNIT ()
  in
  Tacticals.New.tclORELSE0 tac after

(**************************************************************************)
(*                           The Trivial tactic                           *)
(**************************************************************************)

(* local_db is a Hint database containing the hypotheses of current goal *)
(* Papageno : cette fonction a été pas mal simplifiée depuis que la base
  de Hint impérative a été remplacée par plusieurs bases fonctionnelles *)

let auto_unif_flags =
  auto_unif_flags_of full_transparent_state empty_transparent_state false

let flags_of_state st =
  auto_unif_flags_of st st false

let auto_flags_of_state st =
  auto_unif_flags_of full_transparent_state st false

let hintmap_of hdc concl =
  match hdc with
  | None -> Hint_db.map_none
  | Some hdc ->
      if occur_existential concl then Hint_db.map_existential hdc concl
      else Hint_db.map_auto hdc concl

let exists_evaluable_reference env = function
  | EvalConstRef _ -> true
  | EvalVarRef v -> try ignore(lookup_named v env); true with Not_found -> false

let dbg_intro dbg = tclLOG dbg (fun () -> str "intro") intro
let dbg_assumption dbg = tclLOG dbg (fun () -> str "assumption") assumption

let rec trivial_fail_db dbg mod_delta db_list local_db =
  let intro_tac =
    Tacticals.New.tclTHEN (dbg_intro dbg)
      ( Proofview.Goal.enter begin fun gl ->
          let sigma = Proofview.Goal.sigma gl in
          let env = Proofview.Goal.env gl in
          let nf c = Evarutil.nf_evar sigma c in
          let decl = Tacmach.New.pf_last_hyp (Proofview.Goal.assume gl) in
          let hyp = Context.map_named_declaration nf decl in
	  let hintl = make_resolve_hyp env sigma hyp
	  in trivial_fail_db dbg mod_delta db_list (Hint_db.add_list hintl local_db)
      end)
  in
  Proofview.Goal.enter begin fun gl ->
    let concl = Tacmach.New.pf_nf_concl gl in
    Tacticals.New.tclFIRST
      ((dbg_assumption dbg)::intro_tac::
          (List.map Tacticals.New.tclCOMPLETE
             (trivial_resolve dbg mod_delta db_list local_db concl)))
  end

and my_find_search_nodelta db_list local_db hdc concl =
  List.map (fun hint -> (None,hint))
    (List.map_append (hintmap_of hdc concl) (local_db::db_list))

and my_find_search mod_delta =
  if mod_delta then my_find_search_delta
  else my_find_search_nodelta

and my_find_search_delta db_list local_db hdc concl =
  let f = hintmap_of hdc concl in
    if occur_existential concl then
      List.map_append
	(fun db ->
	  if Hint_db.use_dn db then
	    let flags = flags_of_state (Hint_db.transparent_state db) in
	      List.map (fun x -> (Some flags,x)) (f db)
	  else
	    let flags = auto_flags_of_state (Hint_db.transparent_state db) in
	      List.map (fun x -> (Some flags,x)) (f db))
	(local_db::db_list)
    else
      List.map_append (fun db ->
	if Hint_db.use_dn db then
	  let flags = flags_of_state (Hint_db.transparent_state db) in
	    List.map (fun x -> (Some flags, x)) (f db)
	else
	  let (ids, csts as st) = Hint_db.transparent_state db in
	  let flags, l =
	    let l =
	      match hdc with None -> Hint_db.map_none db
	      | Some hdc ->
		  if (Id.Pred.is_empty ids && Cpred.is_empty csts)
		  then Hint_db.map_auto hdc concl db
		  else Hint_db.map_existential hdc concl db
	    in auto_flags_of_state st, l
	  in List.map (fun x -> (Some flags,x)) l)
      	(local_db::db_list)

and tac_of_hint dbg db_list local_db concl (flags, ({pat=p; code=t;poly=poly})) =
  let tactic = 
    match t with
    | Res_pf (c,cl) -> unify_resolve_gen poly flags (c,cl)
    | ERes_pf _ -> Proofview.V82.tactic (fun gl -> error "eres_pf")
    | Give_exact (c, cl)  -> exact poly (c, cl)
    | Res_pf_THEN_trivial_fail (c,cl) ->
      Tacticals.New.tclTHEN
        (unify_resolve_gen poly flags (c,cl))
	(* With "(debug) trivial", we shouldn't end here, and
	   with "debug auto" we don't display the details of inner trivial *)
        (trivial_fail_db (no_dbg ()) (not (Option.is_empty flags)) db_list local_db)
    | Unfold_nth c ->
      Proofview.V82.tactic (fun gl ->
       if exists_evaluable_reference (pf_env gl) c then
	 tclPROGRESS (reduce (Unfold [AllOccurrences,c]) Locusops.onConcl) gl
       else tclFAIL 0 (str"Unbound reference") gl)
    | Extern tacast -> 
      conclPattern concl p tacast
  in
  tclLOG dbg (fun () -> pr_autotactic t) tactic

and trivial_resolve dbg mod_delta db_list local_db cl =
  try
    let head =
      try let hdconstr = decompose_app_bound cl in
	    Some hdconstr
      with Bound -> None
    in
      List.map (tac_of_hint dbg db_list local_db cl)
	(priority
	    (my_find_search mod_delta db_list local_db head cl))
  with Not_found -> []

(** The use of the "core" database can be de-activated by passing
    "nocore" amongst the databases. *)

let trivial ?(debug=Off) lems dbnames =
  Proofview.Goal.nf_enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let db_list = make_db_list dbnames in
  let d = mk_trivial_dbg debug in
  let hints = make_local_hint_db env sigma false lems in
  tclTRY_dbg d
    (trivial_fail_db d false db_list hints)
  end

let full_trivial ?(debug=Off) lems =
  Proofview.Goal.nf_enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let db_list = current_pure_db () in
  let d = mk_trivial_dbg debug in
  let hints = make_local_hint_db env sigma false lems in
  tclTRY_dbg d
    (trivial_fail_db d false db_list hints)
  end

let gen_trivial ?(debug=Off) lems = function
  | None -> full_trivial ~debug lems
  | Some l -> trivial ~debug lems l

let h_trivial ?(debug=Off) lems l = gen_trivial ~debug lems l

(**************************************************************************)
(*                       The classical Auto tactic                        *)
(**************************************************************************)

let possible_resolve dbg mod_delta db_list local_db cl =
  try
    let head =
      try let hdconstr = decompose_app_bound cl in
	    Some hdconstr
      with Bound -> None
    in
      List.map (tac_of_hint dbg db_list local_db cl)
	(my_find_search mod_delta db_list local_db head cl)
  with Not_found -> []

let extend_local_db decl db gl =
  Hint_db.add_list (make_resolve_hyp (Tacmach.New.pf_env gl) (Proofview.Goal.sigma gl) decl) db

(* Introduce an hypothesis, then call the continuation tactic [kont]
   with the hint db extended with the so-obtained hypothesis *)

let intro_register dbg kont db =
  Tacticals.New.tclTHEN (dbg_intro dbg)
    (Proofview.Goal.enter begin fun gl ->
      let extend_local_db decl db = extend_local_db decl db gl in
      Tacticals.New.onLastDecl (fun decl -> kont (extend_local_db decl db))
    end)

(* n is the max depth of search *)
(* local_db contains the local Hypotheses *)

let search d n mod_delta db_list local_db =
  let rec search d n local_db =
    (* spiwack: the test of [n] to 0 must be done independently in
       each goal. Hence the [tclEXTEND] *)
    Proofview.tclEXTEND [] begin
      if Int.equal n 0 then Proofview.tclZERO (Errors.UserError ("",str"BOUND 2")) else
        Tacticals.New.tclORELSE0 (dbg_assumption d)
	  (Tacticals.New.tclORELSE0 (intro_register d (search d n) local_db)
	     ( Proofview.Goal.enter begin fun gl ->
               let concl = Tacmach.New.pf_nf_concl gl in
	       let d' = incr_dbg d in
	       Tacticals.New.tclFIRST
	         (List.map
		    (fun ntac -> Tacticals.New.tclTHEN ntac (search d' (n-1) local_db))
		    (possible_resolve d mod_delta db_list local_db concl))
             end))
    end []
  in
  search d n local_db

let default_search_depth = ref 5

let delta_auto debug mod_delta n lems dbnames =
  Proofview.Goal.nf_enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let db_list = make_db_list dbnames in
  let d = mk_auto_dbg debug in
  let hints = make_local_hint_db env sigma false lems in
  tclTRY_dbg d
    (search d n mod_delta db_list hints)
  end

let delta_auto = 
  if Flags.profile then
    let key = Profile.declare_profile "delta_auto" in
      Profile.profile5 key delta_auto
  else delta_auto

let auto ?(debug=Off) n = delta_auto debug false n

let new_auto ?(debug=Off) n = delta_auto debug true n

let default_auto = auto !default_search_depth [] []

let delta_full_auto ?(debug=Off) mod_delta n lems =
  Proofview.Goal.nf_enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let db_list = current_pure_db () in
  let d = mk_auto_dbg debug in
  let hints = make_local_hint_db env sigma false lems in
  tclTRY_dbg d
    (search d n mod_delta db_list hints)
  end

let full_auto ?(debug=Off) n = delta_full_auto ~debug false n
let new_full_auto ?(debug=Off) n = delta_full_auto ~debug true n

let default_full_auto = full_auto !default_search_depth []

let gen_auto ?(debug=Off) n lems dbnames =
  let n = match n with None -> !default_search_depth | Some n -> n in
  match dbnames with
  | None -> full_auto ~debug n lems
  | Some l -> auto ~debug n lems l

let h_auto ?(debug=Off) n lems l = gen_auto ~debug n lems l
