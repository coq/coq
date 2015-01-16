(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Names
open Term
open Termops
open Reduction
open Proof_type
open Tacticals
open Tacmach
open Tactics
open Patternops
open Clenv
open Typeclasses
open Globnames
open Evd
open Locus
open Misctypes
open Proofview.Notations
open Hints

(** Hint database named "typeclass_instances", now created directly in Auto *)

let typeclasses_debug = ref false
let typeclasses_depth = ref None

let typeclasses_modulo_eta = ref false
let set_typeclasses_modulo_eta d = (:=) typeclasses_modulo_eta d
let get_typeclasses_modulo_eta () = !typeclasses_modulo_eta

let typeclasses_dependency_order = ref false
let set_typeclasses_dependency_order d = (:=) typeclasses_dependency_order d
let get_typeclasses_dependency_order () = !typeclasses_dependency_order

open Goptions

let set_typeclasses_modulo_eta =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "do typeclass search modulo eta conversion";
      optkey   = ["Typeclasses";"Modulo";"Eta"];
      optread  = get_typeclasses_modulo_eta;
      optwrite = set_typeclasses_modulo_eta; }

let set_typeclasses_dependency_order =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "during typeclass resolution, solve instances according to their dependency order";
      optkey   = ["Typeclasses";"Dependency";"Order"];
      optread  = get_typeclasses_dependency_order;
      optwrite = set_typeclasses_dependency_order; }

(** We transform the evars that are concerned by this resolution
    (according to predicate p) into goals.
    Invariant: function p only manipulates and returns undefined evars *)

let top_sort evm undefs =
  let l' = ref [] in
  let tosee = ref undefs in
  let rec visit ev evi = 
    let evs = Evarutil.undefined_evars_of_evar_info evm evi in
      Evar.Set.iter (fun ev -> 
	if Evar.Map.mem ev !tosee then 
	  visit ev (Evar.Map.find ev !tosee)) evs;
      tosee := Evar.Map.remove ev !tosee;
      l' := ev :: !l';
  in
    while not (Evar.Map.is_empty !tosee) do
      let ev, evi = Evar.Map.min_binding !tosee in
	visit ev evi
    done;
    List.rev !l'

let evars_to_goals p evm =
  let goals = ref Evar.Map.empty in
  let map ev evi =
    let evi, goal = p evm ev evi in
    let () = if goal then goals := Evar.Map.add ev evi !goals in
    evi
  in
  let evm = Evd.raw_map_undefined map evm in
  if Evar.Map.is_empty !goals then None
  else Some (!goals, evm)

(** Typeclasses instance search tactic / eauto *)

open Auto

open Unification

let auto_core_unif_flags st freeze = {
  modulo_conv_on_closed_terms = Some st;
  use_metas_eagerly_in_conv_on_closed_terms = true;
  use_evars_eagerly_in_conv_on_closed_terms = false;
  modulo_delta = st;
  modulo_delta_types = st;
  check_applied_meta_types = false;
  use_pattern_unification = true;
  use_meta_bound_pattern_unification = true;
  frozen_evars = freeze;
  restrict_conv_on_strict_subterms = false; (* ? *)
  modulo_betaiota = true;
  modulo_eta = !typeclasses_modulo_eta;
}

let auto_unif_flags freeze st = 
  let fl = auto_core_unif_flags st freeze in
  { core_unify_flags = fl;
    merge_unify_flags = fl;
    subterm_unify_flags = fl;
    allow_K_in_toplevel_higher_order_unification = false;
    resolve_evars = false
}

let rec eq_constr_mod_evars x y =
  match kind_of_term x, kind_of_term y with
  | Evar (e1, l1), Evar (e2, l2) when not (Evar.equal e1 e2) -> true
  | _, _ -> compare_constr eq_constr_mod_evars x y

let progress_evars t =
  Proofview.Goal.nf_enter begin fun gl ->
    let concl = Proofview.Goal.concl gl in
    let check =
      Proofview.Goal.nf_enter begin fun gl' ->
        let newconcl = Proofview.Goal.concl gl' in
        if eq_constr_mod_evars concl newconcl
        then Tacticals.New.tclFAIL 0 (str"No progress made (modulo evars)")
        else Proofview.tclUNIT ()
      end
    in t <*> check
  end


let e_give_exact flags poly (c,clenv) gl =
  let c, gl =
    if poly then
      let clenv', subst = Clenv.refresh_undefined_univs clenv in
      let clenv' = connect_clenv gl clenv' in
      let c = Vars.subst_univs_level_constr subst c in
	c, {gl with sigma = clenv'.evd}
    else c, gl
  in
  let t1 = pf_type_of gl c in
    tclTHEN (Proofview.V82.of_tactic (Clenvtac.unify ~flags t1)) (exact_no_check c) gl

let unify_e_resolve poly flags (c,clenv) gls =
  let clenv' = if poly then fst (Clenv.refresh_undefined_univs clenv) else clenv in
  let clenv' = connect_clenv gls clenv' in
  let clenv' = clenv_unique_resolver ~flags clenv' gls in
  Proofview.V82.of_tactic (Clenvtac.clenv_refine true ~with_classes:false clenv') gls

let unify_resolve poly flags (c,clenv) gls =
  let clenv' = if poly then fst (Clenv.refresh_undefined_univs clenv) else clenv in
  let clenv' = connect_clenv gls clenv' in
  let clenv' = clenv_unique_resolver ~flags clenv' gls in
  Proofview.V82.of_tactic 
    (Clenvtac.clenv_refine false ~with_classes:false clenv') gls

let clenv_of_prods poly nprods (c, clenv) gls =
  if poly || Int.equal nprods 0 then Some clenv
  else
    let ty = pf_type_of gls c in
    let diff = nb_prod ty - nprods in
      if Pervasives.(>=) diff 0 then
        (* Was Some clenv... *)
	Some (mk_clenv_from_n gls (Some diff) (c,ty))
      else None

let with_prods nprods poly (c, clenv) f gls =
  match clenv_of_prods poly nprods (c, clenv) gls with
  | None -> tclFAIL 0 (str"Not enough premisses") gls
  | Some clenv' -> f (c, clenv') gls

(** Hack to properly solve dependent evars that are typeclasses *)

let rec e_trivial_fail_db db_list local_db goal =
  let tacl =
    Eauto.registered_e_assumption ::
    (tclTHEN (Proofview.V82.of_tactic Tactics.intro)
       (function g'->
	  let d = pf_last_hyp g' in
	  let hintl = make_resolve_hyp (pf_env g') (project g') d in
          (e_trivial_fail_db db_list
	      (Hint_db.add_list hintl local_db) g'))) ::
    (List.map (fun (x,_,_,_,_) -> x) 
     (e_trivial_resolve db_list local_db (project goal) (pf_concl goal)))
  in
  tclFIRST (List.map tclCOMPLETE tacl) goal

and e_my_find_search db_list local_db hdc complete sigma concl =
  let prods, concl = decompose_prod_assum concl in
  let nprods = List.length prods in
  let freeze = 
    try
      let cl = Typeclasses.class_info (fst hdc) in
	if cl.cl_strict then
	  Evd.evars_of_term concl
	else Evar.Set.empty
    with _ -> Evar.Set.empty
  in
  let hintl =
    List.map_append
      (fun db ->
	let tacs = 
	  if Hint_db.use_dn db then (* Using dnet *)
	    Hint_db.map_eauto hdc concl db
	  else Hint_db.map_existential hdc concl db
	in
	let flags = auto_unif_flags freeze (Hint_db.transparent_state db) in
	  List.map (fun x -> (flags, x)) tacs)
      (local_db::db_list)
  in
  let tac_of_hint =
    fun (flags, {pri = b; pat = p; poly = poly; code = t; name = name}) ->
      let tac =
	match t with
	  | Res_pf (term,cl) -> with_prods nprods poly (term,cl) (unify_resolve poly flags)
	  | ERes_pf (term,cl) -> with_prods nprods poly (term,cl) (unify_e_resolve poly flags)
	  | Give_exact c -> e_give_exact flags poly c
	  | Res_pf_THEN_trivial_fail (term,cl) ->
              tclTHEN (with_prods nprods poly (term,cl) (unify_e_resolve poly flags))
	        (if complete then tclIDTAC else e_trivial_fail_db db_list local_db)
	  | Unfold_nth c -> tclWEAK_PROGRESS (unfold_in_concl [AllOccurrences,c])
	  | Extern tacast ->
	    Proofview.V82.of_tactic (conclPattern concl p tacast)
      in
      let tac = if complete then tclCOMPLETE tac else tac in
	match t with
	| Extern _ -> (tac,b,true, name, lazy (pr_autotactic t))
	| _ ->
(* 	  let tac gl = with_pattern (pf_env gl) (project gl) flags p concl tac gl in *)
	    (tac,b,false, name, lazy (pr_autotactic t))
  in List.map tac_of_hint hintl

and e_trivial_resolve db_list local_db sigma concl =
  try
    e_my_find_search db_list local_db
     (decompose_app_bound concl) true sigma concl
  with Bound | Not_found -> []

let e_possible_resolve db_list local_db sigma concl =
  try
    e_my_find_search db_list local_db
      (decompose_app_bound concl) false sigma concl
  with Bound | Not_found -> []

let catchable = function
  | Refiner.FailError _ -> true
  | e -> Logic.catchable_exception e

let pr_ev evs ev = Printer.pr_constr_env (Goal.V82.env evs ev) evs (Evarutil.nf_evar evs (Goal.V82.concl evs ev))

let pr_depth l = prlist_with_sep (fun () -> str ".") int (List.rev l)

type autoinfo = { hints : hint_db; is_evar: existential_key option;
		  only_classes: bool; unique : bool;
		  auto_depth: int list; auto_last_tac: std_ppcmds Lazy.t;
		  auto_path : global_reference option list;
		  auto_cut : hints_path }
type autogoal = goal * autoinfo
type 'ans fk = unit -> 'ans
type ('a,'ans) sk = 'a -> 'ans fk -> 'ans
type 'a tac = { skft : 'ans. ('a,'ans) sk -> 'ans fk -> autogoal sigma -> 'ans }

type auto_result = autogoal list sigma

type atac = auto_result tac

(* Some utility types to avoid the need of -rectypes *)

type 'a optionk =
  | Nonek
  | Somek of 'a * 'a optionk fk

type ('a,'b) optionk2 =
  | Nonek2
  | Somek2 of 'a * 'b * ('a,'b) optionk2 fk

let make_resolve_hyp env sigma st flags only_classes pri (id, _, cty) =
  let cty = Evarutil.nf_evar sigma cty in
  let rec iscl env ty =
    let ctx, ar = decompose_prod_assum ty in
      match kind_of_term (fst (decompose_app ar)) with
      | Const (c,_) -> is_class (ConstRef c)
      | Ind (i,_) -> is_class (IndRef i)
      | _ ->
	  let env' = Environ.push_rel_context ctx env in
	  let ty' = whd_betadeltaiota env' ar in
	       if not (Term.eq_constr ty' ar) then iscl env' ty'
	       else false
  in
  let is_class = iscl env cty in
  let keep = not only_classes || is_class in
    if keep then
      let c = mkVar id in
      let name = PathHints [VarRef id] in
      let hints =
	if is_class then
	  let hints = build_subclasses ~check:false env sigma (VarRef id) None in
	    (List.map_append
	       (fun (path,pri, c) -> make_resolves env sigma ~name:(PathHints path)
		  (true,false,Flags.is_verbose()) pri false
		 (IsConstr (c,Univ.ContextSet.empty)))
	       hints)
	else []
      in
        (hints @ List.map_filter
	 (fun f -> try Some (f (c, cty, Univ.ContextSet.empty)) 
	   with Failure _ | UserError _ -> None)
	 [make_exact_entry ~name env sigma pri false; 
	  make_apply_entry ~name env sigma flags pri false])
    else []

let pf_filtered_hyps gls =
  Goal.V82.hyps gls.Evd.sigma (sig_it gls)

let make_hints g st only_classes sign =
  let paths, hintlist =
    List.fold_left
    (fun (paths, hints) hyp ->
      let consider =
	try let (_, b, t) = Global.lookup_named (pi1 hyp) in
	      (* Section variable, reindex only if the type changed *)
	      not (Term.eq_constr t (pi3 hyp))
	with Not_found -> true
     in
      if consider then 
	let path, hint =
	  PathEmpty, pf_apply make_resolve_hyp g st (true,false,false) only_classes None hyp
	in
	  (PathOr (paths, path), hint @ hints)
      else (paths, hints))
    (PathEmpty, []) sign
  in Hint_db.add_list hintlist (Hint_db.empty st true)

let make_autogoal_hints =
  let cache = ref (true, Environ.empty_named_context_val, 
		   Hint_db.empty full_transparent_state true) 
  in
    fun only_classes ?(st=full_transparent_state) g ->
      let sign = pf_filtered_hyps g in
      let (onlyc, sign', cached_hints) = !cache in
	if onlyc == only_classes && 
	  (sign == sign' || Environ.eq_named_context_val sign sign') then
	  cached_hints
	else
	  let hints = make_hints g st only_classes (Environ.named_context_of_val sign) in
	    cache := (only_classes, sign, hints); hints

let lift_tactic tac (f : goal list sigma -> autoinfo -> autogoal list sigma) : 'a tac =
  { skft = fun sk fk {it = gl,hints; sigma=s;} ->
    let res = try Some (tac {it=gl; sigma=s;})
              with e when catchable e -> None in
      match res with
      | Some gls -> sk (f gls hints) fk
      | None -> fk () }

let intro_tac : atac =
  lift_tactic (Proofview.V82.of_tactic Tactics.intro)
    (fun {it = gls; sigma = s} info ->
      let gls' =
	List.map (fun g' ->
	  let env = Goal.V82.env s g' in
	  let context = Environ.named_context_of_val (Goal.V82.hyps s g') in
	  let hint = make_resolve_hyp env s (Hint_db.transparent_state info.hints)
	    (true,false,false) info.only_classes None (List.hd context) in
	  let ldb = Hint_db.add_list hint info.hints in
	    (g', { info with is_evar = None; hints = ldb; auto_last_tac = lazy (str"intro") })) gls
      in {it = gls'; sigma = s;})

let normevars_tac : atac =
  { skft = fun sk fk {it = (gl, info); sigma = s;} ->
    let gl', sigma' = Goal.V82.nf_evar s gl in
    let info' = { info with auto_last_tac = lazy (str"normevars") } in
      sk {it = [gl', info']; sigma = sigma';} fk }

let or_tac (x : 'a tac) (y : 'a tac) : 'a tac =
  { skft = fun sk fk gls -> x.skft sk (fun () -> y.skft sk fk gls) gls }

let is_Prop env sigma concl =
  let ty = Retyping.get_type_of env sigma concl in
  match kind_of_term ty with
  | Sort (Prop Null) -> true
  | _ -> false

let is_unique env concl = 
  try 
    let (cl,u), args = dest_class_app env concl in
      cl.cl_unique
  with _ -> false

let needs_backtrack env evd oev concl =
  if Option.is_empty oev || is_Prop env evd concl then
    occur_existential concl
  else true

let hints_tac hints =
  { skft = fun sk fk {it = gl,info; sigma = s;} ->
      let env = Goal.V82.env s gl in
      let concl = Goal.V82.concl s gl in
      let tacgl = {it = gl; sigma = s;} in
      let poss = e_possible_resolve hints info.hints s concl in
      let unique = is_unique env concl in
      let rec aux i foundone = function
      | (tac, _, b, name, pp) :: tl ->
	let derivs = path_derivate info.auto_cut name in
	let res =
          try
	    if path_matches derivs [] then None else Some (tac tacgl)
	  with e when catchable e -> None
	in
	  (match res with
	  | None -> aux i foundone tl
	  | Some {it = gls; sigma = s';} ->
	    if !typeclasses_debug then
	      msg_debug (pr_depth (i :: info.auto_depth) ++ str": " ++ Lazy.force pp
			 ++ str" on" ++ spc () ++ pr_ev s gl);
	    let sgls =
	      evars_to_goals
		(fun evm ev evi ->
		  if Typeclasses.is_resolvable evi && not (Evd.is_undefined s ev) &&
		    (not info.only_classes || Typeclasses.is_class_evar evm evi)
		  then Typeclasses.mark_unresolvable evi, true
		  else evi, false) s'
	    in
	    let newgls, s' =
	      let gls' = List.map (fun g -> (None, g)) gls in
		match sgls with
		| None -> gls', s'
		| Some (evgls, s') ->
		  if not !typeclasses_dependency_order then
		    (gls' @ List.map (fun (ev,_) -> (Some ev, ev)) (Evar.Map.bindings evgls), s')
		  else 
 		    (* Reorder with dependent subgoals. *)
		    let evm = List.fold_left 
		      (fun acc g -> Evar.Map.add g (Evd.find_undefined s' g) acc) evgls gls in
		    let gls = top_sort s' evm in
		      (List.map (fun ev -> Some ev, ev) gls, s')
	    in
	    let gls' = List.map_i
	      (fun j (evar, g) ->
		let info =
		  { info with auto_depth = j :: i :: info.auto_depth; auto_last_tac = pp;
		    is_evar = evar;
		    hints =
		      if b && not (Environ.eq_named_context_val (Goal.V82.hyps s' g) 
				     (Goal.V82.hyps s' gl))
		      then make_autogoal_hints info.only_classes
			~st:(Hint_db.transparent_state info.hints) {it = g; sigma = s';}
		      else info.hints;
		    auto_cut = derivs }
		in g, info) 1 newgls in
	    let glsv = {it = gls'; sigma = s';} in
	    let fk' =
	      (fun () ->
		let do_backtrack =
		  if unique then occur_existential concl
		  else if info.unique then true
		  else if List.is_empty gls' then 
		    needs_backtrack env s' info.is_evar concl
		  else true
		in
		  if !typeclasses_debug then
		    msg_debug 
		      ((if do_backtrack then str"Backtracking after "
			else str "Not backtracking after ")
		       ++ Lazy.force pp);
		  if do_backtrack then aux (succ i) true tl
		  else fk ())
	    in
	      sk glsv fk')
      | [] ->
	if not foundone && !typeclasses_debug then
	  msg_debug (pr_depth info.auto_depth ++ str": no match for " ++
		       Printer.pr_constr_env (Goal.V82.env s gl) s concl ++
		       spc () ++ str ", " ++ int (List.length poss) ++ str" possibilities");
	fk ()
      in aux 1 false poss }

let then_list (second : atac) (sk : (auto_result, 'a) sk) : (auto_result, 'a) sk =
  let rec aux s (acc : autogoal list list) fk = function
    | (gl,info) :: gls ->
	(match info.is_evar with
	 | Some ev when Evd.is_defined s ev -> aux s acc fk gls
	 | _ ->
	     second.skft
	       (fun {it=gls';sigma=s'} fk' -> 
		 let fk'' =
		   if not info.unique && List.is_empty gls' &&
		     not (needs_backtrack (Goal.V82.env s gl) s
			    info.is_evar (Goal.V82.concl s gl))
		   then fk
		   else fk'
		 in
		   aux s' (gls'::acc) fk'' gls)
	       fk {it = (gl,info); sigma = s; })
    | [] -> Somek2 (List.rev acc, s, fk)
  in fun {it = gls; sigma = s; } fk ->
    let rec aux' = function
      | Nonek2 -> fk ()
      | Somek2 (res, s', fk') ->
	  let goals' = List.concat res in
	    sk {it = goals'; sigma = s'; } (fun () -> aux' (fk' ()))
    in aux' (aux s [] (fun () -> Nonek2) gls)

let then_tac (first : atac) (second : atac) : atac =
  { skft = fun sk fk -> first.skft (then_list second sk) fk }

let run_tac (t : 'a tac) (gl : autogoal sigma) : auto_result option =
  t.skft (fun x _ -> Some x) (fun _ -> None) gl

type run_list_res = auto_result optionk

let run_list_tac (t : 'a tac) p goals (gl : autogoal list sigma) : run_list_res =
  (then_list t (fun x fk -> Somek (x, fk)))
    gl
    (fun _ -> Nonek)

let fail_tac : atac =
  { skft = fun sk fk _ -> fk () }

let rec fix (t : 'a tac) : 'a tac =
  then_tac t { skft = fun sk fk -> (fix t).skft sk fk }

let rec fix_limit limit (t : 'a tac) : 'a tac =
  if Int.equal limit 0 then fail_tac
  else then_tac t { skft = fun sk fk -> (fix_limit (pred limit) t).skft sk fk }

let make_autogoal ?(only_classes=true) ?(unique=false) ?(st=full_transparent_state) cut ev g =
  let hints = make_autogoal_hints only_classes ~st g in
    (g.it, { hints = hints ; is_evar = ev; unique = unique;
	     only_classes = only_classes; auto_depth = []; auto_last_tac = lazy (str"none");
	     auto_path = []; auto_cut = cut })


let cut_of_hints h =
  List.fold_left (fun cut db -> PathOr (Hint_db.cut db, cut)) PathEmpty h

let make_autogoals ?(only_classes=true) ?(unique=false) 
    ?(st=full_transparent_state) hints gs evm' =
  let cut = cut_of_hints hints in
  { it = List.map_i (fun i g ->
    let (gl, auto) = make_autogoal ~only_classes ~unique 
      ~st cut (Some g) {it = g; sigma = evm'; } in
      (gl, { auto with auto_depth = [i]})) 1 gs; sigma = evm'; }

let get_result r =
  match r with
  | Nonek -> None
  | Somek (gls, fk) -> Some (gls.sigma,fk)

let run_on_evars ?(only_classes=true) ?(unique=false) ?(st=full_transparent_state) p evm hints tac =
  match evars_to_goals p evm with
  | None -> None (* This happens only because there's no evar having p *)
  | Some (goals, evm') ->
    let goals = 
      if !typeclasses_dependency_order then
	top_sort evm' goals
      else List.map (fun (ev, _) -> ev) (Evar.Map.bindings goals)
    in
    let res = run_list_tac tac p goals 
      (make_autogoals ~only_classes ~unique ~st hints goals evm') in
      match get_result res with
      | None -> raise Not_found
      | Some (evm', fk) -> 
	Some (evars_reset_evd ~with_conv_pbs:true ~with_univs:false evm' evm, fk)

let eauto_tac hints =
  then_tac normevars_tac (or_tac (hints_tac hints) intro_tac)

let eauto_tac ?limit hints =
  match limit with
  | None -> fix (eauto_tac hints)
  | Some limit -> fix_limit limit (eauto_tac hints)

let eauto ?(only_classes=true) ?st ?limit hints g =
  let gl = { it = make_autogoal ~only_classes ?st (cut_of_hints hints) None g; sigma = project g; } in
    match run_tac (eauto_tac ?limit hints) gl with
    | None -> raise Not_found
    | Some {it = goals; sigma = s; } ->
	{it = List.map fst goals; sigma = s;}

let real_eauto ?limit unique st hints p evd =
  let res =
    run_on_evars ~st ~unique p evd hints (eauto_tac ?limit hints)
  in
    match res with
    | None -> evd
    | Some (evd', fk) -> 
      if unique then
	(match get_result (fk ()) with
	| Some (evd'', fk') -> error "Typeclass resolution gives multiple solutions"
	| None -> evd')
      else evd'
    
let resolve_all_evars_once debug limit unique p evd =
  let db = searchtable_map typeclasses_db in
    real_eauto ?limit unique (Hint_db.transparent_state db) [db] p evd

(** We compute dependencies via a union-find algorithm.
    Beware of the imperative effects on the partition structure,
    it should not be shared, but only used locally. *)

module Intpart = Unionfind.Make(Evar.Set)(Evar.Map)

let deps_of_constraints cstrs evm p =
  List.iter (fun (_, _, x, y) ->
    let evx = Evarutil.undefined_evars_of_term evm x in
    let evy = Evarutil.undefined_evars_of_term evm y in
    Intpart.union_set (Evar.Set.union evx evy) p)
    cstrs

let evar_dependencies evm p =
  Evd.fold_undefined
    (fun ev evi _ ->
      let evars = Evar.Set.add ev (Evarutil.undefined_evars_of_evar_info evm evi)
      in Intpart.union_set evars p)
    evm ()

let resolve_one_typeclass env ?(sigma=Evd.empty) gl unique =
  let nc, gl, subst, _, _ = Evarutil.push_rel_context_to_named_context env gl in
  let (gl,t,sigma) =
    Goal.V82.mk_goal sigma nc gl Store.empty in
  let gls = { it = gl ; sigma = sigma; } in
  let hints = searchtable_map typeclasses_db in
  let gls' = eauto ?limit:!typeclasses_depth ~st:(Hint_db.transparent_state hints) [hints] gls in
  let evd = sig_sig gls' in
  let t' = let (ev, inst) = destEvar t in
    mkEvar (ev, Array.of_list subst)
  in
  let term = Evarutil.nf_evar evd t' in
    evd, term

let _ =
  Typeclasses.solve_instantiation_problem := 
    (fun x y z w -> resolve_one_typeclass x ~sigma:y z w)

(** [split_evars] returns groups of undefined evars according to dependencies *)

let split_evars evm =
  let p = Intpart.create () in
  evar_dependencies evm p;
  deps_of_constraints (snd (extract_all_conv_pbs evm)) evm p;
  Intpart.partition p

let is_inference_forced p evd ev =
  try
    let evi = Evd.find_undefined evd ev in
    if Typeclasses.is_resolvable evi && snd (p ev evi)
    then
      let (loc, k) = evar_source ev evd in
      match k with
	| Evar_kinds.ImplicitArg (_, _, b) -> b
	| Evar_kinds.QuestionMark _ -> false
	| _ -> true
    else true
  with Not_found -> assert false

let is_mandatory p comp evd =
  Evar.Set.exists (is_inference_forced p evd) comp

(** In case of unsatisfiable constraints, build a nice error message *)

let error_unresolvable env comp evd =
  let evd = Evarutil.nf_evar_map_undefined evd in
  let is_part ev = match comp with
  | None -> true
  | Some s -> Evar.Set.mem ev s
  in
  let fold ev evi (found, accu) =
    let ev_class = class_of_constr evi.evar_concl in
    if not (Option.is_empty ev_class) && is_part ev then
      (* focus on one instance if only one was searched for *)
      if not found then (true, Some ev)
      else (found, None)
    else (found, accu)
   in
  let (_, ev) = Evd.fold_undefined fold evd (true, None) in
    Pretype_errors.unsatisfiable_constraints
      (Evarutil.nf_env_evar evd env) evd ev comp

(** Check if an evar is concerned by the current resolution attempt,
    (and in particular is in the current component), and also update
    its evar_info.
    Invariant : this should only be applied to undefined evars,
    and return undefined evar_info *)

let select_and_update_evars p oevd in_comp evd ev evi =
  assert (evi.evar_body == Evar_empty);
  try
    let oevi = Evd.find_undefined oevd ev in
    if Typeclasses.is_resolvable oevi then
      Typeclasses.mark_unresolvable evi,
      (in_comp ev && p evd ev evi)
    else evi, false
  with Not_found ->
    Typeclasses.mark_unresolvable evi, p evd ev evi

(** Do we still have unresolved evars that should be resolved ? *)

let has_undefined p oevd evd =
  let check ev evi = snd (p oevd ev evi) in
  Evar.Map.exists check (Evd.undefined_map evd)

(** Revert the resolvability status of evars after resolution,
    potentially unprotecting some evars that were set unresolvable
    just for this call to resolution. *)

let revert_resolvability oevd evd =
  let map ev evi =
    try
      if not (Typeclasses.is_resolvable evi) then
        let evi' = Evd.find_undefined oevd ev in
        if Typeclasses.is_resolvable evi' then
          Typeclasses.mark_resolvable evi
        else evi
      else evi
    with Not_found -> evi
  in
  Evd.raw_map_undefined map evd

(** If [do_split] is [true], we try to separate the problem in
    several components and then solve them separately *)

exception Unresolved

let resolve_all_evars debug m unique env p oevd do_split fail =
  let split = if do_split then split_evars oevd else [Evar.Set.empty] in
  let in_comp comp ev = if do_split then Evar.Set.mem ev comp else true
  in
  let rec docomp evd = function
    | [] -> revert_resolvability oevd evd
    | comp :: comps ->
      let p = select_and_update_evars p oevd (in_comp comp) in
      try
	 let evd' = resolve_all_evars_once debug m unique p evd in
	 if has_undefined p oevd evd' then raise Unresolved;
	 docomp evd' comps
      with Unresolved | Not_found ->
	if fail && (not do_split || is_mandatory (p evd) comp evd)
	then (* Unable to satisfy the constraints. *)
          let comp = if do_split then Some comp else None in
	  error_unresolvable env comp evd
	else (* Best effort: do nothing on this component *)
	  docomp evd comps
  in docomp oevd split

let initial_select_evars filter =
  fun evd ev evi ->
    filter ev (snd evi.Evd.evar_source) &&
    Typeclasses.is_class_evar evd evi

let resolve_typeclass_evars debug m unique env evd filter split fail =
  let evd =
    try Evarconv.consider_remaining_unif_problems
      ~ts:(Typeclasses.classes_transparent_state ()) env evd
    with e when Errors.noncritical e -> evd
  in
    resolve_all_evars debug m unique env (initial_select_evars filter) evd split fail

let solve_inst debug depth env evd filter unique split fail =
  resolve_typeclass_evars debug depth unique env evd filter split fail

let _ =
  Typeclasses.solve_instantiations_problem :=
    solve_inst false !typeclasses_depth

let set_typeclasses_debug d = (:=) typeclasses_debug d;
  Typeclasses.solve_instantiations_problem := solve_inst d !typeclasses_depth

let get_typeclasses_debug () = !typeclasses_debug

let set_typeclasses_depth d = (:=) typeclasses_depth d;
  Typeclasses.solve_instantiations_problem := solve_inst !typeclasses_debug !typeclasses_depth

let get_typeclasses_depth () = !typeclasses_depth

open Goptions

let set_typeclasses_debug =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "debug output for typeclasses proof search";
      optkey   = ["Typeclasses";"Debug"];
      optread  = get_typeclasses_debug;
      optwrite = set_typeclasses_debug; }

let set_typeclasses_depth =
  declare_int_option
    { optsync  = true;
      optdepr  = false;
      optname  = "depth for typeclasses proof search";
      optkey   = ["Typeclasses";"Depth"];
      optread  = get_typeclasses_depth;
      optwrite = set_typeclasses_depth; }

let typeclasses_eauto ?(only_classes=false) ?(st=full_transparent_state) dbs gl =
  try
    let dbs = List.map_filter
      (fun db -> try Some (searchtable_map db)
        with e when Errors.noncritical e -> None)
      dbs
    in
    let st = match dbs with x :: _ -> Hint_db.transparent_state x | _ -> st in
      eauto ?limit:!typeclasses_depth ~only_classes ~st dbs gl
   with Not_found -> tclFAIL 0 (str" typeclasses eauto failed on: " ++ Printer.pr_goal gl) gl

(** Take the head of the arity of a constr.
    Used in the partial application tactic. *)

let rec head_of_constr t =
  let t = strip_outer_cast(collapse_appl t) in
    match kind_of_term t with
    | Prod (_,_,c2)  -> head_of_constr c2
    | LetIn (_,_,_,c2) -> head_of_constr c2
    | App (f,args)  -> head_of_constr f
    | _      -> t

let head_of_constr h c =
  let c = head_of_constr c in
  letin_tac None (Name h) c None Locusops.allHyps

let not_evar c = match kind_of_term c with
| Evar _ -> Tacticals.New.tclFAIL 0 (str"Evar")
| _ -> Proofview.tclUNIT ()

let is_ground c gl =
  if Evarutil.is_ground_term (project gl) c then tclIDTAC gl
  else tclFAIL 0 (str"Not ground") gl

let autoapply c i gl =
  let flags = auto_unif_flags Evar.Set.empty 
    (Hints.Hint_db.transparent_state (Hints.searchtable_map i)) in
  let cty = pf_type_of gl c in
  let ce = mk_clenv_from gl (c,cty) in
  unify_e_resolve false flags (c,ce) gl
