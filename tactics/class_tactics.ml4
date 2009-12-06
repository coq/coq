(* -*- compile-command: "make -C .. bin/coqtop.byte" -*- *)
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
open Proof_type
open Proof_trees
open Declarations
open Tacticals
open Tacmach
open Evar_refiner
open Tactics
open Pattern
open Clenv
open Auto
open Rawterm
open Hiddentac
open Typeclasses
open Typeclasses_errors
open Classes
open Topconstr
open Pfedit
open Command
open Libnames
open Evd

let default_eauto_depth = 100
let typeclasses_db = "typeclass_instances"

let _ = Auto.auto_init := (fun () ->
  Auto.create_hint_db false typeclasses_db full_transparent_state true)

exception Found of evar_map

let is_dependent ev evm =
  Evd.fold (fun ev' evi dep ->
    if ev = ev' then dep
    else dep || occur_evar ev evi.evar_concl)
    evm false

let valid goals p res_sigma l =
  let evm =
    List.fold_left2
      (fun sigma (ev, evi) prf ->
	let cstr, obls = Refiner.extract_open_proof !res_sigma prf in
	  if not (Evd.is_defined sigma ev) then
	    Evd.define ev cstr sigma
	  else sigma)
      !res_sigma goals l
  in raise (Found evm)

let evar_filter evi =
  let hyps' = evar_filtered_context evi in
    { evi with 
      evar_hyps = Environ.val_of_named_context hyps';
      evar_filter = List.map (fun _ -> true) hyps' }
      
let evars_to_goals p evm =
  let goals, evm' =
    Evd.fold
      (fun ev evi (gls, evm') ->
	if evi.evar_body = Evar_empty then
	  let evi', goal = p evm ev evi in
	    if goal then
	      ((ev, evi') :: gls, Evd.add evm' ev evi')
	    else (gls, Evd.add evm' ev evi')
	else (gls, Evd.add evm' ev evi))
      evm ([], Evd.empty)
  in
    if goals = [] then None
    else
      let goals = List.rev goals in
	Some (goals, evm')

(** Typeclasses instance search tactic / eauto *)

let intersects s t =
  Intset.exists (fun el -> Intset.mem el t) s

open Auto

let e_give_exact flags c gl = 
  let t1 = (pf_type_of gl c) in
    tclTHEN (Clenvtac.unify ~flags t1) (exact_no_check c) gl

let assumption flags id = e_give_exact flags (mkVar id)

open Unification

let auto_unif_flags = {
  modulo_conv_on_closed_terms = Some full_transparent_state;
  use_metas_eagerly = true;
  modulo_delta = var_full_transparent_state;
  resolve_evars = false;
  use_evars_pattern_unification = true;
}

let rec eq_constr_mod_evars x y =
  match kind_of_term x, kind_of_term y with
  | Evar (e1, l1), Evar (e2, l2) when e1 <> e2 -> true
  | _, _ -> compare_constr eq_constr_mod_evars x y

let progress_evars t gl =
  let concl = pf_concl gl in
  let check gl' = 
    let newconcl = pf_concl gl' in
      if eq_constr_mod_evars concl newconcl 
      then tclFAIL 0 (str"No progress made (modulo evars)") gl'
      else tclIDTAC gl'
  in tclTHEN t check gl

TACTIC EXTEND progress_evars
  [ "progress_evars" tactic(t) ] -> [ progress_evars (snd t) ]
END

let unify_e_resolve flags (c,clenv) gls =
  let clenv' = connect_clenv gls clenv in
  let clenv' = clenv_unique_resolver false ~flags clenv' gls in
    tclPROGRESS (Clenvtac.clenv_refine true ~with_classes:false clenv') gls

let unify_resolve flags (c,clenv) gls =
  let clenv' = connect_clenv gls clenv in
  let clenv' = clenv_unique_resolver false ~flags clenv' gls in
    tclPROGRESS (Clenvtac.clenv_refine false ~with_classes:false clenv') gls

(** Hack to properly solve dependent evars that are typeclasses *)

let flags_of_state st =
  {auto_unif_flags with
    modulo_conv_on_closed_terms = Some st; modulo_delta = st}

let rec e_trivial_fail_db db_list local_db goal =
  let tacl =
    Eauto.registered_e_assumption ::
    (tclTHEN Tactics.intro
       (function g'->
	  let d = pf_last_hyp g' in
	  let hintl = make_resolve_hyp (pf_env g') (project g') d in
          (e_trivial_fail_db db_list
	      (Hint_db.add_list hintl local_db) g'))) ::
    (List.map (fun (x,_,_,_) -> x) (e_trivial_resolve db_list local_db (pf_concl goal)))
  in 
  tclFIRST (List.map tclCOMPLETE tacl) goal 

and e_my_find_search db_list local_db hdc concl =
  let hdc = head_of_constr_reference hdc in
  let hintl =
    list_map_append
      (fun db ->
	if Hint_db.use_dn db then
	  let flags = flags_of_state (Hint_db.transparent_state db) in
	    List.map (fun x -> (flags, x)) (Hint_db.map_auto (hdc,concl) db)
	else
	  let flags = flags_of_state (Hint_db.transparent_state db) in
	    List.map (fun x -> (flags, x)) (Hint_db.map_all hdc db))
      (local_db::db_list)
  in
  let tac_of_hint =
    fun (flags, {pri=b; pat = p; code=t}) ->
      let tac =
	match t with
	  | Res_pf (term,cl) -> unify_resolve flags (term,cl)
	  | ERes_pf (term,cl) -> unify_e_resolve flags (term,cl)
	  | Give_exact (c) -> e_give_exact flags c
	  | Res_pf_THEN_trivial_fail (term,cl) ->
              tclTHEN (unify_e_resolve flags (term,cl))
		(e_trivial_fail_db db_list local_db)
	  | Unfold_nth c -> tclWEAK_PROGRESS (unfold_in_concl [all_occurrences,c])
	  | Extern tacast -> conclPattern concl p tacast
      in
	match t with
	| Extern _ -> (tac,b,true,pr_autotactic t)
	| _ -> (tac,b,false,pr_autotactic t)
  in List.map tac_of_hint hintl

and e_trivial_resolve db_list local_db gl =
  try
    e_my_find_search db_list local_db
      (fst (head_constr_bound gl)) gl
  with Bound | Not_found -> []

let e_possible_resolve db_list local_db gl =
  try
    e_my_find_search db_list local_db
      (fst (head_constr_bound gl)) gl
  with Bound | Not_found -> []

let rec catchable = function
  | Refiner.FailError _ -> true
  | Stdpp.Exc_located (_, e) -> catchable e
  | e -> Logic.catchable_exception e

let is_dep gl gls =
  let evs = Evarutil.evars_of_term gl.evar_concl in
    if evs = Intset.empty then false
    else
      List.fold_left
	(fun b gl ->
	  if b then b
	  else
	    let evs' = Evarutil.evars_of_term gl.evar_concl in
	      intersects evs evs')
	false gls

let is_ground gl =
  Evarutil.is_ground_term (project gl) (pf_concl gl)

let nb_empty_evars s =
  Evd.fold (fun ev evi acc -> if evi.evar_body = Evar_empty then succ acc else acc) s 0

let pr_ev evs ev = Printer.pr_constr_env (Evd.evar_env ev) (Evarutil.nf_evar evs ev.Evd.evar_concl)

let typeclasses_debug = ref false

type validation = evar_map -> proof_tree list -> proof_tree

let pr_depth l = prlist_with_sep (fun () -> str ".") pr_int (List.rev l)

type autoinfo = { hints : Auto.hint_db; is_evar: existential_key option;
		  only_classes: bool; auto_depth: int list; auto_last_tac: std_ppcmds }
type autogoal = goal * autoinfo
type 'ans fk = unit -> 'ans
type ('a,'ans) sk = 'a -> 'ans fk -> 'ans
type 'a tac = { skft : 'ans. ('a,'ans) sk -> 'ans fk -> autogoal sigma -> 'ans }

type auto_result = autogoal list sigma * validation

type atac = auto_result tac

let make_resolve_hyp env sigma st flags only_classes pri (id, _, cty) =
  let cty = Evarutil.nf_evar sigma cty in
  let keep = not only_classes || 
    let ctx, ar = decompose_prod cty in
      match kind_of_term (fst (decompose_app ar)) with
      | Const c -> is_class (ConstRef c)
      | Ind i -> is_class (IndRef i)
      | _ -> false
  in
    if keep then let c = mkVar id in
      map_succeed 
	(fun f -> try f (c,cty) with UserError _ -> failwith "") 
	[make_exact_entry pri; make_apply_entry env sigma flags pri]
    else []

let pf_filtered_hyps gls = 
  evar_filtered_context (sig_it gls)

let make_autogoal_hints only_classes ?(st=full_transparent_state) g =
  let sign = pf_filtered_hyps g in
  let hintlist = list_map_append (pf_apply make_resolve_hyp g st (true,false,false) only_classes None) sign in
    Hint_db.add_list hintlist (Hint_db.empty st true)
  
let lift_tactic tac (f : goal list sigma -> autoinfo -> autogoal list sigma) : 'a tac =
  { skft = fun sk fk {it = gl,hints; sigma=s} ->
    let res = try Some (tac {it=gl; sigma=s}) with e when catchable e -> None in
      match res with
      | Some (gls,v) -> sk (f gls hints, fun _ -> v) fk
      | None -> fk () }

let intro_tac : atac =
  lift_tactic Tactics.intro
    (fun {it = gls; sigma = s} info ->
      let gls' =
	List.map (fun g' ->
	  let env = evar_env g' in
	  let hint = make_resolve_hyp env s (Hint_db.transparent_state info.hints) 
	    (true,false,false) info.only_classes None (List.hd (evar_context g')) in
	  let ldb = Hint_db.add_list hint info.hints in
	    (g', { info with is_evar = None; hints = ldb; auto_last_tac = str"intro" })) gls
      in {it = gls'; sigma = s})

let normevars_tac : atac = 
  lift_tactic tclNORMEVAR
    (fun {it = gls; sigma = s} info ->
      let gls' =
	List.map (fun g' ->
	  (g', { info with auto_last_tac = str"NORMEVAR" })) gls
      in {it = gls'; sigma = s})


let id_tac : atac =
  { skft = fun sk fk {it = gl; sigma = s} ->
    sk ({it = [gl]; sigma = s}, fun _ pfs -> List.hd pfs) fk }

(* Ordering of states is lexicographic on the number of remaining goals. *)
let compare (pri, _, _, (res, _)) (pri', _, _, (res', _)) =
  let nbgoals s =
    List.length (sig_it s) + nb_empty_evars (sig_sig s)
  in
  let pri = pri - pri' in
    if pri <> 0 then pri
    else nbgoals res - nbgoals res'

let or_tac (x : 'a tac) (y : 'a tac) : 'a tac =
  { skft = fun sk fk gls -> x.skft sk (fun () -> y.skft sk fk gls) gls }

let solve_tac (x : 'a tac) : 'a tac =
  { skft = fun sk fk gls -> x.skft (fun ({it = gls},_ as res) fk -> if gls = [] then sk res fk else fk ()) fk gls }

let hints_tac hints =
  { skft = fun sk fk {it = gl,info; sigma = s} ->
    let possible_resolve ((lgls,v) as res, pri, b, pp) =
      (pri, pp, b, res)
    in
    let tacs =
      let concl = gl.evar_concl in
      let poss = e_possible_resolve hints info.hints concl in
      let l =
	let tacgl = {it = gl; sigma = s} in
	Util.list_map_append (fun (tac, pri, b, pptac) ->
	  try [tac tacgl, pri, b, pptac] with e when catchable e -> [])
	  poss
      in
	if l = [] && !typeclasses_debug then
	  msgnl (pr_depth info.auto_depth ++ str": no match for " ++
		    Printer.pr_constr_env (Evd.evar_env gl) concl ++
		    spc () ++ int (List.length poss) ++ str" possibilities");
	List.map possible_resolve l
    in
    let tacs = List.sort compare tacs in
    let rec aux i = function
      | (_, pp, b, ({it = gls; sigma = s}, v)) :: tl ->
	  if !typeclasses_debug then msgnl (pr_depth (i :: info.auto_depth) ++ str": " ++ pp
					       ++ str" on" ++ spc () ++ pr_ev s gl);
	  let fk =
	    (fun () -> (* if !typeclasses_debug then msgnl (str"backtracked after " ++ pp); *)
	    aux (succ i) tl)
	  in
	  let gls' = list_map_i (fun j g -> 
	    let info = 
	      { info with auto_depth = j :: i :: info.auto_depth; auto_last_tac = pp;
		is_evar = None;
		hints = 
		  if b && g.evar_hyps <> gl.evar_hyps 
		  then make_autogoal_hints info.only_classes
		    ~st:(Hint_db.transparent_state info.hints) {it = g; sigma = s}
		  else info.hints }
	    in g, info) 1 gls in
	  let glsv = {it = gls'; sigma = s}, (fun _ -> v) in
	    sk glsv fk
      | [] -> fk ()
    in aux 1 tacs }

let evars_of_term c =
  let rec evrec acc c =
    match kind_of_term c with
    | Evar (n, _) -> Intset.add n acc
    | _ -> fold_constr evrec acc c
  in evrec Intset.empty c

exception Found_evar of int

let occur_evars evars c =
  try
    let rec evrec c =
      match kind_of_term c with
      | Evar (n, _) -> if Intset.mem n evars then raise (Found_evar n) else ()
      | _ -> iter_constr evrec c
    in evrec c; false
  with Found_evar _ -> true

let dependent only_classes evd oev concl =
  let concl_evars = Intset.union (evars_of_term concl)
    (Option.cata Intset.singleton Intset.empty oev)
  in not (Intset.is_empty concl_evars)

let then_list (second : atac) (sk : (auto_result, 'a) sk) : (auto_result, 'a) sk =
  let rec aux s (acc : (autogoal list * validation) list) fk = function
    | (gl,info) :: gls ->
	second.skft (fun ({it=gls';sigma=s'},v') fk' ->
	  let s', needs_backtrack = 
	    if gls' = [] then
	      match info.is_evar with
	      | Some ev -> 
		  let s' = 
		    if Evd.is_defined s' ev then s' 
		    else
		      let prf = v' s' [] in
		      let term, _ = Refiner.extract_open_proof s' prf in
			Evd.define ev term s' 
		  in s', dependent info.only_classes s' (Some ev) gl.evar_concl
	      | None -> s', dependent info.only_classes s' None gl.evar_concl
	    else s', true
	  in
	  let fk'' = if not needs_backtrack then
	    (if !typeclasses_debug then msgnl (str"no backtrack on " ++ pr_ev s gl); fk) else fk' 
	  in aux s' ((gls',v')::acc) fk'' gls)
	  fk {it = (gl,info); sigma = s}
    | [] -> Some (List.rev acc, s, fk)
  in fun ({it = gls; sigma = s},v) fk ->
    let rec aux' = function
      | None -> fk ()
      | Some (res, s', fk') ->
	  let goals' = List.concat (List.map (fun (gls,v) -> gls) res) in
	  let v' s' pfs' : proof_tree =
	    let (newpfs, rest) = List.fold_left (fun (newpfs,pfs') (gls,v) ->
	      let before, after = list_split_at (List.length gls) pfs' in
		(v s' before :: newpfs, after))
	      ([], pfs') res
	    in assert(rest = []); v s' (List.rev newpfs)
	  in sk ({it = goals'; sigma = s'}, v') (fun () -> aux' (fk' ()))
    in aux' (aux s [] (fun () -> None) gls)

let then_tac (first : atac) (second : atac) : atac =
  { skft = fun sk fk -> first.skft (then_list second sk) fk }

let run_tac (t : 'a tac) (gl : autogoal sigma) : auto_result option =
  t.skft (fun x _ -> Some x) (fun _ -> None) gl


type run_list_res = (auto_result * run_list_res fk) option

let run_list_tac (t : 'a tac) p goals (gl : autogoal list sigma) : run_list_res =
  (then_list t (fun x fk -> Some (x, fk)))
    (gl, fun s pfs -> valid goals p (ref s) pfs)
    (fun _ -> None)

let rec fix (t : 'a tac) : 'a tac =
  then_tac t { skft = fun sk fk -> (fix t).skft sk fk }

let make_autogoal ?(only_classes=true) ?(st=full_transparent_state) ev g =
  let hints = make_autogoal_hints only_classes ~st g in
    (g.it, { hints = hints ; is_evar = ev; 
	     only_classes = only_classes; auto_depth = []; auto_last_tac = mt() })
      
let make_autogoals ?(only_classes=true) ?(st=full_transparent_state) gs evm' =
  { it = list_map_i (fun i g -> 
    let (gl, auto) = make_autogoal ~only_classes ~st (Some (fst g)) {it = snd g; sigma = evm'} in
      (gl, { auto with auto_depth = [i]})) 1 gs; sigma = evm' }

let get_result r = 
  match r with
  | None -> None
  | Some ((gls, v), fk) ->
      try ignore(v (sig_sig gls) []); assert(false)
      with Found evm' -> Some (evm', fk)

let run_on_evars ?(only_classes=true) ?(st=full_transparent_state) p evm tac =
  match evars_to_goals p evm with
  | None -> None (* This happens only because there's no evar having p *)
  | Some (goals, evm') ->
      let res = run_list_tac tac p goals (make_autogoals ~only_classes ~st goals evm') in
	match get_result res with
	| None -> raise Not_found
	| Some (evm', fk) -> Some (Evd.evars_reset_evd evm' evm, fk)
	    
let eauto_tac hints = 
  fix (or_tac (then_tac normevars_tac (hints_tac hints)) intro_tac)
  
let eauto ?(only_classes=true) ?st hints g =
  let gl = { it = make_autogoal ~only_classes ?st None g; sigma = project g } in
    match run_tac (eauto_tac hints) gl with
    | None -> raise Not_found
    | Some ({it = goals; sigma = s}, valid) ->
	{it = List.map fst goals; sigma = s}, valid s

let real_eauto st hints p evd =
  let rec aux evd fails =
    let res, fails =
      try run_on_evars ~st p evd (eauto_tac hints), fails
      with Not_found ->
	List.fold_right (fun fk (res, fails) ->
	  match res with
	  | Some r -> res, fk :: fails
	  | None -> get_result (fk ()), fails)
	  fails (None, [])
    in
      match res with
      | None -> evd
      | Some (evd', fk) -> aux evd' (fk :: fails)
  in aux evd []

let resolve_all_evars_once debug (mode, depth) p evd =
  let db = searchtable_map typeclasses_db in
    real_eauto (Hint_db.transparent_state db) [db] p evd

exception FoundTerm of constr

let resolve_one_typeclass env ?(sigma=Evd.empty) gl =
  let gls = { it = Evd.make_evar (Environ.named_context_val env) gl; sigma = sigma } in
  let gls', v = eauto [searchtable_map typeclasses_db] gls in
  let term = v [] in
  let evd = sig_sig gls' in
  let term = fst (Refiner.extract_open_proof evd term) in
  let term = Evarutil.nf_evar evd term in
    evd, term

let _ =
  Typeclasses.solve_instanciation_problem := (fun x y z -> resolve_one_typeclass x ~sigma:y z)

let has_undefined p oevd evd =
  Evd.fold (fun ev evi has -> has ||
    (evi.evar_body = Evar_empty && snd (p oevd ev evi)))
    evd false

let rec merge_deps deps = function
  | [] -> [deps]
  | hd :: tl ->
      if intersects deps hd then
	merge_deps (Intset.union deps hd) tl
      else hd :: merge_deps deps tl

let evars_of_evi evi =
  Intset.union (Evarutil.evars_of_term evi.evar_concl)
    (match evi.evar_body with
    | Evar_defined b -> Evarutil.evars_of_term b
    | Evar_empty -> Intset.empty)

let split_evars evm =
  Evd.fold (fun ev evi acc ->
    let deps = Intset.union (Intset.singleton ev) (evars_of_evi evi) in
      merge_deps deps acc)
    evm []

let select_evars evs evm =
  Evd.fold (fun ev evi acc ->
    if Intset.mem ev evs then Evd.add acc ev evi else acc)
    evm Evd.empty

let is_inference_forced p ev evd =
  try
    let evi = Evd.find evd ev in
      if evi.evar_body = Evar_empty then
	if Typeclasses.is_resolvable evi
	  && snd (p ev evi)
	then
	  let (loc, k) = evar_source ev evd in
	    match k with
	    | ImplicitArg (_, _, b) -> b
	    | QuestionMark _ -> false
	    | _ -> true
	else true
      else false
  with Not_found -> true

let is_optional p comp evd =
  Intset.fold (fun ev acc ->
    acc && not (is_inference_forced p ev evd))
    comp true

let resolve_all_evars debug m env p oevd do_split fail =
  let split = if do_split then split_evars oevd else [Intset.empty] in
  let p = if do_split then
    fun comp evd ev evi -> 
      if evi.evar_body = Evar_empty then
	(try let oevi = Evd.find oevd ev in
	       if Typeclasses.is_resolvable oevi then
		 Typeclasses.mark_unresolvable evi, (Intset.mem ev comp &&
							p evd ev evi)
	       else evi, false
	  with Not_found ->
	    Typeclasses.mark_unresolvable evi, p evd ev evi)
      else evi, false
    else fun _ evd ev evi -> 
      if evi.evar_body = Evar_empty then
	try let oevi = Evd.find oevd ev in
	      if Typeclasses.is_resolvable oevi then
		Typeclasses.mark_unresolvable evi, p evd ev evi
	      else evi, false
	with Not_found ->
	  Typeclasses.mark_unresolvable evi, p evd ev evi
      else evi, false
  in
  let rec aux p evd =
    let evd' = resolve_all_evars_once debug m p evd in
      if has_undefined p oevd evd' then None
      else Some evd'
  in
  let rec docomp evd = function
    | [] -> evd
    | comp :: comps ->
	let res = try aux (p comp) evd with Not_found -> None in
	  match res with
	  | None -> 
	      if fail && (not do_split || not (is_optional (p comp evd) comp evd)) then
		(* Unable to satisfy the constraints. *)		
		let evd = Evarutil.nf_evars evd in
		let evm = if do_split then select_evars comp evd else evd in
		let _, ev = Evd.fold
		  (fun ev evi (b,acc) ->
		    (* focus on one instance if only one was searched for *)
		    if class_of_constr evi.evar_concl <> None then
		      if not b (* || do_split *) then
			true, Some ev
		      else b, None
		    else b, acc) evm (false, None)
		in
		  Typeclasses_errors.unsatisfiable_constraints (Evarutil.nf_env_evar evm env) evm ev
	      else (* Best effort: do nothing *) oevd
	  | Some evd' -> docomp evd' comps
  in docomp oevd split

let resolve_typeclass_evars d p env evd onlyargs split fail =
  let pred =
    if onlyargs then
      (fun evd ev evi -> Typeclasses.is_implicit_arg (snd (Evd.evar_source ev evd)) &&
	Typeclasses.is_class_evar evd evi)
    else (fun evd ev evi -> Typeclasses.is_class_evar evd evi)
  in resolve_all_evars d p env pred evd split fail

let solve_inst debug mode depth env evd onlyargs split fail =
  resolve_typeclass_evars debug (mode, depth) env evd onlyargs split fail

let _ =
  Typeclasses.solve_instanciations_problem :=
    solve_inst false true default_eauto_depth

let set_transparency cl b =
  List.iter (fun r -> 
    let gr = Smartlocate.global_with_alias r in
    let ev = Tacred.evaluable_of_global_reference (Global.env ()) gr in
      Classes.set_typeclass_transparency ev b) cl

VERNAC COMMAND EXTEND Typeclasses_Unfold_Settings
| [ "Typeclasses" "Transparent" reference_list(cl) ] -> [
    set_transparency cl true ]
END

VERNAC COMMAND EXTEND Typeclasses_Rigid_Settings
| [ "Typeclasses" "Opaque" reference_list(cl) ] -> [
    set_transparency cl false ]
END

open Genarg
open Extraargs

let pr_debug _prc _prlc _prt b =
  if b then Pp.str "debug" else Pp.mt()

ARGUMENT EXTEND debug TYPED AS bool PRINTED BY pr_debug
| [ "debug" ] -> [ true ]
| [ ] -> [ false ]
END

let pr_mode _prc _prlc _prt m =
  match m with
      Some b ->
	if b then Pp.str "depth-first" else Pp.str "breadth-fist"
    | None -> Pp.mt()

ARGUMENT EXTEND search_mode TYPED AS bool option PRINTED BY pr_mode
| [ "dfs" ] -> [ Some true ]
| [ "bfs" ] -> [ Some false ]
| [] -> [ None ]
END

let pr_depth _prc _prlc _prt = function
    Some i -> Util.pr_int i
  | None -> Pp.mt()

ARGUMENT EXTEND depth TYPED AS int option PRINTED BY pr_depth
| [ int_or_var_opt(v) ] -> [ match v with Some (ArgArg i) -> Some i | _ -> None ]
END

VERNAC COMMAND EXTEND Typeclasses_Settings
 | [ "Typeclasses" "eauto" ":=" debug(d) search_mode(s) depth(depth) ] -> [
     typeclasses_debug := d;
     let mode = match s with Some t -> t | None -> true in
     let depth = match depth with Some i -> i | None -> default_eauto_depth in
       Typeclasses.solve_instanciations_problem :=
	 solve_inst d mode depth
   ]
END

let typeclasses_eauto ?(only_classes=false) ?(st=full_transparent_state) dbs gl =
  try 
    let dbs = list_map_filter (fun db -> try Some (Auto.searchtable_map db) with _ -> None) dbs in
    let st = match dbs with x :: _ -> Hint_db.transparent_state x | _ -> st in
      eauto ~only_classes ~st dbs gl
   with Not_found -> tclFAIL 0 (str" typeclasses eauto failed") gl
 
TACTIC EXTEND typeclasses_eauto
| [ "typeclasses" "eauto" "with" ne_preident_list(l) ] -> [ typeclasses_eauto l ]
| [ "typeclasses" "eauto" ] -> [ typeclasses_eauto ~only_classes:true [typeclasses_db] ]
END

let _ = Classes.refine_ref := Refine.refine

(** Take the head of the arity af constr. *)

let rec head_of_constr t =
  let t = strip_outer_cast(collapse_appl t) in
    match kind_of_term t with
    | Prod (_,_,c2)  -> head_of_constr c2
    | LetIn (_,_,_,c2) -> head_of_constr c2
    | App (f,args)  -> head_of_constr f
    | _      -> t

TACTIC EXTEND head_of_constr
  [ "head_of_constr" ident(h) constr(c) ] -> [
    let c = head_of_constr c in
      letin_tac None (Name h) c None allHyps
  ]
END

(** A tactic to help reification based on classes:
    factorize all variables of a particular type into a varmap. *)

let gen_constant dir s = Coqlib.gen_constant "typeclass_tactics" dir s
let coq_List_nth = lazy (gen_constant ["Lists"; "List"] "nth")
let coq_List_cons = lazy (gen_constant ["Lists"; "List"] "cons")
let coq_List_nil = lazy (gen_constant ["Lists"; "List"] "nil")

let freevars c =
  let rec frec acc c = match kind_of_term c with
    | Var id       -> Idset.add id acc
    | _ -> fold_constr frec acc c
  in
  frec Idset.empty c

let coq_zero = lazy (gen_constant ["Init"; "Datatypes"] "O")
let coq_succ = lazy (gen_constant ["Init"; "Datatypes"] "S")
let coq_nat = lazy (gen_constant ["Init"; "Datatypes"] "nat")

let rec coq_nat_of_int = function
  | 0 -> Lazy.force coq_zero
  | n -> mkApp (Lazy.force coq_succ, [| coq_nat_of_int (pred n) |])

let varify_constr_list ty def varh c =
  let vars = Idset.elements (freevars c) in
  let mkaccess i =
    mkApp (Lazy.force coq_List_nth,
	  [| ty; coq_nat_of_int i; varh; def |])
  in
  let l = List.fold_right (fun id acc ->
    mkApp (Lazy.force coq_List_cons, [| ty ; mkVar id; acc |]))
    vars (mkApp (Lazy.force coq_List_nil, [| ty |]))
  in
  let subst =
    list_map_i (fun i id -> (id, mkaccess i)) 0 vars
  in
    l, replace_vars subst c

let coq_varmap_empty =  lazy (gen_constant ["quote"; "Quote"] "Empty_vm")
let coq_varmap_node =  lazy (gen_constant ["quote"; "Quote"] "Node_vm")
let coq_varmap_lookup =  lazy (gen_constant ["quote"; "Quote"] "varmap_find")

let coq_index_left =  lazy (gen_constant ["quote"; "Quote"] "Left_idx")
let coq_index_right =  lazy (gen_constant ["quote"; "Quote"] "Right_idx")
let coq_index_end =  lazy (gen_constant ["quote"; "Quote"] "End_idx")

let rec split_interleaved l r = function
  | hd :: hd' :: tl' ->
      split_interleaved (hd :: l) (hd' :: r) tl'
  | hd :: [] -> (List.rev (hd :: l), List.rev r)
  | [] -> (List.rev l, List.rev r)

let rec mkidx i p =
  if i mod 2 = 0 then
    if i = 0 then mkApp (Lazy.force coq_index_left, [|Lazy.force coq_index_end|])
    else mkApp (Lazy.force coq_index_left, [|mkidx (i - p) (2 * p)|])
  else if i = 1 then mkApp (Lazy.force coq_index_right, [|Lazy.force coq_index_end|])
  else mkApp (Lazy.force coq_index_right, [|mkidx (i - p) (2 * p)|])

let varify_constr_varmap ty def varh c =
  let vars = Idset.elements (freevars c) in
  let mkaccess i =
    mkApp (Lazy.force coq_varmap_lookup,
	  [| ty; def; i; varh |])
  in
  let rec vmap_aux l cont =
    match l with
    | [] -> [], mkApp (Lazy.force coq_varmap_empty, [| ty |])
    | hd :: tl ->
	let left, right = split_interleaved [] [] tl in
	let leftvars, leftmap = vmap_aux left (fun x -> cont (mkApp (Lazy.force coq_index_left, [| x |]))) in
	let rightvars, rightmap = vmap_aux right (fun x -> cont (mkApp (Lazy.force coq_index_right, [| x |]))) in
	  (hd, cont (Lazy.force coq_index_end)) :: leftvars @ rightvars,
	mkApp (Lazy.force coq_varmap_node, [| ty; hd; leftmap ; rightmap |])
  in
  let subst, vmap = vmap_aux (def :: List.map (fun x -> mkVar x) vars) (fun x -> x) in
  let subst = List.map (fun (id, x) -> (destVar id, mkaccess x)) (List.tl subst) in
    vmap, replace_vars subst c


TACTIC EXTEND varify
  [ "varify" ident(varh) ident(h') constr(ty) constr(def) constr(c) ] -> [
    let vars, c' = varify_constr_varmap ty def (mkVar varh) c in
      tclTHEN (letin_tac None (Name varh) vars None allHyps)
	(letin_tac None (Name h') c' None allHyps)
  ]
END

TACTIC EXTEND not_evar
  [ "not_evar" constr(ty) ] -> [
    match kind_of_term ty with
    | Evar _ -> tclFAIL 0 (str"Evar")
    | _ -> tclIDTAC ]
END

TACTIC EXTEND is_ground
  [ "is_ground" constr(ty) ] -> [ fun gl ->
    if Evarutil.is_ground_term (project gl) ty then tclIDTAC gl
    else tclFAIL 0 (str"Not ground") gl ]
END

TACTIC EXTEND autoapply
  [ "autoapply" constr(c) "using" preident(i) ] -> [ fun gl ->
    let flags = flags_of_state (Auto.Hint_db.transparent_state (Auto.searchtable_map i)) in
    let cty = pf_type_of gl c in
    let ce = mk_clenv_from gl (c,cty) in
      unify_e_resolve flags (c,ce) gl ]
END
