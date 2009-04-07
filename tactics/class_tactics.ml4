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

(** Typeclasses instance search tactic / eauto *)

let intersects s t =
  Intset.exists (fun el -> Intset.mem el t) s

open Auto

let e_give_exact flags c gl = 
  let t1 = (pf_type_of gl c) and t2 = pf_concl gl in 
    if occur_existential t1 or occur_existential t2 then 
      tclTHEN (Clenvtac.unify (* ~flags *) t1) (exact_no_check c) gl
    else exact_check c gl
(*   let t1 = (pf_type_of gl c) in *)
(*     tclTHEN (Clenvtac.unify ~flags t1) (exact_no_check c) gl *)
      
let assumption flags id = e_give_exact flags (mkVar id)

open Unification

let auto_unif_flags = {
  modulo_conv_on_closed_terms = Some full_transparent_state;
  use_metas_eagerly = true;
  modulo_delta = var_full_transparent_state;
}

let unify_e_resolve flags (c,clenv) gls = 
  let clenv' = connect_clenv gls clenv in
  let clenv' = clenv_unique_resolver false ~flags clenv' gls in
    Clenvtac.clenv_refine true ~with_classes:false clenv' gls
      
let unify_resolve flags (c,clenv) gls = 
  let clenv' = connect_clenv gls clenv in
  let clenv' = clenv_unique_resolver false ~flags clenv' gls in
    Clenvtac.clenv_refine false ~with_classes:false clenv' gls

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
    (List.map pi1 (e_trivial_resolve db_list local_db (pf_concl goal)) )
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
	  | Unfold_nth c -> unfold_in_concl [all_occurrences,c]
	  | Extern tacast -> conclPattern concl p tacast
      in 
	(tac,b,pr_autotactic t)
  in 
    List.map tac_of_hint hintl

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

let find_first_goal gls = 
  try first_goal gls with UserError _ -> assert false
    
type search_state = { 
  depth : int; (*r depth of search before failing *)
  tacres : goal list sigma * validation;
  pri : int;
  last_tactic : std_ppcmds;
  dblist : Auto.hint_db list;
  localdb : (bool ref * bool ref option * Auto.hint_db) list }
    
let filter_hyp t = 
  match kind_of_term t with
    | Evar _ | Meta _ | Sort _ -> false
    | _ -> true

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
	
module SearchProblem = struct
    
  type state = search_state

  let debug = ref false

  let success s = sig_it (fst s.tacres) = []

  let pr_ev evs ev = Printer.pr_constr_env (Evd.evar_env ev) (Evarutil.nf_evar evs ev.Evd.evar_concl)
    
  let pr_goals gls =
    let evars = Evarutil.nf_evars (Refiner.project gls) in
      prlist (pr_ev evars) (sig_it gls)
	
  let filter_tactics (glls,v) l =
    let glls,nv = apply_tac_list Refiner.tclNORMEVAR glls in
    let v p = v (nv p) in
    let rec aux = function
      | [] -> []
      | (tac,pri,pptac) :: tacl -> 
	  try 
	    let (lgls,ptl) = apply_tac_list tac glls in 
	    let v' p = v (ptl p) in
	      ((lgls,v'),pri,pptac) :: aux tacl
	  with e when catchable e -> aux tacl
    in aux l
      
  let nb_empty_evars s = 
    Evd.fold (fun ev evi acc -> if evi.evar_body = Evar_empty then succ acc else acc) s 0

  (* Ordering of states is lexicographic on depth (greatest first) then
     priority (lowest pri means higher priority), then number of remaining goals. *)
  let compare s s' =
    let d = s'.depth - s.depth in
    let nbgoals s = 
      List.length (sig_it (fst s.tacres)) + 
	nb_empty_evars (sig_sig (fst s.tacres))
    in
      if d <> 0 then d else
	let pri = s.pri - s'.pri in
	  if pri <> 0 then pri
	  else nbgoals s - nbgoals s'
	  
  let branching s = 
    if s.depth = 0 then 
      []
    else      
      let (cut, do_cut, ldb as hdldb) = List.hd s.localdb in
	if !cut then
(* 	  let {it=gls; sigma=sigma} = fst s.tacres in *)
(* 	    msg (str"cut:" ++ pr_ev sigma (List.hd gls) ++ str"\n"); *)
	    []
	else begin
	  let {it=gl; sigma=sigma} = fst s.tacres in 
	    Option.iter (fun r ->
(*  	      msg (str"do cut:" ++ pr_ev sigma (List.hd gl) ++ str"\n"); *)
	      r := true) do_cut;
(* 	  let sigma = Evarutil.nf_evars sigma in *)
	  let gl = List.map (Evarutil.nf_evar_info sigma) gl in
	  let nbgl = List.length gl in
(* 	  let gl' = { it = gl ; sigma = sigma } in *)
(* 	  let tacres' = gl', snd s.tacres in *)
	  let new_db, localdb =
	    let tl = List.tl s.localdb in hdldb, tl
(* 	      match tl with *)
(* 	      | [] -> hdldb, tl *)
(* 	      | (cut', do', ldb') :: rest -> *)
(* 		  if not (is_dep (List.hd gl) (List.tl gl)) then *)
(* 		    let fresh = ref false in *)
(* 		      if do' = None then ( *)
(* (\*  			msg (str"adding a cut:" ++ pr_ev sigma (List.hd gl) ++ str"\n"); *\) *)
(* 			(fresh, None, ldb), (cut', Some fresh, ldb') :: rest *)
(* 		      ) else ( *)
(* (\* 			msg (str"keeping the previous cut:" ++ pr_ev sigma (List.hd gl) ++ str"\n"); *\) *)
(* 			(cut', None, ldb), tl ) *)
(* 		  else hdldb, tl *)
	  in let localdb = new_db :: localdb in
	  let intro_tac =
	    List.map
	      (fun ((lgls,_) as res,pri,pp) ->
		let g' = first_goal lgls in
		let hintl =
		  make_resolve_hyp (pf_env g') (project g') (pf_last_hyp g')
		in
		let ldb = Hint_db.add_list hintl ldb in
		  { s with tacres = res;
		    last_tactic = pp;
		    pri = pri;
		    localdb = (cut, None, ldb) :: List.tl s.localdb })
	      (filter_tactics s.tacres [Tactics.intro,1,(str "intro")])
	  in
	  let possible_resolve ((lgls,_) as res, pri, pp) =
	    let nbgl' = List.length (sig_it lgls) in
	      if nbgl' < nbgl then
		{ s with 
		  depth = pred s.depth;
		  tacres = res; last_tactic = pp; pri = pri;
		  localdb = List.tl localdb }
	      else 
		{ s with depth = pred s.depth; tacres = res; 
		  last_tactic = pp; pri = pri;
		  localdb = list_tabulate (fun _ -> new_db) (nbgl'-nbgl) @ localdb }
	  in
	  let rec_tacs = 
	    let l = 
	      filter_tactics s.tacres (e_possible_resolve s.dblist ldb (List.hd gl).evar_concl)
	    in
	      List.map possible_resolve l
	  in
	    List.sort compare (intro_tac @ rec_tacs)
	end
	  
  let pp s = 
    msg (hov 0 (str " depth=" ++ int s.depth ++ spc () ++ 
		  s.last_tactic ++ str "\n"))

end

module Search = Explore.Make(SearchProblem)

let make_initial_state n gls dblist localdbs =
  { depth = n;
    tacres = gls;
    pri = 0;
    last_tactic = (mt ());
    dblist = dblist;
    localdb = localdbs }

let e_depth_search debug s =
  let tac = if debug then
    (SearchProblem.debug := true; Search.debug_depth_first) else Search.depth_first in
  let s = tac s in
    s.tacres

let e_breadth_search debug s =
  try
    let tac = 
      if debug then Search.debug_breadth_first else Search.breadth_first 
    in let s = tac s in s.tacres
  with Not_found -> error "eauto: breadth first search failed."


(* A special one for getting everything into a dnet. *)

let is_transparent_gr (ids, csts) = function
  | VarRef id -> Idpred.mem id ids
  | ConstRef cst -> Cpred.mem cst csts
  | IndRef _ | ConstructRef _ -> false

let make_resolve_hyp env sigma st flags pri (id, _, cty) =
  let ctx, ar = decompose_prod cty in
  let keep = 
    match kind_of_term (fst (decompose_app ar)) with
    | Const c -> is_class (ConstRef c)
    | Ind i -> is_class (IndRef i)
    | _ -> false
  in
    if keep then let c = mkVar id in
      map_succeed 
	(fun f -> f (c,cty)) 
	[make_exact_entry pri; make_apply_entry env sigma flags pri]
    else []

let make_local_hint_db st eapply lems g =
  let sign = pf_hyps g in
  let hintlist = list_map_append (pf_apply make_resolve_hyp g st (eapply,false,false) None) sign in
  let hintlist' = list_map_append (pf_apply make_resolves g (eapply,false,false) None) lems in
    Hint_db.add_list hintlist' (Hint_db.add_list hintlist (Hint_db.empty st true))

let e_search_auto debug (in_depth,p) lems st db_list gls = 
  let sigma = Evd.sig_sig (fst gls) and gls' = Evd.sig_it (fst gls) in
  let local_dbs = List.map (fun gl -> 
    let db = make_local_hint_db st true lems ({it = gl; sigma = sigma}) in
      (ref false, None, db)) gls' in
  let state = make_initial_state p gls db_list local_dbs in
  if in_depth then 
    e_depth_search debug state
  else
    e_breadth_search debug state

let full_eauto debug n lems gls = 
  let dbnames = current_db_names () in
  let dbnames =  list_subtract dbnames ["v62"] in
  let db_list = List.map searchtable_map dbnames in
  let db = searchtable_map typeclasses_db in
    e_search_auto debug n lems (Hint_db.transparent_state db) db_list gls

let nf_goal (gl, valid) =
  { gl with sigma = Evarutil.nf_evars gl.sigma }, valid

let typeclasses_eauto debug n lems gls =
  let db = searchtable_map typeclasses_db in
    e_search_auto debug n lems (Hint_db.transparent_state db) [db] gls

exception Found of evar_map

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

let is_dependent ev evm = 
  Evd.fold (fun ev' evi dep -> 
    if ev = ev' then dep
    else dep || occur_evar ev evi.evar_concl)
    evm false
    
let resolve_all_evars_once debug (mode, depth) env p evd =
  let evm =  evd in
  let goals, evm' = 
    Evd.fold
      (fun ev evi (gls, evm') ->
	if evi.evar_body = Evar_empty 
	  && Typeclasses.is_resolvable evi
(* 	  && not (is_dependent ev evm) *)
	  && p ev evi then ((ev,evi) :: gls, Evd.add evm' ev (Typeclasses.mark_unresolvable evi)) else 
	  (gls, Evd.add evm' ev evi))
      evm ([], Evd.empty)
  in
  let goals = List.rev goals in
  let gls = { it = List.map snd goals; sigma = evm' } in
  let res_sigma = ref evm' in
  let gls', valid' = typeclasses_eauto debug (mode, depth) [] (gls, valid goals p res_sigma) in
    res_sigma := Evarutil.nf_evars (sig_sig gls');
    try ignore(valid' []); assert(false) 
    with Found evm' -> Evarutil.nf_evar_defs (Evd.evars_reset_evd evm' evd)

exception FoundTerm of constr

let resolve_one_typeclass env ?(sigma=Evd.empty) gl =
  let gls = { it = [ Evd.make_evar (Environ.named_context_val env) gl ] ; sigma = sigma } in
  let valid x = raise (FoundTerm (fst (Refiner.extract_open_proof sigma (List.hd x)))) in
  let gls', valid' = typeclasses_eauto false (true, default_eauto_depth) [] (gls, valid) in
    try ignore(valid' []); assert false with FoundTerm t -> 
      let term = Evarutil.nf_evar (sig_sig gls') t in
	if occur_existential term then raise Not_found else term

let _ = 
  Typeclasses.solve_instanciation_problem := (fun x y z -> resolve_one_typeclass x ~sigma:y z)

let has_undefined p oevd evd =
  Evd.fold (fun ev evi has -> has ||
    (evi.evar_body = Evar_empty && p ev evi && 
	(try Typeclasses.is_resolvable (Evd.find oevd ev) with _ -> true)))
    ( evd) false

let rec merge_deps deps = function
  | [] -> [deps]
  | hd :: tl -> 
      if intersects deps hd then 
	merge_deps (Intset.union deps hd) tl
      else hd :: merge_deps deps tl
	
let split_evars evm =
  Evd.fold (fun ev evi acc ->
    let deps = Intset.union (Intset.singleton ev) (Evarutil.evars_of_term evi.evar_concl) in
      merge_deps deps acc)
    evm []

let select_evars evs evm =
  Evd.fold (fun ev evi acc ->
    if Intset.mem ev evs then Evd.add acc ev evi else acc)
    evm Evd.empty

let resolve_all_evars debug m env p oevd do_split fail =
  let oevm =  oevd in
  let split = if do_split then split_evars (Evd.undefined_evars oevd) else [Intset.empty] in
  let p = if do_split then 
    fun comp ev evi -> (Intset.mem ev comp || not (Evd.mem oevm ev)) && p ev evi
    else fun _ -> p 
  in
  let rec aux n p evd =
    if has_undefined p oevm evd then
      if n > 0 then
	let evd' = resolve_all_evars_once debug m env p evd in
	  aux (pred n) p evd'
      else None
    else Some evd
  in 
  let rec docomp evd = function
    | [] -> evd
    | comp :: comps ->
	let res = try aux 3 (p comp) evd with Not_found -> None in
	  match res with
	  | None -> 
	      if fail then 
		(* Unable to satisfy the constraints. *)
		let evm =  evd in
		let evm = if do_split then select_evars comp evm else evm in
		let _, ev = Evd.fold 
		  (fun ev evi (b,acc) -> 
		    (* focus on one instance if only one was searched for *)
		    if class_of_constr evi.evar_concl <> None then
		      if not b (* || do_split *) then
			true, Some ev 
		      else b, None
		    else b, acc) evm (false, None)
		in
		  Typeclasses_errors.unsatisfiable_constraints env (Evd.evars_reset_evd evm evd) ev
	      else (* Best effort: do nothing *) oevd
	  | Some evd' -> docomp evd' comps
  in docomp oevd split

let resolve_typeclass_evars d p env evd onlyargs split fail =
  let pred = 
    if onlyargs then 
      (fun ev evi -> Typeclasses.is_implicit_arg (snd (Evd.evar_source ev evd)) &&
	Typeclasses.is_class_evar evi)
    else (fun ev evi -> Typeclasses.is_class_evar evi)
  in resolve_all_evars d p env pred evd split fail
    
let solve_inst debug mode depth env evd onlyargs split fail =
  resolve_typeclass_evars debug (mode, depth) env evd onlyargs split fail

let _ = 
  Typeclasses.solve_instanciations_problem :=
    solve_inst false true default_eauto_depth

    
VERNAC COMMAND EXTEND Typeclasses_Unfold_Settings
| [ "Typeclasses" "Transparent" reference_list(cl) ] -> [
    add_hints false [typeclasses_db] (Vernacexpr.HintsTransparency (cl, true))
  ]
END
	
VERNAC COMMAND EXTEND Typeclasses_Rigid_Settings
| [ "Typeclasses" "Opaque" reference_list(cl) ] -> [
    add_hints false [typeclasses_db] (Vernacexpr.HintsTransparency (cl, false))
  ]
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
     let mode = match s with Some t -> t | None -> true in
     let depth = match depth with Some i -> i | None -> default_eauto_depth in
       Typeclasses.solve_instanciations_problem :=
	 solve_inst d mode depth
   ]
END

TACTIC EXTEND typeclasses_eauto
| [ "typeclasses" "eauto" debug(d) search_mode(s) depth(depth) ] -> [ 
    let mode = match s with Some t -> t | None -> true in
    let depth = match depth with Some i -> i | None -> default_eauto_depth in
      fun gl -> 
	let gls = {it = [sig_it gl]; sigma = project gl} in
	let vals v = List.hd v in
	  try typeclasses_eauto d (mode, depth) [] (gls, vals) 
	  with Not_found -> tclFAIL 0 (str" typeclasses eauto failed") gl ]
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


