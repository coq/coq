(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id: eauto.ml4 10346 2007-12-05 21:11:19Z aspiwack $ *)

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

open Evd

(** Typeclasses instance search tactic / eauto *)

open Auto

let e_give_exact c gl = 
  let t1 = (pf_type_of gl c) and t2 = pf_concl gl in 
  if occur_existential t1 or occur_existential t2 then 
     tclTHEN (Clenvtac.unify t1) (exact_check c) gl
  else exact_check c gl

let assumption id = e_give_exact (mkVar id)

let unify_e_resolve  (c,clenv) gls = 
  let clenv' = connect_clenv gls clenv in
  let _ = clenv_unique_resolver false clenv' gls in
  h_simplest_eapply c gls


let rec e_trivial_fail_db db_list local_db goal =
  let tacl = 
    Eauto.registered_e_assumption ::
    (tclTHEN Tactics.intro 
       (function g'->
	  let d = pf_last_hyp g' in
	  let hintl = make_resolve_hyp (pf_env g') (project g') d in
          (e_trivial_fail_db db_list
	     (Hint_db.add_list hintl local_db) g'))) ::
    (List.map fst (e_trivial_resolve db_list local_db (pf_concl goal)) )
  in 
  tclFIRST (List.map tclCOMPLETE tacl) goal 

and e_my_find_search db_list local_db hdc concl = 
  let hdc = head_of_constr_reference hdc in
  let hintl =
    if occur_existential concl then
      list_map_append (Hint_db.map_all hdc) (local_db::db_list)
    else
      list_map_append (Hint_db.map_auto (hdc,concl)) (local_db::db_list)
  in 
  let tac_of_hint = 
    fun {pri=b; pat = p; code=t} -> 
      (b, 
       let tac =
	 match t with
	   | Res_pf (term,cl) -> unify_resolve (term,cl)
	   | ERes_pf (term,cl) -> unify_e_resolve (term,cl)
	   | Give_exact (c) -> e_give_exact c
	   | Res_pf_THEN_trivial_fail (term,cl) ->
               tclTHEN (unify_e_resolve (term,cl)) 
		 (e_trivial_fail_db db_list local_db)
	   | Unfold_nth c -> unfold_in_concl [[],c]
	   | Extern tacast -> conclPattern concl 
	       (Option.get p) tacast
       in 
       (tac,fmt_autotactic t))
  in 
    List.map tac_of_hint hintl

and e_trivial_resolve db_list local_db gl = 
  try 
    Auto.priority 
      (e_my_find_search db_list local_db 
	 (List.hd (head_constr_bound gl [])) gl)
  with Bound | Not_found -> []

let e_possible_resolve db_list local_db gl =
  try 
    List.map snd (e_my_find_search db_list local_db 
		       (List.hd (head_constr_bound gl [])) gl)
  with Bound | Not_found -> []

let find_first_goal gls = 
  try first_goal gls with UserError _ -> assert false


type search_state = { 
  depth : int; (*r depth of search before failing *)
  tacres : goal list sigma * validation;
  last_tactic : std_ppcmds;
  dblist : Auto.Hint_db.t list;
  localdb :  Auto.Hint_db.t list }
    
module SearchProblem = struct
    
  type state = search_state

  let debug = ref false

  let success s = (sig_it (fst s.tacres)) = []

  let pr_ev evs ev = Printer.pr_constr_env (Evd.evar_env ev) (Evarutil.nf_evar evs ev.Evd.evar_concl)
    
  let pr_goals gls =
    let evars = Evarutil.nf_evars (Refiner.project gls) in
      prlist (pr_ev evars) (sig_it gls)
	
  let filter_tactics (glls,v) l =
(*     let _ = Proof_trees.db_pr_goal (List.hd (sig_it glls)) in *)
(*     let evars = Evarutil.nf_evars (Refiner.project glls) in *)
(*     msg (str"Goal:" ++ pr_ev evars (List.hd (sig_it glls)) ++ str"\n"); *)
    let rec aux = function
      | [] -> []
      | (tac,pptac) :: tacl -> 
	  try 
	    let (lgls,ptl) = apply_tac_list tac glls in 
	    let v' p = v (ptl p) in
(*               if !debug then *)
(* 		begin *)
(* 		  let evars = Evarutil.nf_evars (Refiner.project glls) in *)
(* 	            msg (str"Goal:" ++ pr_ev evars (List.hd (sig_it glls)) ++ str"\n"); *)
(* 		    msg (hov 1 (pptac ++ str" gives: \n" ++ pr_goals lgls ++ str"\n")) *)
(* 		end; *)
	      ((lgls,v'),pptac) :: aux tacl
	  with e when Logic.catchable_exception e ->
	    aux tacl
    in aux l

  let nb_empty_evars s = 
    Evd.fold (fun ev evi acc -> if evi.evar_body = Evar_empty then succ acc else acc) s 0

  (* Ordering of states is lexicographic on depth (greatest first) then
     number of remaining goals. *)
  let compare s s' =
    let d = s'.depth - s.depth in
    let nbgoals s = 
      List.length (sig_it (fst s.tacres)) + 
	nb_empty_evars (sig_sig (fst s.tacres))
    in
      if d <> 0 then d else nbgoals s - nbgoals s'

  let branching s = 
    if s.depth = 0 then 
      []
    else      
      let lg = fst s.tacres in
      let nbgl = List.length (sig_it lg) in
      assert (nbgl > 0);
      let g = find_first_goal lg in
      let assumption_tacs = 
	let l = 
	  filter_tactics s.tacres
	    (List.map 
	       (fun id -> (Eauto.e_give_exact_constr (mkVar id),
			   (str "exact" ++ spc () ++ pr_id id)))
	       (pf_ids_of_hyps g))
	in
	List.map (fun (res,pp) -> { depth = s.depth; tacres = res;
				    last_tactic = pp; dblist = s.dblist;
				    localdb = List.tl s.localdb }) l
      in
      let intro_tac = 
	List.map 
	  (fun ((lgls,_) as res,pp) -> 
	     let g' = first_goal lgls in 
	     let hintl = 
	       make_resolve_hyp (pf_env g') (project g') (pf_last_hyp g')
	     in
	       
             let ldb = Hint_db.add_list hintl (match s.localdb with [] -> assert false | hd :: _ -> hd) in
	     { depth = s.depth; tacres = res; 
	       last_tactic = pp; dblist = s.dblist;
	       localdb = ldb :: List.tl s.localdb })
	  (filter_tactics s.tacres [Tactics.intro,(str "intro")])
      in
      let rec_tacs = 
	let l = 
	  filter_tactics s.tacres (e_possible_resolve s.dblist (List.hd s.localdb) (pf_concl g))
	in
	List.map 
	  (fun ((lgls,_) as res, pp) -> 
	     let nbgl' = List.length (sig_it lgls) in
	     if nbgl' < nbgl then
	       { depth = s.depth; tacres = res; last_tactic = pp;
		 dblist = s.dblist; localdb = List.tl s.localdb }
	     else 
	       { depth = pred s.depth; tacres = res; 
		 dblist = s.dblist; last_tactic = pp;
		 localdb = 
		   list_addn (nbgl'-nbgl) (match s.localdb with [] -> assert false | hd :: _ -> hd) s.localdb })
	  l
      in
      List.sort compare (assumption_tacs @ intro_tac @ rec_tacs)

  let pp s = 
    msg (hov 0 (str " depth=" ++ int s.depth ++ spc () ++ 
		  s.last_tactic ++ str "\n"))

end

module Search = Explore.Make(SearchProblem)

let make_initial_state n gls dblist localdbs =
  { depth = n;
    tacres = gls;
    last_tactic = (mt ());
    dblist = dblist;
    localdb = localdbs }

let e_depth_search debug p db_list local_dbs gls =
  try
    let tac = if debug then
      (SearchProblem.debug := true; Search.debug_depth_first) else Search.depth_first in
    let s = tac (make_initial_state p gls db_list local_dbs) in
    s.tacres
  with Not_found -> error "EAuto: depth first search failed"

let e_breadth_search debug n db_list local_dbs gls =
  try
    let tac = 
      if debug then Search.debug_breadth_first else Search.breadth_first 
    in
    let s = tac (make_initial_state n gls db_list local_dbs) in
    s.tacres
  with Not_found -> error "EAuto: breadth first search failed"

let e_search_auto debug (in_depth,p) lems db_list gls = 
  let sigma = Evd.sig_sig (fst gls) and gls' = Evd.sig_it (fst gls) in
  let local_dbs = List.map (fun gl -> make_local_hint_db lems ({it = gl; sigma = sigma})) gls' in
  if in_depth then 
    e_depth_search debug p db_list local_dbs gls
  else
    e_breadth_search debug p db_list local_dbs gls

let full_eauto debug n lems gls = 
  let dbnames = current_db_names () in
  let dbnames =  list_subtract dbnames ["v62"] in
  let db_list = List.map searchtable_map dbnames in
    e_search_auto debug n lems db_list gls

exception Found of evar_defs

let valid evm p res_sigma l = 
  let evd' =
    Evd.fold
      (fun ev evi (gls, sigma) ->
	if not (Evd.is_evar evm ev) then
	  match gls with
	      hd :: tl -> 
		if evi.evar_body = Evar_empty then
		  let cstr, obls = Refiner.extract_open_proof !res_sigma hd in
		    (tl, Evd.evar_define ev cstr sigma)
		else (tl, sigma)
	    | [] -> ([], sigma)
	else if not (Evd.is_defined evm ev) && p ev evi then
	  match gls with
	      hd :: tl -> 
		if evi.evar_body = Evar_empty then
		  let cstr, obls = Refiner.extract_open_proof !res_sigma hd in
		    (tl, Evd.evar_define ev cstr sigma)
		else (tl, sigma)
	    | [] -> assert(false)
	else (gls, sigma))
      !res_sigma (l, Evd.create_evar_defs !res_sigma)
  in raise (Found (snd evd'))

let refresh_evi evi = 
  { evi with 
(*     evar_hyps = Environ.map_named_val Termops.refresh_universes evi.evar_hyps ; *)
    evar_concl = Termops.refresh_universes evi.evar_concl }
    
let resolve_all_evars_once debug (mode, depth) env p evd =
  let evm = Evd.evars_of evd in
  let goals, evm = 
    Evd.fold
      (fun ev evi (gls, evm) ->
(* 	let evi = refresh_evi evi in *)
	  (if evi.evar_body = Evar_empty && p ev evi then evi :: gls else gls), 
	Evd.add evm ev evi)
      evm ([], Evd.empty)
  in
  let gls = { it = List.rev goals; sigma = evm } in
  let res_sigma = ref evm in
  let gls', valid' = full_eauto debug (mode, depth) [] (gls, valid evm p res_sigma) in
    res_sigma := Evarutil.nf_evars (sig_sig gls');
    try ignore(valid' []); assert(false) with Found evd' -> Evarutil.nf_evar_defs evd'

exception FoundTerm of constr

let resolve_one_typeclass env gl =
  let gls = { it = [ Evd.make_evar (Environ.named_context_val env) gl ] ; sigma = Evd.empty } in
  let valid x = raise (FoundTerm (fst (Refiner.extract_open_proof Evd.empty (List.hd x)))) in
  let gls', valid' = full_eauto false (true, 15) [] (gls, valid) in
    try ignore(valid' []); assert false with FoundTerm t -> t

let has_undefined p evd =
  Evd.fold (fun ev evi has -> has ||
    (evi.evar_body = Evar_empty && p ev evi))
    (Evd.evars_of evd) false
    
let rec resolve_all_evars debug m env p evd =
  let rec aux n evd = 
    if has_undefined p evd && n > 0 then
      let evd' = resolve_all_evars_once debug m env p evd in
	aux (pred n) evd'
    else evd
  in aux 3 evd

(** Typeclass-based rewriting. *)

let morphism_class = lazy (class_info (id_of_string "Morphism"))

let get_respect cl = 
  Option.get (List.hd (Recordops.lookup_projections cl.cl_impl))

let respect_proj = lazy (get_respect (Lazy.force morphism_class))

let gen_constant dir s = Coqlib.gen_constant "Class_setoid" dir s
let coq_proj1 = lazy(gen_constant ["Init"; "Logic"] "proj1")
let coq_proj2 = lazy(gen_constant ["Init"; "Logic"] "proj2")
let iff = lazy (gen_constant ["Init"; "Logic"] "iff")
let impl = lazy (gen_constant ["Program"; "Basics"] "impl")
let arrow = lazy (gen_constant ["Program"; "Basics"] "arrow")
let coq_id = lazy (gen_constant ["Program"; "Basics"] "id")

let reflexive_type = lazy (gen_constant ["Classes"; "Relations"] "Reflexive")
let reflexive_proof = lazy (gen_constant ["Classes"; "Relations"] "reflexive")

let symmetric_type = lazy (gen_constant ["Classes"; "Relations"] "Symmetric")
let symmetric_proof = lazy (gen_constant ["Classes"; "Relations"] "symmetric")

let transitive_type = lazy (gen_constant ["Classes"; "Relations"] "Transitive")
let transitive_proof = lazy (gen_constant ["Classes"; "Relations"] "transitive")

let inverse = lazy (gen_constant ["Classes"; "Relations"] "inverse")

let respectful_dep = lazy (gen_constant ["Classes"; "Morphisms"] "respectful_dep")
let respectful = lazy (gen_constant ["Classes"; "Morphisms"] "respectful")

let equivalence = lazy (gen_constant ["Classes"; "Relations"] "Equivalence")
let default_relation = lazy (gen_constant ["Classes"; "Relations"] "DefaultRelation")

let iff_equiv = lazy (gen_constant ["Classes"; "Relations"] "iff_equivalence")
let eq_equiv = lazy (gen_constant ["Classes"; "SetoidClass"] "eq_equivalence")

(* let coq_relation = lazy (gen_constant ["Relations";"Relation_Definitions"] "relation") *)
(* let coq_relation = lazy (gen_constant ["Classes";"Relations"] "relation") *)
let coq_relation a = mkProd (Anonymous, a, mkProd (Anonymous, a, mkProp))
let coq_relationT = lazy (gen_constant ["Classes";"Relations"] "relationT")

let setoid_refl_proj = lazy (gen_constant ["Classes"; "SetoidClass"] "equiv_refl")

let iff_setoid = lazy (gen_constant ["Classes"; "SetoidClass"] "iff_setoid")
let eq_setoid = lazy (gen_constant ["Classes"; "SetoidClass"] "eq_setoid")

let setoid_equiv = lazy (gen_constant ["Classes"; "SetoidClass"] "equiv")
let setoid_morphism = lazy (gen_constant ["Classes"; "SetoidClass"] "setoid_morphism")
let setoid_refl_proj = lazy (gen_constant ["Classes"; "SetoidClass"] "equiv_refl")
  
let arrow_morphism a b = 
  if isprop a && isprop b then
    Lazy.force impl
  else
    mkLambda (Name (id_of_string "A"), a, 
	     mkLambda (Name (id_of_string "B"), b, 
		      mkProd (Anonymous, mkRel 2, mkRel 2)))
    
let setoid_refl pars x = 
  applistc (Lazy.force setoid_refl_proj) (pars @ [x])
      
let morphism_class_proj = lazy (Lazy.force morphism_class, Lazy.force respect_proj)

exception Found of (constr * constr * (types * types) list * constr * constr array *
		       (constr * (constr * constr * constr * constr)) option array)

let is_equiv env sigma t = 
  isConst t && Reductionops.is_conv env sigma (Lazy.force setoid_equiv) t

let split_head = function
    hd :: tl -> hd, tl
  | [] -> assert(false)

let build_signature isevars env m (cstrs : 'a option list) (f : 'a -> constr) =
  let new_evar isevars env t =
    Evarutil.e_new_evar isevars env
      (* ~src:(dummy_loc, ImplicitArg (ConstRef (Lazy.force respectful), (n, Some na))) *) t
  in
  let mk_relty ty obj =
    match obj with
      | None -> 
	  let relty = coq_relation ty in
	    new_evar isevars env relty
      | Some x -> f x
  in
  let rec aux t l =
    let t = Reductionops.whd_betadelta env (Evd.evars_of !isevars) t in
    match kind_of_term t, l with
      | Prod (na, ty, b), obj :: cstrs -> 
	  let (arg, evars) = aux b cstrs in
	  let relty = mk_relty ty obj in
	  let arg' = mkApp (Lazy.force respectful, [| ty ; relty ; b ; arg |]) in
	    arg', (ty, relty) :: evars
      | _, [finalcstr] -> 
	  (match finalcstr with
	      None -> 
		let rel = mk_relty t None in 
		  rel, [t, rel]
	    | Some (t, rel) -> rel, [t, rel])
      | _, _ -> assert false
  in aux m cstrs

let reflexivity_proof_evar env evars carrier relation x =
  let goal =
    mkApp (Lazy.force reflexive_type, [| carrier ; relation |])
  in
  let inst = Evarutil.e_new_evar evars env goal in
    (* try resolve_one_typeclass env goal *)
    mkApp (Lazy.force reflexive_proof, [| carrier ; relation ; inst ; x |])
    (*     with Not_found -> *)
(*       let meta = Evarutil.new_meta() in *)
(* 	mkCast (mkMeta meta, DEFAULTcast, mkApp (relation, [| x; x |])) *)

let find_class_proof proof_type proof_method env carrier relation =
  let goal =
    mkApp (Lazy.force proof_type, [| carrier ; relation |])
  in
    try 
      let inst = resolve_one_typeclass env goal in
	mkApp (Lazy.force proof_method, [| carrier ; relation ; inst |])
    with e when Logic.catchable_exception e -> raise Not_found

let reflexive_proof env = find_class_proof reflexive_type reflexive_proof env
let symmetric_proof env = find_class_proof symmetric_type symmetric_proof env
let transitive_proof env = find_class_proof transitive_type transitive_proof env

let resolve_morphism env sigma oldt m args args' cstr evars =
  let (morphism_cl, morphism_proj) = Lazy.force morphism_class_proj in
  let morph_instance, proj, sigargs, m', args, args' = 
(*     if is_equiv env sigma m then  *)
(*       let params, rest = array_chop 3 args in *)
(*       let a, r, s = params.(0), params.(1), params.(2) in *)
(*       let params', rest' = array_chop 3 args' in *)
(*       let inst = mkApp (Lazy.force setoid_morphism, params) in *)
(* 	(* Equiv gives a binary morphism *) *)
(*       let (cl, proj) = Lazy.force class_two in *)
(*       let ctxargs = [ a; r; s; a; r; s; mkProp; Lazy.force iff; Lazy.force iff_setoid; ] in *)
(*       let m' = mkApp (m, [| a; r; s |]) in *)
(* 	inst, proj, ctxargs, m', rest, rest' *)
(*     else *)
    let first = 
      let first = ref (-1) in
	for i = 0 to Array.length args' - 1 do
	  if !first = -1 && args'.(i) <> None then first := i
	done;
	!first
    in
    let morphargs, morphobjs = array_chop first args in
    let morphargs', morphobjs' = array_chop first args' in
    let appm = mkApp(m, morphargs) in
    let appmtype = Typing.type_of env sigma appm in
    let cstrs = List.map (function None -> None | Some (_, (a, r, _, _)) -> Some (a, r)) (Array.to_list morphobjs') in
    let signature, sigargs = build_signature evars env appmtype (cstrs @ [cstr]) (fun (a, r) -> r) in
    let cl_args = [| appmtype ; signature ; appm |] in
    let app = mkApp (mkInd morphism_cl.cl_impl, cl_args) in
    let morph = Evarutil.e_new_evar evars env app in
    let proj = 
      mkApp (mkConst morphism_proj, 
	    Array.append cl_args [|morph|])
    in
      morph, proj, sigargs, appm, morphobjs, morphobjs'
  in 
  let projargs, respars, typeargs = 
    array_fold_left2 
      (fun (acc, sigargs, typeargs') x y -> 
	let (carrier, relation), sigargs = split_head sigargs in
	  match y with
	      None ->
		let refl_proof = reflexivity_proof_evar env evars carrier relation x in
		  [ refl_proof ; x ; x ] @ acc, sigargs, x :: typeargs'
	    | Some (p, (_, _, _, t')) ->
		[ p ; t'; x ] @ acc, sigargs, t' :: typeargs')
      ([], sigargs, []) args args'
  in
  let proof = applistc proj (List.rev projargs) in
  let newt = applistc m' (List.rev typeargs) in
    match respars with
	[ a, r ] -> (proof, (a, r, oldt, newt))
      | _ -> assert(false)

(* Adapted from setoid_replace. *)

type hypinfo = {
  cl : clausenv;
  prf : constr;
  rel : constr;
  l2r : bool;
  c1 : constr;
  c2 : constr;
  c  : constr option;
  abs : (constr * types) option;
}

let decompose_setoid_eqhyp gl c left2right =
  let ctype = pf_type_of gl c in
  let eqclause  = Clenv.make_clenv_binding gl (c,ctype) Rawterm.NoBindings in
  let (equiv, args) = decompose_app (Clenv.clenv_type eqclause) in
  let rec split_last_two = function
    | [c1;c2] -> [],(c1, c2)
    | x::y::z ->
	let l,res = split_last_two (y::z) in x::l, res
    | _ -> error "The term provided is not an applied relation" in
  let others, (c1,c2) = split_last_two args in
    { cl=eqclause; prf=(Clenv.clenv_value eqclause);
      rel=mkApp (equiv, Array.of_list others);
      l2r=left2right; c1=c1; c2=c2; c=Some c; abs=None }

let rewrite_unif_flags = {
  Unification.modulo_conv_on_closed_terms = false;
  Unification.use_metas_eagerly = true;
  Unification.modulo_conv = false
}

let rewrite2_unif_flags = {
  Unification.modulo_conv_on_closed_terms = true;
  Unification.use_metas_eagerly = true;
  Unification.modulo_conv = false
 }

(* let unification_rewrite c1 c2 cl but gl =  *)
(*   let (env',c1) = *)
(*     try *)
(*       (\* ~flags:(false,true) to allow to mark occurences that must not be *)
(*          rewritten simply by replacing them with let-defined definitions *)
(*          in the context *\) *)
(*       w_unify_to_subterm ~flags:rewrite_unif_flags (pf_env gl) (c1,but) cl.evd *)
(*     with *)
(* 	Pretype_errors.PretypeError _ -> *)
(* 	  (\* ~flags:(true,true) to make Ring work (since it really *)
(*              exploits conversion) *\) *)
(* 	  w_unify_to_subterm ~flags:rewrite2_unif_flags *)
(* 	    (pf_env gl) (c1,but) cl.evd *)
(*   in *)
(*   let cl' = {cl with evd = env' } in *)
(*   let c2 = Clenv.clenv_nf_meta cl' c2 in *)
(*   check_evar_map_of_evars_defs env' ; *)
(*   env',Clenv.clenv_value cl', c1, c2 *)

let allowK = true

let unify_eqn gl hypinfo t = 
  try 
    let {cl=cl; prf=prf; rel=rel; l2r=l2r; c1=c1; c2=c2; c=c; abs=abs} = !hypinfo in
    let env' = 
      try clenv_unify allowK ~flags:rewrite_unif_flags
	CONV (if l2r then c1 else c2) t cl
      with Pretype_errors.PretypeError _ -> (* For Ring essentially *)
	clenv_unify allowK ~flags:rewrite2_unif_flags
	  CONV (if l2r then c1 else c2) t cl
    in
    let c1 = Clenv.clenv_nf_meta env' c1 
    and c2 = Clenv.clenv_nf_meta env' c2
    and rel = Clenv.clenv_nf_meta env' rel in
    let car = pf_type_of gl c1 in
    let prf =
      if abs = None then
(* 	let (rel, args) = destApp typ in *)
(* 	let relargs, args = array_chop (Array.length args - 2) args in *)
(* 	let rel = mkApp (rel, relargs) in *)
	let prf = Clenv.clenv_value env' in
	  begin
	    match c with 
	      | Some c when occur_meta prf ->
		  (* Refresh the clausenv to not get the same meta twice in the goal. *)
		  hypinfo := decompose_setoid_eqhyp gl c l2r;
	      | _ -> ()
	  end;
	  prf
      else prf
    in
    let res =
      if l2r then (prf, (car, rel, c1, c2))
      else
	try (mkApp (symmetric_proof (pf_env gl) car rel, [| c1 ; c2 ; prf |]), (car, rel, c2, c1))
	with Not_found ->
	  (prf, (car, mkApp (Lazy.force inverse, [| car ; rel |]), c2, c1))
    in Some (env', res)
  with _ -> None

let unfold_impl t = 
  match kind_of_term t with
    | App (arrow, [| a; b |]) when eq_constr arrow (Lazy.force impl) -> 
	mkProd (Anonymous, a, b)
    | _ -> t

let build_new gl env sigma occs hypinfo concl cstr evars =
  let is_occ occ = occs = [] || List.mem occ occs in
  let rec aux t occ cstr =
    match unify_eqn gl hypinfo t with
      | Some (env', (prf, hypinfo as x)) ->
	  if is_occ occ then (
	    evars := Evd.evar_merge !evars (Evd.evars_of (Evd.undefined_evars env'.evd));
	    match cstr with
		None -> Some x, succ occ
	      | Some _ ->
		  let (car, r, orig, dest) = hypinfo in
		  let res = 
		    try 
		      Some (resolve_morphism env sigma t 
			       (mkLambda (Name (id_of_string "x"), car, mkRel 1))
			       (* (Termops.refresh_universes (mkApp (Lazy.force coq_id, [| car |]))) *)
			       [| orig |] [| Some x |] cstr evars)
		    with Not_found -> None
		  in res, succ occ)
	  else None, succ occ
      | None -> 
	  match kind_of_term t with
	    | App (m, args) ->
		let args', occ = 
		  Array.fold_left 
		    (fun (acc, occ) arg -> let res, occ = aux arg occ None in (res :: acc, occ))
		    ([], occ) args
		in
		let res =
		  if List.for_all (fun x -> x = None) args' then None
		  else 
		    let args' = Array.of_list (List.rev args') in
		      (try Some (resolve_morphism env sigma t m args args' cstr evars)
			with Not_found -> None)
		in res, occ
		  
	    | Prod (_, x, b) -> 
		let x', occ = aux x occ None in
		let b', occ = aux b occ None in
		let res = 
		  if x' = None && b' = None then None
		  else 
		    (try 
			let (proof, (a, r, oldt, newt)) = 
			  resolve_morphism env sigma t
			    (arrow_morphism (pf_type_of gl x) (pf_type_of gl b)) [| x ; b |] [| x' ; b' |]
			    cstr evars
			in
			let newt' = unfold_impl newt in
			  Some (proof, (a, r, oldt, newt'))
		      with Not_found -> None)
		in res, occ
		  
	    | _ -> None, occ
  in aux concl 1 cstr
    
let resolve_all_typeclasses env evd = 
  resolve_all_evars false (true, 15) env
    (fun ev evi -> Typeclasses.class_of_constr evi.Evd.evar_concl <> None) evd

let cl_rewrite_clause_aux hypinfo goal_meta occs clause gl =
  let concl, is_hyp = 
    match clause with
	Some ((_, id), _) -> pf_get_hyp_typ gl id, Some id
      | None -> pf_concl gl, None
  in
  let cstr = 
    match is_hyp with
	None -> (mkProp, mkApp (Lazy.force inverse, [| mkProp; Lazy.force impl |]))
      | Some _ -> (mkProp, Lazy.force impl)
  in
  let evars = ref (Evd.create_evar_defs Evd.empty) in
  let env = pf_env gl in
  let sigma = project gl in
  let eq, _ = build_new gl env sigma occs hypinfo concl (Some cstr) evars in
    match eq with  
	Some (p, (_, _, oldt, newt)) -> 
	  (try 
	      evars := Typeclasses.resolve_typeclasses env (Evd.evars_of !evars) !evars;
	      let p = Evarutil.nf_isevar !evars p in
	      let newt = Evarutil.nf_isevar !evars newt in
	      let undef = Evd.undefined_evars !evars in
	      let rewtac = 
		match is_hyp with
		  | Some id -> 
		      let term = 
			match !hypinfo.abs with
			    None -> p
			  | Some (t, ty) -> 
			      mkApp (mkLambda (Name (id_of_string "lemma"), ty, p), [| t |])
		      in
			cut_replacing id newt 
			  (fun x -> Tactics.refine (mkApp (term, [| mkVar id |])))
		  | None -> 
		      (match !hypinfo.abs with
			  None -> 
			    let name = next_name_away_with_default "H" Anonymous (pf_ids_of_hyps gl) in
			      tclTHENLAST
				(Tacmach.internal_cut_no_check name newt)
				(tclTHEN (Tactics.revert [name]) (Tactics.refine p))
			| Some (t, ty) -> 
			    Tactics.refine
			      (mkApp (mkLambda (Name (id_of_string "newt"), newt,
					       mkLambda (Name (id_of_string "lemma"), ty,
							mkApp (p, [| mkRel 2 |]))),
				     [| mkMeta goal_meta; t |])))
	      in
	      let evartac = 
		let evd = Evd.evars_of undef in
		  if not (evd = Evd.empty) then Refiner.tclEVARS (Evd.merge sigma evd)
		  else tclIDTAC
	      in tclTHENLIST [evartac; rewtac] gl
	    with UserError (env, e) -> 
	      tclFAIL 0 (str" setoid rewrite failed: unable to satisfy the rewriting constraints") gl)
      | None -> 
	  let {l2r=l2r; c1=x; c2=y} = !hypinfo in
	    raise (Pretype_errors.PretypeError (pf_env gl, Pretype_errors.NoOccurrenceFound (if l2r then x else y)))
	      (* tclFAIL 1 (str"setoid rewrite failed") gl *)
	  
let cl_rewrite_clause c left2right occs clause gl =
  let meta = Evarutil.new_meta() in
  let hypinfo = ref (decompose_setoid_eqhyp gl c left2right) in
    cl_rewrite_clause_aux hypinfo meta occs clause gl

open Genarg
open Extraargs

TACTIC EXTEND class_rewrite
| [ "clrewrite" orient(o) constr(c) "in" hyp(id) "at" occurences(occ) ] -> [ cl_rewrite_clause c o occ (Some (([],id), [])) ]
| [ "clrewrite" orient(o) constr(c) "at" occurences(occ) "in" hyp(id) ] -> [ cl_rewrite_clause c o occ (Some (([],id), [])) ]
| [ "clrewrite" orient(o) constr(c) "in" hyp(id) ] -> [ cl_rewrite_clause c o [] (Some (([],id), [])) ]
| [ "clrewrite" orient(o) constr(c) "at" occurences(occ) ] -> [ cl_rewrite_clause c o occ None ]
| [ "clrewrite" orient(o) constr(c) ] -> [ cl_rewrite_clause c o [] None ]
END


let clsubstitute o c =
  let is_tac id = match kind_of_term c with Var id' when id' = id -> true | _ -> false in
    Tacticals.onAllClauses 
      (fun cl -> 
	match cl with
	  | Some ((_,id),_) when is_tac id -> tclIDTAC
	  | _ -> cl_rewrite_clause c o [] cl)

TACTIC EXTEND map_tac
| [ "clsubstitute" orient(o) constr(c) ] -> [ clsubstitute o c ]
END

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

let resolve_argument_typeclasses d p env evd onlyargs all =
  let pred = 
    if onlyargs then 
      (fun ev evi -> Typeclasses.is_implicit_arg (snd (Evd.evar_source ev evd)) &&
	class_of_constr evi.Evd.evar_concl <> None)
    else
      (fun ev evi -> class_of_constr evi.Evd.evar_concl <> None)
  in
    try 
      resolve_all_evars d p env pred evd
    with e -> 
      if all then raise e else evd
	
VERNAC COMMAND EXTEND Typeclasses_Settings
| [ "Typeclasses" "eauto" ":=" debug(d) search_mode(s) depth(depth) ] -> [ 
    let mode = match s with Some t -> t | None -> true in
    let depth = match depth with Some i -> i | None -> 15 in
      Typeclasses.solve_instanciations_problem :=
	resolve_argument_typeclasses d (mode, depth) ]
END

let _ = 
  Typeclasses.solve_instanciations_problem :=
    resolve_argument_typeclasses false (true, 15)

TACTIC EXTEND typeclasses_eauto
| [ "typeclasses" "eauto" debug(d) search_mode(s) depth(depth) ] -> [ fun gl ->
    let env = pf_env gl in
    let sigma = project gl in
      if Evd.dom sigma = [] then Refiner.tclIDTAC gl
      else
	let evd = Evd.create_evar_defs sigma in
	let mode = match s with Some t -> t | None -> true in
	let depth = match depth with Some i -> i | None -> 15 in
	let evd' = resolve_argument_typeclasses d (mode, depth) env evd false false in
	  Refiner.tclEVARS (Evd.evars_of evd') gl ]
END

let _ = 
  Classes.refine_ref := Refine.refine

(* Compatibility with old Setoids *)
  
TACTIC EXTEND setoid_rewrite
   [ "setoid_rewrite" orient(o) constr(c) ]
   -> [ cl_rewrite_clause c o [] None ]
 | [ "setoid_rewrite" orient(o) constr(c) "in" hyp(id) ] ->
      [ cl_rewrite_clause c o [] (Some (([],id), []))]
 | [ "setoid_rewrite" orient(o) constr(c) "at" occurences(occ) ] ->
      [ cl_rewrite_clause c o occ None]
 | [ "setoid_rewrite" orient(o) constr(c) "at" occurences(occ) "in" hyp(id)] ->
      [ cl_rewrite_clause c o occ (Some (([],id), []))]
 | [ "setoid_rewrite" orient(o) constr(c) "in" hyp(id) "at" occurences(occ)] ->
      [ cl_rewrite_clause c o occ (Some (([],id), []))]
END

(* let solve_obligation lemma =  *)
(*   tclTHEN (Tacinterp.interp (Tacexpr.TacAtom (dummy_loc, Tacexpr.TacAnyConstructor None))) *)
(*     (eapply_with_bindings (Constrintern.interp_constr Evd.empty (Global.env()) lemma, NoBindings)) *)
    
let mkappc s l = CAppExpl (dummy_loc,(None,(Libnames.Ident (dummy_loc,id_of_string s))),l)

let declare_instance a aeq n s = ((dummy_loc,Name n),Explicit,
				  CApp (dummy_loc, (None, mkIdentC (id_of_string s)), 
					[(a,None);(aeq,None)]))

let anew_instance instance fields = new_instance [] instance fields None (fun _ -> ())

let require_library dirpath =
  let qualid = (dummy_loc, Libnames.qualid_of_dirpath (Libnames.dirpath_of_string dirpath)) in
    Library.require_library [qualid] (Some false)

let check_required_library d =
  let d' = List.map id_of_string d in
  let dir = make_dirpath (List.rev d') in
  if not (Library.library_is_opened dir) then
    error ("Library "^(list_last d)^" has to be required first")

let init_setoid () =
  check_required_library ["Coq";"Setoids";"Setoid"]

let declare_instance_refl a aeq n lemma = 
  let instance = declare_instance a aeq (add_suffix n "_refl") "Reflexive" 
  in anew_instance instance 
       [((dummy_loc,id_of_string "reflexive"),[],lemma)]

let declare_instance_sym a aeq n lemma = 
  let instance = declare_instance a aeq (add_suffix n "_sym") "Symmetric" 
  in anew_instance instance 
       [((dummy_loc,id_of_string "symmetric"),[],lemma)]

let declare_instance_trans a aeq n lemma = 
  let instance = declare_instance a aeq (add_suffix n "_trans") "Transitive" 
  in anew_instance instance 
       [((dummy_loc,id_of_string "transitive"),[],lemma)]

let constr_tac = Tacinterp.interp (Tacexpr.TacAtom (dummy_loc, Tacexpr.TacAnyConstructor None)) 

let declare_relation a aeq n refl symm trans = 
  init_setoid ();
  match (refl,symm,trans) with 
      (None, None, None) -> 
	let instance = declare_instance a aeq n "DefaultRelation" 
	in ignore(anew_instance instance [])
    | (Some lemma1, None, None) -> 
	ignore (declare_instance_refl a aeq n lemma1)
    | (None, Some lemma2, None) -> 
	ignore (declare_instance_sym a aeq n lemma2)
    | (None, None, Some lemma3) -> 
	ignore (declare_instance_trans a aeq n lemma3)
    | (Some lemma1, Some lemma2, None) -> 
	ignore (declare_instance_refl a aeq n lemma1); 
	ignore (declare_instance_sym a aeq n lemma2)
    | (Some lemma1, None, Some lemma3) -> 
	let lemma_refl = declare_instance_refl a aeq n lemma1 in
	let lemma_trans = declare_instance_trans a aeq n lemma3 in
	let instance = declare_instance a aeq n "PreOrder" 
	in ignore(
	    anew_instance instance 
	      [((dummy_loc,id_of_string "preorder_refl"), [], mkIdentC lemma_refl);
	       ((dummy_loc,id_of_string "preorder_trans"),[], mkIdentC lemma_trans)])
    | (None, Some lemma2, Some lemma3) -> 
	let lemma_sym = declare_instance_sym a aeq n lemma2 in
	let lemma_trans = declare_instance_trans a aeq n lemma3 in
	let instance = declare_instance a aeq n "PER" 
	in ignore(
	    anew_instance instance 
	      [((dummy_loc,id_of_string "per_sym"),  [], mkIdentC lemma_sym);
	       ((dummy_loc,id_of_string "per_trans"),[], mkIdentC lemma_trans)])
     | (Some lemma1, Some lemma2, Some lemma3) -> 
	let lemma_refl = declare_instance_refl a aeq n lemma1 in 
	let lemma_sym = declare_instance_sym a aeq n lemma2 in
	let lemma_trans = declare_instance_trans a aeq n lemma3 in
	let instance = declare_instance a aeq n "Equivalence" 
	in ignore(
	    anew_instance instance 
	      [((dummy_loc,id_of_string "equiv_refl"), [], mkIdentC lemma_refl);
	       ((dummy_loc,id_of_string "equiv_sym"),  [], mkIdentC lemma_sym);
	       ((dummy_loc,id_of_string "equiv_trans"),[], mkIdentC lemma_trans)])

VERNAC COMMAND EXTEND AddRelation
    [ "Add" "Relation" constr(a) constr(aeq) "reflexivity" "proved" "by" constr(lemma1) 
	"symmetry" "proved" "by" constr(lemma2) "as" ident(n) ] ->
      [ declare_relation a aeq n (Some lemma1) (Some lemma2) None ]
  | [ "Add" "Relation" constr(a) constr(aeq) "reflexivity" "proved" "by" constr(lemma1)  
	"as" ident(n) ] ->
      [ declare_relation a aeq n (Some lemma1) None None ]
  | [ "Add" "Relation" constr(a) constr(aeq)  "as" ident(n) ] -> 
      [ declare_relation a aeq n None None None ]
END

VERNAC COMMAND EXTEND AddRelation2
    [ "Add" "Relation" constr(a) constr(aeq) "symmetry" "proved" "by" constr(lemma2) 
      "as" ident(n) ] ->
      [ declare_relation a aeq n None (Some lemma2) None ]
  | [ "Add" "Relation" constr(a) constr(aeq) "symmetry" "proved" "by" constr(lemma2) "transitivity" "proved" "by" constr(lemma3)  "as" ident(n) ] ->
      [ declare_relation a aeq n None (Some lemma2) (Some lemma3) ]
END

VERNAC COMMAND EXTEND AddRelation3
    [ "Add" "Relation" constr(a) constr(aeq) "reflexivity" "proved" "by" constr(lemma1) 
      "transitivity" "proved" "by" constr(lemma3) "as" ident(n) ] ->
      [ declare_relation a aeq n (Some lemma1) None (Some lemma3) ]
  | [ "Add" "Relation" constr(a) constr(aeq) "reflexivity" "proved" "by" constr(lemma1) 
      "symmetry" "proved" "by" constr(lemma2) "transitivity" "proved" "by" constr(lemma3) 
      "as" ident(n) ] ->
      [ declare_relation a aeq n (Some lemma1) (Some lemma2) (Some lemma3) ] 
  | [ "Add" "Relation" constr(a) constr(aeq) "transitivity" "proved" "by" constr(lemma3)
	"as" ident(n) ] ->  
      [ declare_relation a aeq n None None (Some lemma3) ] 
END

let mk_qualid s =
  Libnames.Qualid (dummy_loc, Libnames.qualid_of_string s)

let cHole = CHole (dummy_loc, None)

open Entries
open Libnames

let respect_projection r ty =
  let ctx, inst = Sign.decompose_prod_assum ty in
  let mor, args = destApp inst in
  let instarg = mkApp (r, rel_vect 0 (List.length ctx)) in
  let app = mkApp (mkConst (Lazy.force respect_proj), 
		  Array.append args [| instarg |]) in
    it_mkLambda_or_LetIn app ctx
      
let declare_projection n instance_id r =
  let ty = Global.type_of_global r in
  let c = constr_of_global r in
  let term = respect_projection c ty in
  let typ = Typing.type_of (Global.env ()) Evd.empty term in
  let typ =
    let n = 
      let rec aux t = 
	match kind_of_term t with
	    App (f, [| a ; rel; a'; rel' |]) when eq_constr f (Lazy.force respectful) -> 
	      succ (aux rel')
	  | _ -> 0
      in
      let init = 
	match kind_of_term typ with
	    App (f, args) when eq_constr f (Lazy.force respectful) -> 
	      mkApp (f, fst (array_chop (Array.length args - 2) args))
	  | _ -> typ
      in aux init
    in
    let ctx,ccl = Reductionops.decomp_n_prod (Global.env()) Evd.empty (3 * n) typ
    in it_mkProd_or_LetIn ccl ctx 
  in
  let cst = 
    { const_entry_body = term;
      const_entry_type = Some typ;
      const_entry_opaque = false;
      const_entry_boxed = false }
  in
    ignore(Declare.declare_constant n (Entries.DefinitionEntry cst, Decl_kinds.IsDefinition Decl_kinds.Definition))
          
let build_morphism_signature m =
  let env = Global.env () in
  let m = Constrintern.interp_constr Evd.empty env m in
  let t = Typing.type_of env Evd.empty m in
  let isevars = ref (Evd.create_evar_defs Evd.empty) in
  let cstrs = 
    let rec aux t = 
      match kind_of_term t with
	| Prod (na, a, b) -> 
	    None :: aux b
	| _ -> [None]
    in aux t
  in
  let sig_, evars = build_signature isevars env t cstrs snd in
  let _ = List.iter 
    (fun (ty, rel) -> 
      let default = mkApp (Lazy.force default_relation, [| ty; rel |]) in
	ignore(Evarutil.e_new_evar isevars env default))
    evars
  in
  let morph = 
    mkApp (mkInd (Lazy.force morphism_class).cl_impl, [| t; sig_; m |])
  in
  let evd = resolve_all_evars_once false (true, 15) env
    (fun x evi -> class_of_constr evi.Evd.evar_concl <> None) !isevars in
    Evarutil.nf_isevar evd morph

let default_morphism sign m =
  let env = Global.env () in
  let isevars = ref (Evd.create_evar_defs Evd.empty) in
  let t = Typing.type_of env Evd.empty m in
  let sign, evars = 
    build_signature isevars env t sign (fun (ty, rel) -> rel)
  in
  let morph = 
    mkApp (mkInd (Lazy.force morphism_class).cl_impl, [| t; sign; m |])
  in
  let mor = resolve_one_typeclass env morph in
    mor, respect_projection mor morph
    	  
let unfold_respectful = lazy (Tactics.unfold_in_concl [[], EvalConstRef (destConst (Lazy.force respectful))])

VERNAC COMMAND EXTEND AddSetoid1
   [ "Add" "Setoid" constr(a) constr(aeq) constr(t) "as" ident(n) ] ->
     [	init_setoid ();
	let lemma_refl = declare_instance_refl a aeq n (mkappc "Seq_refl" [a;aeq;t]) in 
	let lemma_sym = declare_instance_sym a aeq n (mkappc "Seq_sym" [a;aeq;t]) in
	let lemma_trans = declare_instance_trans a aeq n (mkappc "Seq_trans" [a;aeq;t])  in
	let instance = declare_instance a aeq n "Equivalence"
	in ignore(
	    anew_instance instance
	      [((dummy_loc,id_of_string "equiv_refl"), [], mkIdentC lemma_refl);
	       ((dummy_loc,id_of_string "equiv_sym"),  [], mkIdentC lemma_sym);
	       ((dummy_loc,id_of_string "equiv_trans"),[], mkIdentC lemma_trans)])]
  | [ "Add" "Morphism" constr(m) ":" ident(n) ] ->
      [ init_setoid ();
	let instance_id = add_suffix n "_Morphism" in
	let instance = build_morphism_signature m in
	  if Lib.is_modtype () then 
	    let cst = Declare.declare_internal_constant instance_id
	      (Entries.ParameterEntry (instance,false), Decl_kinds.IsAssumption Decl_kinds.Logical)
	    in
	      add_instance { is_class = Lazy.force morphism_class ; is_pri = None; is_impl = cst };
	      declare_projection n instance_id (ConstRef cst)
	  else
	    let kind = Decl_kinds.Global, Decl_kinds.DefinitionBody Decl_kinds.Instance in
	      Flags.silently 
		(fun () ->
		  Command.start_proof instance_id kind instance 
		    (fun _ -> function
			Libnames.ConstRef cst -> 
			  add_instance { is_class = Lazy.force morphism_class ; is_pri = None; is_impl = cst };
			  declare_projection n instance_id (ConstRef cst)
		      | _ -> assert false);
		  Pfedit.by (Tacinterp.interp <:tactic<add_morphism_tactic>>)) ();
	      Flags.if_verbose (fun x -> msg (Printer.pr_open_subgoals x)) () ]

  | [ "Add" "Morphism" constr(m) "with" "signature" lconstr(s) "as" ident(n) ] ->
      [ init_setoid ();
	let instance_id = add_suffix n "_Morphism" in
	let instance = 
	  ((dummy_loc,Name instance_id), Implicit,
	  CApp (dummy_loc, (None, mkRefC 
	    (Qualid (dummy_loc, Libnames.qualid_of_string "Coq.Classes.Morphisms.Morphism"))), 
	       [(s,None);(m,None)]))
	in
	  if Lib.is_modtype () then (context ~hook:(fun r -> declare_projection n instance_id r) [ instance ])
	  else (
	    Flags.silently 
	      (fun () ->
		ignore(new_instance [] instance [] None (fun cst -> declare_projection n instance_id (ConstRef cst)));
		Pfedit.by (Tacinterp.interp <:tactic<add_morphism_tactic>>)) ();
	    Flags.if_verbose (fun x -> msg (Printer.pr_open_subgoals x)) ())
      ]
END

(** Bind to "rewrite" too *)

(** Taken from original setoid_replace, to emulate the old rewrite semantics where
    lemmas are first instantiated once and then rewrite proceeds. *)

let check_evar_map_of_evars_defs evd =
 let metas = Evd.meta_list evd in
 let check_freemetas_is_empty rebus =
  Evd.Metaset.iter
   (fun m ->
     if Evd.meta_defined evd m then () else
      raise (Logic.RefinerError (Logic.OccurMetaGoal rebus)))
 in
  List.iter
   (fun (_,binding) ->
     match binding with
        Evd.Cltyp (_,{Evd.rebus=rebus; Evd.freemetas=freemetas}) ->
         check_freemetas_is_empty rebus freemetas
      | Evd.Clval (_,({Evd.rebus=rebus1; Evd.freemetas=freemetas1},_),
                 {Evd.rebus=rebus2; Evd.freemetas=freemetas2}) ->
         check_freemetas_is_empty rebus1 freemetas1 ;
         check_freemetas_is_empty rebus2 freemetas2
   ) metas

let unification_rewrite l2r c1 c2 cl rel but gl = 
  let (env',c') =
    try
      (* ~flags:(false,true) to allow to mark occurences that must not be
         rewritten simply by replacing them with let-defined definitions
         in the context *)
      Unification.w_unify_to_subterm ~flags:rewrite_unif_flags (pf_env gl) ((if l2r then c1 else c2),but) cl.evd
    with
	Pretype_errors.PretypeError _ ->
	  (* ~flags:(true,true) to make Ring work (since it really
             exploits conversion) *)
	  Unification.w_unify_to_subterm ~flags:rewrite2_unif_flags
	    (pf_env gl) ((if l2r then c1 else c2),but) cl.evd
  in
  let cl' = {cl with evd = env' } in
  let c1 = Clenv.clenv_nf_meta cl' c1 
  and c2 = Clenv.clenv_nf_meta cl' c2 in
  check_evar_map_of_evars_defs env';
  let prf = Clenv.clenv_value cl' in
  let prfty = Clenv.clenv_type cl' in
    if occur_meta prf then
      {cl=cl'; prf=(mkRel 1); rel=rel; l2r=l2r; c1=c1; c2=c2; c=None; abs=Some (prf, prfty)}
    else
      {cl=cl'; prf=prf; rel=rel; l2r=l2r; c1=c1; c2=c2; c=None; abs=None}

let get_hyp gl c clause l2r = 
  match kind_of_term (pf_type_of gl c) with
      Prod _ -> 
	let hi = decompose_setoid_eqhyp gl c l2r in
	let but = match clause with Some id -> pf_get_hyp_typ gl id | None -> pf_concl gl in
	  unification_rewrite hi.l2r hi.c1 hi.c2 hi.cl hi.rel but gl
    | _ -> decompose_setoid_eqhyp gl c l2r
	
let general_s_rewrite l2r c ~new_goals gl =
  let meta = Evarutil.new_meta() in
  let hypinfo = ref (get_hyp gl c None l2r) in
    cl_rewrite_clause_aux hypinfo meta [] None gl

let general_s_rewrite_in id l2r c ~new_goals gl =
  let meta = Evarutil.new_meta() in
  let hypinfo = ref (get_hyp gl c (Some id) l2r) in
    cl_rewrite_clause_aux hypinfo meta [] (Some (([],id), [])) gl
    
let general_s_rewrite_clause = function
  | None -> general_s_rewrite
  | Some id -> general_s_rewrite_in id

let _ = Equality.register_general_setoid_rewrite_clause general_s_rewrite_clause

(* [setoid_]{reflexivity,symmetry,transitivity} tactics *)

let relation_of_constr c = 
  match kind_of_term c with
    | App (f, args) when Array.length args >= 2 -> 
	let relargs, args = array_chop (Array.length args - 2) args in
	  mkApp (f, relargs), args
    | _ -> error "Not an applied relation"

let setoid_reflexivity gl =
  let env = pf_env gl in
  let rel, args = relation_of_constr (pf_concl gl) in
    try
      apply (reflexive_proof env (pf_type_of gl args.(0)) rel) gl
    with Not_found -> 
      tclFAIL 0 (str" The relation " ++ Printer.pr_constr_env env rel ++ str" is not a declared reflexive relation")
	gl

let setoid_symmetry gl =
  let env = pf_env gl in
  let rel, args = relation_of_constr (pf_concl gl) in
    try
      apply (symmetric_proof env (pf_type_of gl args.(0)) rel) gl
    with Not_found -> 
      tclFAIL 0 (str" The relation " ++ Printer.pr_constr_env env rel ++ str" is not a declared symmetric relation")
	gl
	
let setoid_transitivity c gl =
  let env = pf_env gl in
  let rel, args = relation_of_constr (pf_concl gl) in
    try
      apply_with_bindings
	((transitive_proof env (pf_type_of gl args.(0)) rel),
	Rawterm.ExplicitBindings [ dummy_loc, Rawterm.NamedHyp (id_of_string "y"), c ]) gl
    with Not_found -> 
      tclFAIL 0
	(str" The relation " ++ Printer.pr_constr_env env rel ++ str" is not a declared transitive relation") gl
	
let setoid_symmetry_in id gl =
  let ctype = pf_type_of gl (mkVar id) in
  let binders,concl = Sign.decompose_prod_assum ctype in
  let (equiv, args) = decompose_app concl in
  let rec split_last_two = function
    | [c1;c2] -> [],(c1, c2)
    | x::y::z -> let l,res = split_last_two (y::z) in x::l, res
    | _ -> error "The term provided is not an equivalence" 
  in
  let others,(c1,c2) = split_last_two args in
  let he,c1,c2 =  mkApp (equiv, Array.of_list others),c1,c2 in
  let new_hyp' =  mkApp (he, [| c2 ; c1 |]) in
  let new_hyp = it_mkProd_or_LetIn new_hyp'  binders in
    tclTHENS (cut new_hyp)
      [ intro_replacing id;
	tclTHENLIST [ intros; setoid_symmetry; apply (mkVar id); Tactics.assumption ] ]
      gl

let _ = Tactics.register_setoid_reflexivity setoid_reflexivity
let _ = Tactics.register_setoid_symmetry setoid_symmetry
let _ = Tactics.register_setoid_symmetry_in setoid_symmetry_in
let _ = Tactics.register_setoid_transitivity setoid_transitivity

TACTIC EXTEND setoid_symmetry
   [ "setoid_symmetry" ] -> [ setoid_symmetry ]
 | [ "setoid_symmetry" "in" hyp(n) ] -> [ setoid_symmetry_in n ]
END

TACTIC EXTEND setoid_reflexivity
   [ "setoid_reflexivity" ] -> [ setoid_reflexivity ]
END

TACTIC EXTEND setoid_transitivity
   [ "setoid_transitivity" constr(t) ] -> [ setoid_transitivity t ]
END
