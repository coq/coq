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

(** Typeclasses instance search tactic / eauto *)

open Auto

let e_give_exact c gl = 
  let t1 = (pf_type_of gl c) and t2 = pf_concl gl in 
  if occur_existential t1 or occur_existential t2 then 
     tclTHEN (Clenvtac.unify t1) (exact_check c) gl
  else exact_check c gl

let assumption id = e_give_exact (mkVar id)

open Unification

let auto_unif_flags = ref {
  modulo_conv_on_closed_terms = true; 
  use_metas_eagerly = true;
  modulo_delta = Cpred.empty;
}

let unify_e_resolve (c,clenv) gls = 
  let clenv' = connect_clenv gls clenv in
  let clenv' = clenv_unique_resolver false ~flags:(!auto_unif_flags) clenv' gls in
    Clenvtac.clenv_refine true clenv' gls

let unify_resolve (c,clenv) gls = 
  let clenv' = connect_clenv gls clenv in
  let clenv' = clenv_unique_resolver false ~flags:(!auto_unif_flags) clenv' gls in  
    Clenvtac.clenv_refine false clenv' gls

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
    if occur_existential concl then
      list_map_append (Hint_db.map_all hdc) (local_db::db_list)
    else
      list_map_append (Hint_db.map_auto (hdc,concl)) (local_db::db_list)
  in 
  let tac_of_hint = 
    fun {pri=b; pat = p; code=t} -> 
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
	(tac,b,fmt_autotactic t)
  in 
    List.map tac_of_hint hintl

and e_trivial_resolve db_list local_db gl = 
  try 
    e_my_find_search db_list local_db 
      (List.hd (head_constr_bound gl [])) gl
  with Bound | Not_found -> []

let e_possible_resolve db_list local_db gl =
  try 
    e_my_find_search db_list local_db 
      (List.hd (head_constr_bound gl [])) gl
  with Bound | Not_found -> []

let find_first_goal gls = 
  try first_goal gls with UserError _ -> assert false


type search_state = { 
  depth : int; (*r depth of search before failing *)
  tacres : goal list sigma * validation;
  pri : int;
  last_tactic : std_ppcmds;
(*   filter : constr -> constr -> bool; *)
  dblist : Auto.Hint_db.t list;
  localdb :  Auto.Hint_db.t list }
    
let filter_hyp t = 
  match kind_of_term t with
    | Evar _ | Meta _ | Sort _ -> false
    | _ -> true

module SearchProblem = struct
    
  type state = search_state

  let debug = ref false

  let success s = (sig_it (fst s.tacres)) = []

  let pr_ev evs ev = Printer.pr_constr_env (Evd.evar_env ev) (Evarutil.nf_evar evs ev.Evd.evar_concl)
    
  let pr_goals gls =
    let evars = Evarutil.nf_evars (Refiner.project gls) in
      prlist (pr_ev evars) (sig_it gls)
	
  let filter_tactics (glls,v) l =
(*     if !debug then *)
(*       (let _ = Proof_trees.db_pr_goal (List.hd (sig_it glls)) in *)
(*       let evars = Evarutil.nf_evars (Refiner.project glls) in *)
(*     	msg (str"Goal: " ++ pr_ev evars (List.hd (sig_it glls)) ++ str"\n")); *)
    let rec aux = function
      | [] -> []
      | (tac,pri,pptac) :: tacl -> 
	  try 
(* 	    if !debug then msg (str"\nTrying tactic: " ++ pptac ++ str"\n"); *)
	    let (lgls,ptl) = apply_tac_list tac glls in 
	    let v' p = v (ptl p) in
(* 	      	      if !debug then *)
(* 	      		begin *)
(* 	      		  let evars = Evarutil.nf_evars (Refiner.project glls) in *)
(* 	      		    msg (str"\nOn goal: " ++ pr_ev evars (List.hd (sig_it glls)) ++ str"\n"); *)
(* 	      		    msg (hov 1 (pptac ++ str" gives: \n" ++ pr_goals lgls ++ str"\n")) *)
(* 	      		end; *)
	      ((lgls,v'),pri,pptac) :: aux tacl
	  with e when Logic.catchable_exception e ->
	    (* 	    if !debug then msg (str"failed\n"); *)
	    aux tacl
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
      if d <> 0 && d <> 1 then d else
	let pri = s.pri - s'.pri in
	  if pri <> 0 then pri
	  else nbgoals s - nbgoals s'

  let branching s = 
    if s.depth = 0 then 
      []
    else      
      let lg = fst s.tacres in
      let nbgl = List.length (sig_it lg) in
      assert (nbgl > 0);
      let g = find_first_goal lg in
(*       let filt = s.filter (pf_concl g) in *)
      let assumption_tacs = 
	let l = 
	  filter_tactics s.tacres
	    (List.map 
		(fun id -> (Eauto.e_give_exact_constr (mkVar id), 0,
			   (str "exact" ++ spc () ++ pr_id id)))
		(List.filter (fun id -> filter_hyp (pf_get_hyp_typ g id))
		    (pf_ids_of_hyps g)))
	in
	  List.map (fun (res,pri,pp) -> { s with tacres = res; pri = 0;
	    last_tactic = pp; localdb = List.tl s.localdb }) l
      in
(*       let intro_tac =  *)
(* 	List.map  *)
(* 	  (fun ((lgls,_) as res,pri,pp) ->  *)
(* 	     let g' = first_goal lgls in  *)
(* 	     let hintl =  *)
(* 	       make_resolve_hyp (pf_env g') (project g') (pf_last_hyp g') *)
(* 	     in	        *)
(*              let ldb = Hint_db.add_list hintl (match s.localdb with [] -> assert false | hd :: _ -> hd) in *)
(* 	       { s with tacres = res;  *)
(* 		 last_tactic = pp; *)
(* 		 pri = pri; *)
(* 		 localdb = ldb :: List.tl s.localdb }) *)
(* 	  (filter_tactics s.tacres [Tactics.intro,1,(str "intro")]) *)
(*       in *)
      let possible_resolve ((lgls,_) as res, pri, pp) =
	let nbgl' = List.length (sig_it lgls) in
	  if nbgl' < nbgl then
	    { s with tacres = res; last_tactic = pp; pri = pri;
	      localdb = List.tl s.localdb }
	  else 
	    { s with 
	      depth = pred s.depth; tacres = res; 
	      last_tactic = pp; pri = pri;
	      localdb = 
		list_addn (nbgl'-nbgl) (List.hd s.localdb) s.localdb }
      in
      let rec_tacs = 
	let l = 
	  filter_tactics s.tacres (e_possible_resolve s.dblist (List.hd s.localdb) (pf_concl g))
	in
	List.map possible_resolve l
      in
      List.sort compare (assumption_tacs (* @intro_tac  @ custom_tac *) @ rec_tacs)

  let pp s = 
    msg (hov 0 (str " depth=" ++ int s.depth ++ spc () ++ 
		  s.last_tactic ++ str "\n"))

end

module Search = Explore.Make(SearchProblem)


let filter_pat c =
  try
    let morg = Nametab.global (Qualid (dummy_loc, qualid_of_string "Coq.Classes.Morphisms.Morphism")) in
    let morc = constr_of_global morg in
	match kind_of_term c with
	  | App(morph, [| t; r; m |]) when eq_constr morph morc ->
	      (fun y ->
		(match y.pat with
		    Some (PApp (PRef mor, [| t'; r'; m' |])) when mor = morg ->
		      (match m' with
			| PRef c -> if isConst m then eq_constr (constr_of_global c) m else false
			| _ -> true)
		  | _ -> true))
	  | _ -> fun _ -> true
  with _ -> fun _ -> true

let morphism_class = 
  lazy (class_info (Nametab.global (Qualid (dummy_loc, qualid_of_string "Coq.Classes.Morphisms.Morphism"))))
    
let filter c =
  try let morc = constr_of_global (Nametab.global (Qualid (dummy_loc, qualid_of_string "Coq.Classes.Morphisms.Morphism"))) in
	match kind_of_term c with
	  | App(morph, [| t; r; m |]) when eq_constr morph morc ->
	      (fun y ->
		let (_, r) = decompose_prod y in
		  (match kind_of_term r with
		      App (morph', [| t'; r'; m' |]) when eq_constr morph' morc ->
			(match kind_of_term m' with
			  | Rel n -> true
			  | Const c -> eq_constr m m'
			  | App _ -> true
			  | _ -> false)
		    | _ -> false))
	  | _ -> fun _ -> true
  with _ -> fun _ -> true

let make_initial_state n gls dblist localdbs =
  { depth = n;
    tacres = gls;
    pri = 0;
(*     filter = filter; *)
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
  with Not_found -> error "EAuto: breadth first search failed"

let e_search_auto debug (in_depth,p) lems db_list gls = 
  let sigma = Evd.sig_sig (fst gls) and gls' = Evd.sig_it (fst gls) in
  let local_dbs = List.map (fun gl -> make_local_hint_db true lems ({it = gl; sigma = sigma})) gls' in
  let state = make_initial_state p gls db_list local_dbs in
  if in_depth then 
    e_depth_search debug state
  else
    e_breadth_search debug state

let full_eauto debug n lems gls = 
  let dbnames = current_db_names () in
  let dbnames =  list_subtract dbnames ["v62"] in
  let db_list = List.map searchtable_map dbnames in
    e_search_auto debug n lems db_list gls

exception Found of evar_map

let valid goals p res_sigma l = 
  let evm = 
    List.fold_left2 
      (fun sigma (ev, evi) prf ->
	let cstr, obls = Refiner.extract_open_proof !res_sigma prf in
	  if not (Evd.is_defined sigma ev) then
	    Evd.define sigma ev cstr
	  else sigma)
      !res_sigma goals l
  in raise (Found evm)
    
let resolve_all_evars_once debug (mode, depth) env p evd =
  let evm = Evd.evars_of evd in
  let goals, evm' = 
    Evd.fold
      (fun ev evi (gls, evm) ->
	if evi.evar_body = Evar_empty 
	  && Typeclasses.is_resolvable evi
	  && p ev evi then ((ev,evi) :: gls, Evd.add evm ev (Typeclasses.mark_unresolvable evi)) else 
	  (gls, Evd.add evm ev evi))
      evm ([], Evd.empty)
  in
  let goals = List.rev goals in
  let gls = { it = List.map snd goals; sigma = evm' } in
  let res_sigma = ref evm' in
  let gls', valid' = full_eauto debug (mode, depth) [] (gls, valid goals p res_sigma) in
    res_sigma := Evarutil.nf_evars (sig_sig gls');
    try ignore(valid' []); assert(false) 
    with Found evm' -> Evarutil.nf_evar_defs (Evd.evars_reset_evd evm' evd)

exception FoundTerm of constr

let resolve_one_typeclass env gl =
  let gls = { it = [ Evd.make_evar (Environ.named_context_val env) gl ] ; sigma = Evd.empty } in
  let valid x = raise (FoundTerm (fst (Refiner.extract_open_proof Evd.empty (List.hd x)))) in
  let gls', valid' = full_eauto false (true, 15) [] (gls, valid) in
    try ignore(valid' []); assert false with FoundTerm t -> 
      let term = Evarutil.nf_evar (sig_sig gls') t in
	if occur_existential term then raise Not_found else term

let has_undefined p evd =
  Evd.fold (fun ev evi has -> has ||
    (evi.evar_body = Evar_empty && p ev evi))
    (Evd.evars_of evd) false
    
let resolve_all_evars debug m env p oevd =
(*   let evd = resolve_all_evars_once ~tac debug m env p evd in *)
(*     if has_undefined p evd then raise Not_found *)
(*     else evd *)
  try
    let rec aux n evd =
      if has_undefined p evd then
	if n > 0 then
	  let evd' = resolve_all_evars_once debug m env p evd in
	    aux (pred n) evd'
	else None
      else Some evd
    in aux 3 oevd
  with Not_found -> None
    
(** Handling of the state of unfolded constants. *)

open Libobject

let freeze () = !auto_unif_flags.modulo_delta

let unfreeze delta = 
  auto_unif_flags := { !auto_unif_flags with modulo_delta = delta }
    
let init () =
  auto_unif_flags := {
    modulo_conv_on_closed_terms = true; 
    use_metas_eagerly = true;
    modulo_delta = Cpred.empty;
  }
    
let _ = 
  Summary.declare_summary "typeclasses_unfold"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_module = false;
      Summary.survive_section = true }
    
let cache_autounfold (_,unfoldlist) = 
  auto_unif_flags := { !auto_unif_flags with
    modulo_delta = Cpred.union !auto_unif_flags.modulo_delta unfoldlist }
  
let subst_autounfold (_,subst,(unfoldlist as obj)) = 
  let b, l' = Cpred.elements unfoldlist in
  let l'' = list_smartmap (fun x -> fst (Mod_subst.subst_con subst x)) l' in
    if l'' == l' then obj 
    else
      let set = List.fold_right Cpred.add l'' Cpred.empty in
	if not b then set
	else Cpred.complement set
	  
let classify_autounfold (_,obj) = Substitute obj
      
let export_autounfold obj =
  Some obj

let (inAutoUnfold,outAutoUnfold) =
  declare_object 
    {(default_object "AUTOUNFOLD") with
      cache_function = cache_autounfold;
      load_function = (fun _ -> cache_autounfold);
      subst_function = subst_autounfold;
      classify_function = classify_autounfold;
      export_function = export_autounfold }

let cpred_of_list l =
  List.fold_right Cpred.add l Cpred.empty

VERNAC COMMAND EXTEND Typeclasses_Unfold_Settings
| [ "Typeclasses" "unfold" constr_list(cl) ] -> [
    let csts = 
      List.map
	(fun c -> 
	  let c = Constrintern.interp_constr Evd.empty (Global.env ()) c in
	    match kind_of_term c with
	      | Const c -> c
	      | _ -> error "Not a constant reference")
	cl
    in
      Lib.add_anonymous_leaf (inAutoUnfold (cpred_of_list csts))
  ]
END


(** Typeclass-based rewriting. *)

let respect_proj = lazy (mkConst (List.hd (Lazy.force morphism_class).cl_projs))

let make_dir l = make_dirpath (List.map id_of_string (List.rev l))

let try_find_reference dir s =
  let sp = Libnames.make_path (make_dir ("Coq"::dir)) (id_of_string s) in
    constr_of_global (Nametab.absolute_reference sp)

let gen_constant dir s = Coqlib.gen_constant "Class_setoid" dir s
let coq_proj1 = lazy(gen_constant ["Init"; "Logic"] "proj1")
let coq_proj2 = lazy(gen_constant ["Init"; "Logic"] "proj2")
let iff = lazy (gen_constant ["Init"; "Logic"] "iff")
let coq_all = lazy (gen_constant ["Init"; "Logic"] "all")
let impl = lazy (gen_constant ["Program"; "Basics"] "impl")
let arrow = lazy (gen_constant ["Program"; "Basics"] "arrow")
let coq_id = lazy (gen_constant ["Program"; "Basics"] "id")

let reflexive_type = lazy (try_find_reference ["Classes"; "RelationClasses"] "Reflexive")
let reflexive_proof = lazy (try_find_reference ["Classes"; "RelationClasses"] "reflexivity")

let symmetric_type = lazy (try_find_reference ["Classes"; "RelationClasses"] "Symmetric")
let symmetric_proof = lazy (try_find_reference ["Classes"; "RelationClasses"] "symmetry")

let transitive_type = lazy (try_find_reference ["Classes"; "RelationClasses"] "Transitive")
let transitive_proof = lazy (try_find_reference ["Classes"; "RelationClasses"] "transitivity")

let coq_inverse = lazy (gen_constant (* ["Classes"; "RelationClasses"] "inverse" *)
			   ["Program"; "Basics"] "flip")

let inverse car rel = mkApp (Lazy.force coq_inverse, [| car ; car; mkProp; rel |])

let complement = lazy (gen_constant ["Classes"; "RelationClasses"] "complement")
let pointwise_relation = lazy (gen_constant ["Classes"; "RelationClasses"] "pointwise_relation")

let respectful_dep = lazy (gen_constant ["Classes"; "Morphisms"] "respectful_dep")
let respectful = lazy (gen_constant ["Classes"; "Morphisms"] "respectful")

let equivalence = lazy (gen_constant ["Classes"; "RelationClasses"] "Equivalence")
let default_relation = lazy (gen_constant ["Classes"; "RelationClasses"] "DefaultRelation")

let coq_relation = lazy (gen_constant ["Relations";"Relation_Definitions"] "relation")
let mk_relation a = mkApp (Lazy.force coq_relation, [| a |])
let coq_relationT = lazy (gen_constant ["Classes";"Relations"] "relationT")

let setoid_refl_proj = lazy (gen_constant ["Classes"; "SetoidClass"] "equivalence_reflexive")

let setoid_equiv = lazy (gen_constant ["Classes"; "SetoidClass"] "equiv")
let setoid_morphism = lazy (gen_constant ["Classes"; "SetoidClass"] "setoid_morphism")
let setoid_refl_proj = lazy (gen_constant ["Classes"; "SetoidClass"] "equivalence_reflexive")
  
let arrow_morphism a b = 
  if isprop a && isprop b then
    Lazy.force impl
  else
    mkApp(Lazy.force arrow, [|a;b|])
(*     mkLambda (Name (id_of_string "A"), a,  *)
(* 	     mkLambda (Name (id_of_string "B"), b,  *)
(* 		      mkProd (Anonymous, mkRel 2, mkRel 2))) *)
    
let setoid_refl pars x = 
  applistc (Lazy.force setoid_refl_proj) (pars @ [x])
      
let morphism_type = lazy (constr_of_global (Lazy.force morphism_class).cl_impl)

exception Found of (constr * constr * (types * types) list * constr * constr array *
		       (constr * (constr * constr * constr * constr)) option array)

let is_equiv env sigma t = 
  isConst t && Reductionops.is_conv env sigma (Lazy.force setoid_equiv) t

let split_head = function
    hd :: tl -> hd, tl
  | [] -> assert(false)

let build_signature isevars env m (cstrs : 'a option list) (finalcstr : 'a Lazy.t option) (f : 'a -> constr) =
  let new_evar isevars env t =
    Evarutil.e_new_evar isevars env
      (* ~src:(dummy_loc, ImplicitArg (ConstRef (Lazy.force respectful), (n, Some na))) *) t
  in
  let mk_relty ty obj =
    match obj with
      | None -> 
	  let relty = mk_relation ty in
	    new_evar isevars env relty
      | Some x -> f x
  in
  let rec aux ty l =
    let t = Reductionops.whd_betadeltaiota env (Evd.evars_of !isevars) ty in
    match kind_of_term t, l with
      | Prod (na, ty, b), obj :: cstrs -> 
	  let (b, arg, evars) = aux b cstrs in
	  let ty = Reductionops.nf_betaiota ty in
	  let relty = mk_relty ty obj in
	  let arg' = mkApp (Lazy.force respectful, [| ty ; b ; relty ; arg |]) in
	    mkProd(na, ty, b), arg', (ty, relty) :: evars
      | _, obj :: _ -> anomaly "build_signature: not enough products"
      | _, [] -> 
	  (match finalcstr with
	      None -> 
		let t = Reductionops.nf_betaiota ty in
		let rel = mk_relty t None in 
		  t, rel, [t, rel]
	    | Some codom -> let (t, rel) = Lazy.force codom in
			      t, rel, [t, rel])
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
  try 
    let goal =
      mkApp (Lazy.force proof_type, [| carrier ; relation |])
    in
    let inst = resolve_one_typeclass env goal in
      mkApp (Lazy.force proof_method, [| carrier ; relation ; inst |])
  with e when Logic.catchable_exception e -> raise Not_found

let reflexive_proof env = find_class_proof reflexive_type reflexive_proof env
let symmetric_proof env = find_class_proof symmetric_type symmetric_proof env
let transitive_proof env = find_class_proof transitive_type transitive_proof env

exception FoundInt of int

let array_find (arr: 'a array) (pred: int -> 'a -> bool): int = 
  try
    for i=0 to Array.length arr - 1 do if pred i (arr.(i)) then raise (FoundInt i) done;
    raise Not_found
  with FoundInt i -> i

let resolve_morphism env sigma oldt m ?(fnewt=fun x -> x) args args' cstr evars =
  let morph_instance, proj, sigargs, m', args, args' = 
    let first = try (array_find args' (fun i b -> b <> None)) with Not_found -> raise (Invalid_argument "resolve_morphism") in
    let morphargs, morphobjs = array_chop first args in
    let morphargs', morphobjs' = array_chop first args' in
    let appm = mkApp(m, morphargs) in
    let appmtype = Typing.type_of env sigma appm in
    let cstrs = List.map (function None -> None | Some (_, (a, r, _, _)) -> Some (a, r)) (Array.to_list morphobjs') in
    let appmtype', signature, sigargs = build_signature evars env appmtype cstrs cstr (fun (a, r) -> r) in
    let cl_args = [| appmtype' ; signature ; appm |] in
    let app = mkApp (Lazy.force morphism_type, cl_args) in
    let morph = Evarutil.e_new_evar evars env app in
    let proj = 
      mkApp (Lazy.force respect_proj, 
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
	[ a, r ] -> (proof, (a, r, oldt, fnewt newt))
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

let decompose_setoid_eqhyp env sigma c left2right =
  let ctype = Typing.type_of env sigma c in
  let eqclause  = Clenv.mk_clenv_from_env env sigma None (c,ctype) in
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
  Unification.modulo_delta = Cpred.empty
}

let rewrite2_unif_flags = {
  Unification.modulo_conv_on_closed_terms = true;
  Unification.use_metas_eagerly = true;
  Unification.modulo_delta = Cpred.empty
 }

(* let unification_rewrite c1 c2 cl but gl =  *)
(*   let (env',c1) = *)
(*     try *)
(*       (\* ~flags:(false,true) to allow to mark occurrences that must not be *)
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

let refresh_hypinfo env sigma hypinfo = 
  if !hypinfo.abs = None then
    let {l2r=l2r; c = c} = !hypinfo in
      match c with 
	| Some c ->
	    (* Refresh the clausenv to not get the same meta twice in the goal. *)
	    hypinfo := decompose_setoid_eqhyp env sigma c l2r;
	| _ -> ()
  else ()

let convertible env x y =
  ignore(Reduction.conv env x y)
  
let unify_eqn env sigma hypinfo t = 
  try 
    let {cl=cl; prf=prf; rel=rel; l2r=l2r; c1=c1; c2=c2; c=c; abs=abs} = !hypinfo in
    let env' = 
      match abs with
	  Some _ -> convertible env (if l2r then c1 else c2) t; cl
	| None ->
	    try clenv_unify allowK ~flags:rewrite_unif_flags
	      CONV (if l2r then c1 else c2) t cl
	    with Pretype_errors.PretypeError _ ->
	      (* For Ring essentially, only when doing setoid_rewrite *)
	      clenv_unify allowK ~flags:rewrite2_unif_flags
		CONV (if l2r then c1 else c2) t cl
    in
    let c1 = Clenv.clenv_nf_meta env' c1 
    and c2 = Clenv.clenv_nf_meta env' c2
    and rel = Clenv.clenv_nf_meta env' rel in
    let car = Typing.type_of env'.env (Evd.evars_of env'.evd) c1 in
    let prf =
      if abs = None then
(* 	let (rel, args) = destApp typ in *)
(* 	let relargs, args = array_chop (Array.length args - 2) args in *)
(* 	let rel = mkApp (rel, relargs) in *)
	let prf = Clenv.clenv_value env' in
	  if occur_meta prf then refresh_hypinfo env sigma hypinfo;
	  prf
      else prf
    in
    let res =
      if l2r then (prf, (car, rel, c1, c2))
      else
	try (mkApp (symmetric_proof env car rel, [| c1 ; c2 ; prf |]), (car, rel, c2, c1))
	with Not_found ->
	  (prf, (car, inverse car rel, c2, c1))
    in Some (env', res)
  with _ -> None

let unfold_impl t = 
  match kind_of_term t with
    | App (arrow, [| a; b |])(*  when eq_constr arrow (Lazy.force impl) *) -> 
	mkProd (Anonymous, a, b)
    | _ -> assert false

let unfold_id t = 
  match kind_of_term t with
    | App (id, [| a; b |]) (* when eq_constr id (Lazy.force coq_id) *) -> b
    | _ -> assert false

let unfold_all t = 
  match kind_of_term t with
    | App (id, [| a; b |]) (* when eq_constr id (Lazy.force coq_all) *) ->
	(match kind_of_term b with
	  | Lambda (n, ty, b) -> mkProd (n, ty, b)
	  | _ -> assert false)
    | _ -> assert false

(* let lift_cstr env sigma evars args cstr = *)
(*   let codom =  *)
(*     match cstr with *)
(*       | Some c -> c *)
(*       | None -> *)
(* 	  let ty = Evarutil.e_new_evar evars env (new_Type ()) in *)
(* 	  let rel = Evarutil.e_new_evar evars env (mk_relation ty) in *)
(* 	    (ty, rel) *)
(*   in *)
(*     Array.fold_right *)
(*       (fun arg (car, rel) ->  *)
(* 	let ty = Typing.type_of env sigma arg in *)
(* 	let car' = mkProd (Anonymous, ty, car) in *)
(* 	let rel' = mkApp (Lazy.force pointwise_relation, [| ty; car; rel |]) in *)
(* 	  (car', rel')) *)
(*       args codom *)

let rec decomp_pointwise n c =
  if n = 0 then c
  else
    match kind_of_term c with
      | App (pointwise, [| a; b; relb |]) -> decomp_pointwise (pred n) relb
      | _ -> raise Not_found
	  
let lift_cstr env sigma evars args cstr =
  match cstr with
    | Some codom -> 
	let cstr () =
	  Array.fold_right
	    (fun arg (car, rel) -> 
	      let ty = Typing.type_of env sigma arg in
	      let car' = mkProd (Anonymous, ty, car) in
	      let rel' = mkApp (Lazy.force pointwise_relation, [| ty; car; rel |]) in
		(car', rel'))
	    args (Lazy.force codom)
	in Some (Lazy.lazy_from_fun cstr)
    | None -> None
	  
type rewrite_flags = { under_lambdas : bool; on_morphisms : bool }

let default_flags = { under_lambdas = true; on_morphisms = true; }

let build_new gl env sigma flags occs hypinfo concl cstr evars =
  let is_occ occ = occs = [] || List.mem occ occs in
  let rec aux env t occ cstr =
    match unify_eqn env sigma hypinfo t with
      | Some (env', (prf, hypinfo as x)) ->
	  if is_occ occ then (
	    evars := Evd.evar_merge !evars (Evd.evars_of (Evd.undefined_evars env'.evd));
	    match cstr with
		None -> Some x, succ occ
	      | Some _ ->
		  let (car, r, orig, dest) = hypinfo in
		  let res = 
		    try 
		      Some 
			(resolve_morphism env sigma t ~fnewt:unfold_id
			  (mkApp (Lazy.force coq_id, [| car |]))
			  [| orig |] [| Some x |] cstr evars)
		    with Not_found -> None
		  in res, succ occ)
	  else None, succ occ
      | None -> 
	  match kind_of_term t with
	    | App (m, args) ->
		let rewrite_args () = 
		  let args', occ = 
		    Array.fold_left 
		      (fun (acc, occ) arg -> let res, occ = aux env arg occ None in (res :: acc, occ))
		      ([], occ) args
		  in
		  let res =
		    if List.for_all (fun x -> x = None) args' then None
		    else 
		      let args' = Array.of_list (List.rev args') in
			(try Some (resolve_morphism env sigma t m args args' cstr evars)
			  with Not_found -> None)
		  in res, occ
		in
		  if flags.on_morphisms then
		    let m', occ = aux env m occ (lift_cstr env sigma evars args cstr) in
		      match m' with
			  None -> rewrite_args () (* Standard path, try rewrite on arguments *)
			| Some (prf, (car, rel, c1, c2)) -> 
			    (* We rewrote the function and get a proof of pointwise rel for the arguments.
			       We just apply it. *)
			    let nargs = Array.length args in
			    let decompprod c = snd (Reductionops.decomp_n_prod env (Evd.evars_of !evars) nargs c) in
			    let res = 
			      try Some (mkApp (prf, args),
				       (decompprod car, decomp_pointwise nargs rel, mkApp(c1, args), mkApp(c2, args)))
			      with Not_found -> None
			    in res, occ
		  else rewrite_args ()
		    
	    | Prod (_, x, b) when not (dependent (mkRel 1) b) -> 
		let x', occ = aux env x occ None in
		let b', occ = aux env b occ None in
		let res = 
		  if x' = None && b' = None then None
		  else 
		    (try 
			Some (resolve_morphism env sigma t
				 ~fnewt:unfold_impl
				 (arrow_morphism (Typing.type_of env sigma x) (Typing.type_of env sigma b))
				 [| x ; b |] [| x' ; b' |]
				 cstr evars)
		      with Not_found -> None)
		in res, occ
		  
	    | Prod (n, ty, b) ->
		let lam = mkLambda (n, ty, b) in
		let lam', occ = aux env lam occ None in
		let res = 
		  match lam' with
		    | None -> None
		    | Some (prf, (car, rel, c1, c2)) ->
			try 
			  Some (resolve_morphism env sigma t
				   ~fnewt:unfold_all
				   (Lazy.force coq_all) [| ty ; lam |] [| None; lam' |]
				   cstr evars)
			with Not_found -> None
		in res, occ
		  
	    | Lambda (n, t, b) when flags.under_lambdas ->
		let env' = Environ.push_rel (n, None, t) env in
		refresh_hypinfo env' sigma hypinfo;
		let b', occ = aux env' b occ None in
		let res =
		  match b' with
		      None -> None
		    | Some (prf, (car, rel, c1, c2)) ->
			let prf' = mkLambda (n, t, prf) in
			let car' = mkProd (n, t, car) in
			let rel' = mkApp (Lazy.force pointwise_relation, [| t; car; rel |]) in
			let c1' = mkLambda(n, t, c1) and c2' = mkLambda (n, t, c2) in
			  Some (prf', (car', rel', c1', c2'))
		in res, occ
	    | _ -> None, occ
  in aux env concl 1 cstr
    
let resolve_typeclass_evars d p env evd onlyargs =
  let pred = 
    if onlyargs then 
      (fun ev evi -> Typeclasses.is_implicit_arg (snd (Evd.evar_source ev evd)) &&
	class_of_constr evi.Evd.evar_concl <> None)
    else
      (fun ev evi -> class_of_constr evi.Evd.evar_concl <> None)
  in resolve_all_evars d p env pred evd
      
let cl_rewrite_clause_aux ?(flags=default_flags) hypinfo goal_meta occs clause gl =
  let concl, is_hyp = 
    match clause with
	Some ((_, id), _) -> pf_get_hyp_typ gl id, Some id
      | None -> pf_concl gl, None
  in
  let cstr = 
    match is_hyp with
	None -> (mkProp, inverse mkProp (Lazy.force impl))
      | Some _ -> (mkProp, Lazy.force impl)
  in
  let evars = ref (Evd.create_evar_defs Evd.empty) in
  let env = pf_env gl in
  let sigma = project gl in
  let eq, _ = build_new gl env sigma flags occs hypinfo concl (Some (Lazy.lazy_from_val cstr)) evars in
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
	    with 
	      | TypeClassError (_env, UnsatisfiableConstraints _evm) -> 
		  tclFAIL 0 (str" setoid rewrite failed: unable to satisfy the rewriting constraints.") gl
	      | Not_found ->
		  tclFAIL 0 (str" setoid rewrite failed: unable to satisfy the rewriting constraints.") gl)
      | None -> 
	  let {l2r=l2r; c1=x; c2=y} = !hypinfo in
	    raise (Pretype_errors.PretypeError (pf_env gl, Pretype_errors.NoOccurrenceFound (if l2r then x else y)))
	      (* tclFAIL 1 (str"setoid rewrite failed") gl *)
	  
let cl_rewrite_clause c left2right occs clause gl =
  let meta = Evarutil.new_meta() in
  let hypinfo = ref (decompose_setoid_eqhyp (pf_env gl) (project gl) c left2right) in
    cl_rewrite_clause_aux hypinfo meta occs clause gl

open Genarg
open Extraargs

TACTIC EXTEND class_rewrite
| [ "clrewrite" orient(o) constr(c) "in" hyp(id) "at" occurrences(occ) ] -> [ cl_rewrite_clause c o occ (Some (([],id), [])) ]
| [ "clrewrite" orient(o) constr(c) "at" occurrences(occ) "in" hyp(id) ] -> [ cl_rewrite_clause c o occ (Some (([],id), [])) ]
| [ "clrewrite" orient(o) constr(c) "in" hyp(id) ] -> [ cl_rewrite_clause c o [] (Some (([],id), [])) ]
| [ "clrewrite" orient(o) constr(c) "at" occurrences(occ) ] -> [ cl_rewrite_clause c o occ None ]
| [ "clrewrite" orient(o) constr(c) ] -> [ cl_rewrite_clause c o [] None ]
END


let clsubstitute o c =
  let is_tac id = match kind_of_term c with Var id' when id' = id -> true | _ -> false in
    Tacticals.onAllClauses 
      (fun cl -> 
	match cl with
	  | Some ((_,id),_) when is_tac id -> tclIDTAC
	  | _ -> tclTRY (cl_rewrite_clause c o [] cl))

TACTIC EXTEND substitute
| [ "substitute" orient(o) constr(c) ] -> [ clsubstitute o c ]
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
	
let solve_inst debug mode depth env evd onlyargs all =
  match resolve_typeclass_evars debug (mode, depth) env evd onlyargs with 
    | None -> 
	if all then 
	  (* Unable to satisfy the constraints. *)
	  Typeclasses_errors.unsatisfiable_constraints env evd
	else (* Best effort: do nothing *) evd
    | Some evd -> evd

let _ = 
  Typeclasses.solve_instanciations_problem :=
    solve_inst false true 15
      
VERNAC COMMAND EXTEND Typeclasses_Settings
 | [ "Typeclasses" "eauto" ":=" debug(d) search_mode(s) depth(depth) ] -> [ 
     let mode = match s with Some t -> t | None -> true in
     let depth = match depth with Some i -> i | None -> 15 in
       Typeclasses.solve_instanciations_problem :=
	 solve_inst d mode depth
   ]
END

TACTIC EXTEND typeclasses_eauto
| [ "typeclasses" "eauto" debug(d) search_mode(s) depth(depth) ] -> [ fun gl ->
    let env = pf_env gl in
    let sigma = project gl in
      if Evd.dom sigma = [] then Refiner.tclIDTAC gl
      else
	let evd = Evd.create_evar_defs sigma in
	let mode = match s with Some t -> t | None -> true in
	let depth = match depth with Some i -> i | None -> 15 in
	  match resolve_typeclass_evars d (mode, depth) env evd false with
	    | Some evd' -> Refiner.tclEVARS (Evd.evars_of evd') gl
	    | None -> tclIDTAC gl
  ]
END

let _ = 
  Classes.refine_ref := Refine.refine

(* Compatibility with old Setoids *)
  
TACTIC EXTEND setoid_rewrite
   [ "setoid_rewrite" orient(o) constr(c) ]
   -> [ cl_rewrite_clause c o [] None ]
 | [ "setoid_rewrite" orient(o) constr(c) "in" hyp(id) ] ->
      [ cl_rewrite_clause c o [] (Some (([],id), []))]
 | [ "setoid_rewrite" orient(o) constr(c) "at" occurrences(occ) ] ->
      [ cl_rewrite_clause c o occ None]
 | [ "setoid_rewrite" orient(o) constr(c) "at" occurrences(occ) "in" hyp(id)] ->
      [ cl_rewrite_clause c o occ (Some (([],id), []))]
 | [ "setoid_rewrite" orient(o) constr(c) "in" hyp(id) "at" occurrences(occ)] ->
      [ cl_rewrite_clause c o occ (Some (([],id), []))]
END

(* let solve_obligation lemma =  *)
(*   tclTHEN (Tacinterp.interp (Tacexpr.TacAtom (dummy_loc, Tacexpr.TacAnyConstructor None))) *)
(*     (eapply_with_bindings (Constrintern.interp_constr Evd.empty (Global.env()) lemma, NoBindings)) *)

let mkappc s l = CAppExpl (dummy_loc,(None,(Libnames.Ident (dummy_loc,id_of_string s))),l)

let declare_an_instance n s args =
  ((dummy_loc,Name n), Explicit,
  CAppExpl (dummy_loc, (None, Qualid (dummy_loc, qualid_of_string s)), 
	   args))

let declare_instance a aeq n s = declare_an_instance n s [a;aeq]

let anew_instance binders instance fields = 
  new_instance binders instance fields 
    ~on_free_vars:Classes.fail_on_free_vars
    None

let require_library dirpath =
  let qualid = (dummy_loc, Libnames.qualid_of_dirpath (Libnames.dirpath_of_string dirpath)) in
    Library.require_library [qualid] (Some false)

let check_required_library d =
  let d' = List.map id_of_string d in
  let dir = make_dirpath (List.rev d') in
  if (* not (Library.library_is_opened dir) ||  *)not (Library.library_is_loaded dir) then
    error ("Library "^(list_last d)^" has to be required first")

let init_setoid () =
  check_required_library ["Coq";"Setoids";"Setoid"]

let declare_instance_refl binders a aeq n lemma = 
  let instance = declare_instance a aeq (add_suffix n "_reflexive") "Coq.Classes.RelationClasses.Reflexive" 
  in anew_instance binders instance 
       [((dummy_loc,id_of_string "reflexivity"),[],lemma)]

let declare_instance_sym binders a aeq n lemma = 
  let instance = declare_instance a aeq (add_suffix n "_symmetric") "Coq.Classes.RelationClasses.Symmetric"
  in anew_instance binders instance 
       [((dummy_loc,id_of_string "symmetry"),[],lemma)]

let declare_instance_trans binders a aeq n lemma = 
  let instance = declare_instance a aeq (add_suffix n "_transitive") "Coq.Classes.RelationClasses.Transitive" 
  in anew_instance binders instance 
       [((dummy_loc,id_of_string "transitivity"),[],lemma)]

let constr_tac = Tacinterp.interp (Tacexpr.TacAtom (dummy_loc, Tacexpr.TacAnyConstructor (false,None)))

let declare_relation ?(binders=[]) a aeq n refl symm trans = 
  init_setoid ();
  match (refl,symm,trans) with 
      (None, None, None) -> 
	let instance = declare_instance a aeq n "Coq.Classes.RelationClasses.DefaultRelation"
	in ignore(anew_instance binders instance [])
    | (Some lemma1, None, None) -> 
	ignore (declare_instance_refl binders a aeq n lemma1)
    | (None, Some lemma2, None) -> 
	ignore (declare_instance_sym binders a aeq n lemma2)
    | (None, None, Some lemma3) -> 
	ignore (declare_instance_trans binders a aeq n lemma3)
    | (Some lemma1, Some lemma2, None) -> 
	ignore (declare_instance_refl binders a aeq n lemma1); 
	ignore (declare_instance_sym binders a aeq n lemma2)
    | (Some lemma1, None, Some lemma3) -> 
	let lemma_refl = declare_instance_refl binders a aeq n lemma1 in
	let lemma_trans = declare_instance_trans binders a aeq n lemma3 in
	let instance = declare_instance a aeq n "Coq.Classes.RelationClasses.PreOrder" 
	in ignore(
	    anew_instance binders instance 
	      [((dummy_loc,id_of_string "preorder_reflexive"), [], mkIdentC lemma_refl);
	       ((dummy_loc,id_of_string "preorder_transitive"),[], mkIdentC lemma_trans)])
    | (None, Some lemma2, Some lemma3) -> 
	let lemma_sym = declare_instance_sym binders a aeq n lemma2 in
	let lemma_trans = declare_instance_trans binders a aeq n lemma3 in
	let instance = declare_instance a aeq n "Coq.Classes.RelationClasses.PER" 
	in ignore(
	    anew_instance binders instance 
	      [((dummy_loc,id_of_string "per_symmetric"),  [], mkIdentC lemma_sym);
	       ((dummy_loc,id_of_string "per_transitive"),[], mkIdentC lemma_trans)])
     | (Some lemma1, Some lemma2, Some lemma3) -> 
	let lemma_refl = declare_instance_refl binders a aeq n lemma1 in 
	let lemma_sym = declare_instance_sym binders a aeq n lemma2 in
	let lemma_trans = declare_instance_trans binders a aeq n lemma3 in
	let instance = declare_instance a aeq n "Coq.Classes.RelationClasses.Equivalence" 
	in ignore(
	  anew_instance binders instance 
	    [((dummy_loc,id_of_string "equivalence_reflexive"), [], mkIdentC lemma_refl);
	     ((dummy_loc,id_of_string "equivalence_symmetric"),  [], mkIdentC lemma_sym);
	     ((dummy_loc,id_of_string "equivalence_transitive"),[], mkIdentC lemma_trans)])

type 'a binders_let_argtype = (local_binder list, 'a) Genarg.abstract_argument_type

let (wit_binders_let : Genarg.tlevel binders_let_argtype),
  (globwit_binders_let : Genarg.glevel binders_let_argtype),
  (rawwit_binders_let : Genarg.rlevel binders_let_argtype) =
  Genarg.create_arg "binders_let"

open Pcoq.Constr

VERNAC COMMAND EXTEND AddRelation
  | [ "Add" "Relation" constr(a) constr(aeq) "reflexivity" "proved" "by" constr(lemma1) 
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

VERNAC COMMAND EXTEND AddParametricRelation
  | [ "Add" "Parametric" "Relation" binders_let(b) ":" constr(a) constr(aeq)
	"reflexivity" "proved" "by" constr(lemma1) 
	"symmetry" "proved" "by" constr(lemma2) "as" ident(n) ] ->
      [ declare_relation ~binders:b a aeq n (Some lemma1) (Some lemma2) None ]
  | [ "Add" "Parametric" "Relation" binders_let(b) ":" constr(a) constr(aeq)
	"reflexivity" "proved" "by" constr(lemma1)  
	"as" ident(n) ] ->
      [ declare_relation ~binders:b a aeq n (Some lemma1) None None ]
  | [ "Add" "Parametric" "Relation" binders_let(b) ":" constr(a) constr(aeq)  "as" ident(n) ] -> 
      [ declare_relation ~binders:b a aeq n None None None ]
END

VERNAC COMMAND EXTEND AddParametricRelation2
    [ "Add" "Parametric" "Relation" binders_let(b) ":" constr(a) constr(aeq) "symmetry" "proved" "by" constr(lemma2) 
      "as" ident(n) ] ->
      [ declare_relation ~binders:b a aeq n None (Some lemma2) None ]
  | [ "Add" "Parametric" "Relation" binders_let(b) ":" constr(a) constr(aeq) "symmetry" "proved" "by" constr(lemma2) "transitivity" "proved" "by" constr(lemma3)  "as" ident(n) ] ->
      [ declare_relation ~binders:b a aeq n None (Some lemma2) (Some lemma3) ]
END

VERNAC COMMAND EXTEND AddParametricRelation3
    [ "Add" "Parametric" "Relation" binders_let(b) ":" constr(a) constr(aeq) "reflexivity" "proved" "by" constr(lemma1) 
      "transitivity" "proved" "by" constr(lemma3) "as" ident(n) ] ->
      [ declare_relation ~binders:b a aeq n (Some lemma1) None (Some lemma3) ]
  | [ "Add" "Parametric" "Relation" binders_let(b) ":" constr(a) constr(aeq) "reflexivity" "proved" "by" constr(lemma1) 
      "symmetry" "proved" "by" constr(lemma2) "transitivity" "proved" "by" constr(lemma3) 
      "as" ident(n) ] ->
      [ declare_relation ~binders:b a aeq n (Some lemma1) (Some lemma2) (Some lemma3) ] 
  | [ "Add" "Parametric" "Relation" binders_let(b) ":" constr(a) constr(aeq) "transitivity" "proved" "by" constr(lemma3)
	"as" ident(n) ] ->  
      [ declare_relation ~binders:b a aeq n None None (Some lemma3) ] 
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
  let app = mkApp (Lazy.force respect_proj, 
		  Array.append args [| instarg |]) in
    it_mkLambda_or_LetIn app ctx
      
let declare_projection n instance_id r =
  let ty = Global.type_of_global r in
  let c = constr_of_global r in
  let term = respect_projection c ty in
  let typ = Typing.type_of (Global.env ()) Evd.empty term in
  let ctx, typ = Sign.decompose_prod_assum typ in
  let typ =
    let n = 
      let rec aux t = 
	match kind_of_term t with
	    App (f, [| a ; a' ; rel; rel' |]) when eq_constr f (Lazy.force respectful) -> 
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
  let typ = it_mkProd_or_LetIn typ ctx in
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
	| _ -> []
    in aux t
  in
  let t', sig_, evars = build_signature isevars env t cstrs None snd in
  let _ = List.iter
    (fun (ty, rel) -> 
      let default = mkApp (Lazy.force default_relation, [| ty; rel |]) in
	ignore (Evarutil.e_new_evar isevars env default))
    evars
  in
  let morph = 
    mkApp (Lazy.force morphism_type, [| t; sig_; m |])
  in
  let evd = resolve_all_evars_once false (true, 15) env
    (fun x evi -> class_of_constr evi.Evd.evar_concl <> None) !isevars in
    Evarutil.nf_isevar evd morph
	
let default_morphism sign m =
  let env = Global.env () in
  let isevars = ref (Evd.create_evar_defs Evd.empty) in
  let t = Typing.type_of env Evd.empty m in
  let _, sign, evars =
    build_signature isevars env t (fst sign) (snd sign) (fun (ty, rel) -> rel)
  in
  let morph =
    mkApp (Lazy.force morphism_type, [| t; sign; m |])
  in
  let mor = resolve_one_typeclass env morph in
    mor, respect_projection mor morph
    	  
let add_setoid binders a aeq t n =
  init_setoid ();
  let lemma_refl = declare_instance_refl binders a aeq n (mkappc "Seq_refl" [a;aeq;t]) in 
  let lemma_sym = declare_instance_sym binders a aeq n (mkappc "Seq_sym" [a;aeq;t]) in
  let lemma_trans = declare_instance_trans binders a aeq n (mkappc "Seq_trans" [a;aeq;t])  in
  let instance = declare_instance a aeq n "Coq.Classes.RelationClasses.Equivalence"
  in ignore(
    anew_instance binders instance
      [((dummy_loc,id_of_string "equivalence_reflexive"), [], mkIdentC lemma_refl);
       ((dummy_loc,id_of_string "equivalence_symmetric"),  [], mkIdentC lemma_sym);
       ((dummy_loc,id_of_string "equivalence_transitive"),[], mkIdentC lemma_trans)])

let add_morphism_infer m n =
  init_setoid ();
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
	Flags.if_verbose (fun x -> msg (Printer.pr_open_subgoals x)) () 

let add_morphism binders m s n =
  init_setoid ();
  let instance_id = add_suffix n "_Morphism" in
  let instance = 
    ((dummy_loc,Name instance_id), Explicit,
    CAppExpl (dummy_loc, 
	     (None, Qualid (dummy_loc, Libnames.qualid_of_string "Coq.Classes.Morphisms.Morphism")), 
	     [cHole; s; m]))
  in	  
  let tac = Tacinterp.interp <:tactic<add_morphism_tactic>> in
    ignore(new_instance binders instance []
	      ~on_free_vars:Classes.fail_on_free_vars
	      ~tac ~hook:(fun cst -> declare_projection n instance_id (ConstRef cst))
	      None)

VERNAC COMMAND EXTEND AddSetoid1
   [ "Add" "Setoid" constr(a) constr(aeq) constr(t) "as" ident(n) ] ->
     [ add_setoid [] a aeq t n ]
  | [ "Add" "Parametric" "Setoid" binders_let(binders) ":" constr(a) constr(aeq) constr(t) "as" ident(n) ] ->
     [	add_setoid binders a aeq t n ]
  | [ "Add" "Morphism" constr(m) ":" ident(n) ] ->
      [ add_morphism_infer m n ]
  | [ "Add" "Morphism" constr(m) "with" "signature" lconstr(s) "as" ident(n) ] ->
      [ add_morphism [] m s n ]
  | [ "Add" "Parametric" "Morphism" binders_let(binders) ":" constr(m) "with" "signature" lconstr(s) "as" ident(n) ] ->
      [ add_morphism binders m s n ]
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
      raise
	(Logic.RefinerError (Logic.UnresolvedBindings [Evd.meta_name evd m])))
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
      (* ~flags:(false,true) to allow to mark occurrences that must not be
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
  let cl' = {cl with evd = env'} in
  let c1 = Clenv.clenv_nf_meta cl' c1 
  and c2 = Clenv.clenv_nf_meta cl' c2 in
  check_evar_map_of_evars_defs env';
  let prf = Clenv.clenv_value cl' in
  let prfty = Clenv.clenv_type cl' in
  let cl' = { cl' with templval = mk_freelisted prf ; templtyp = mk_freelisted prfty } in
    {cl=cl'; prf=(mkRel 1); rel=rel; l2r=l2r; c1=c1; c2=c2; c=None; abs=Some (prf, prfty)}
(*         if occur_meta prf then *)
(* else *)
(*       {cl=cl'; prf=prf; rel=rel; l2r=l2r; c1=c1; c2=c2; c=None; abs=None} *)

let get_hyp gl c clause l2r = 
  match kind_of_term (pf_type_of gl c) with
      Prod _ -> 
	let hi = decompose_setoid_eqhyp (pf_env gl) (project gl) c l2r in
	let but = match clause with Some id -> pf_get_hyp_typ gl id | None -> pf_concl gl in
	  unification_rewrite hi.l2r hi.c1 hi.c2 hi.cl hi.rel but gl
    | _ -> decompose_setoid_eqhyp (pf_env gl) (project gl) c l2r
	
let general_rewrite_flags = { under_lambdas = false; on_morphisms = false }

let general_s_rewrite l2r occs c ~new_goals gl =
  let meta = Evarutil.new_meta() in
  let hypinfo = ref (get_hyp gl c None l2r) in
    cl_rewrite_clause_aux ~flags:general_rewrite_flags hypinfo meta occs None gl

let general_s_rewrite_in id l2r occs c ~new_goals gl =
  let meta = Evarutil.new_meta() in
  let hypinfo = ref (get_hyp gl c (Some id) l2r) in
    cl_rewrite_clause_aux ~flags:general_rewrite_flags hypinfo meta occs (Some (([],id), [])) gl

let classes_dirpath =
  make_dirpath (List.map id_of_string ["Classes";"Coq"])
  
let init_rewrite () =
  if is_dirpath_prefix_of classes_dirpath (Lib.cwd ()) then ()
  else check_required_library ["Coq";"Setoids";"Setoid"]

let general_s_rewrite_clause x =
  init_rewrite ();
  match x with
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

let is_loaded d =
  let d' = List.map id_of_string d in
  let dir = make_dirpath (List.rev d') in
    Library.library_is_loaded dir

let try_loaded f gl =
  if is_loaded ["Coq";"Classes";"RelationClasses"] then f gl 
  else tclFAIL 0 (str"You need to require Coq.Classes.RelationClasses first") gl
    
let setoid_reflexivity gl =
  let env = pf_env gl in
  let rel, args = relation_of_constr (pf_concl gl) in
    try
      apply (reflexive_proof env (pf_type_of gl args.(0)) rel) gl
    with Not_found -> 
      tclFAIL 0 (str" The relation " ++ Printer.pr_constr_env env rel ++ str" is not a declared reflexive relation")
	gl

(* let setoid_reflexivity gl = *)
(*   try_loaded setoid_reflexivity gl *)
	  
let setoid_symmetry gl =
  let env = pf_env gl in
  let rel, args = relation_of_constr (pf_concl gl) in
    try
      apply (symmetric_proof env (pf_type_of gl args.(0)) rel) gl
    with Not_found -> 
      tclFAIL 0 (str" The relation " ++ Printer.pr_constr_env env rel ++ str" is not a declared symmetric relation")
	gl

(* let setoid_symmetry gl = *)
(*   try_loaded setoid_symmetry gl *)
	
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
	
(* let setoid_transitivity c gl = *)
(*   try_loaded (setoid_transitivity c) gl *)

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

(* let setoid_symmetry_in h gl = *)
(*   try_loaded (setoid_symmetry_in h) gl *)

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
